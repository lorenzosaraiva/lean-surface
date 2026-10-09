"""Source command assembly; every retained command is copied verbatim."""

import pathlib, re, hashlib

LIBRARIES = set()
CACHE_RESET = """run_elab
  let names := (\u2190 Lean.getEnv).constants.toList.filterMap fun (n, _) =>
    if n.toString.endsWith ".Lean.Meta.Match.matcherExt" ||
       n.toString.endsWith ".Lean.Meta.sparseCasesOnCacheExt" ||
       n == `Lean.Meta.Match.matcherExt || n == `Lean.Meta.sparseCasesOnCacheExt
    then some n else none
  unless names.length == 2 do
    throwError "expected exactly two matcher cache extensions"
  for n in names do
    let ext := Lean.mkIdent n
    let cmd \u2190 `(command| run_elab
      Lean.modifyEnv fun env => Lean.EnvExtension.setState $ext env {})
    Lean.liftCommandElabM (Lean.Elab.Command.elabCommand cmd)

""".encode("utf-8")


def byte_pos(b, line, col):
    lines = b.splitlines(keepends=True)
    if line == len(lines) + 1 and col == 0:
        return len(b)
    return sum(map(len, lines[: line - 1])) + len(
        lines[line - 1].decode()[:col].encode()
    )


def generate(project, module, decl, data, out):
    global LIBRARIES
    LIBRARIES = set(
        data.get("trusted_roots", ["Init", "Std", "Lean", "Batteries", "Mathlib"])
    )
    parsed = {s["path"]: s for s in data["parsed_sources"]}
    sources = {p: pathlib.Path(p).read_bytes() for p in parsed}
    tables = {}
    for p, b in sources.items():
        lines = b.splitlines(keepends=True)
        prefix = [0]
        for line in lines:
            prefix.append(prefix[-1] + len(line))
        tables[p] = (lines, prefix)

    def position(p, line, col):
        lines, prefix = tables[p]
        if line == len(lines) + 1 and col == 0:
            return prefix[-1]
        return prefix[line - 1] + len(
            lines[line - 1].decode("utf-8")[:col].encode("utf-8")
        )

    # Parser byte offsets refer to Lean's text stream (CRLF is normalized by
    # Windows text I/O). Map checked line/Unicode-column positions back into
    # the untouched file bytes, including declaration-value spans.
    for p, s in parsed.items():
        for c in s["commands"]:
            for part in [c, *c["parts"]]:
                if "start_column" in part and "end_column" in part:
                    part["start_byte"] = position(
                        p, part["start_line"], part["start_column"]
                    )
                    part["end_byte"] = position(p, part["end_line"], part["end_column"])
    selected = {p: set() for p in parsed}
    owners = {}
    selected_names = {row["name"] for row in data["reading_list"]} | set(
        data["targets"]
    )
    boundary_names = set(data.get("boundary", []))

    def command(s):
        p, r = s["path"], s["range"]
        if p not in parsed or not r:
            raise ValueError(f"{s['source_owner']}: {s['status']}")
        lo = position(p, r["start_line"], r["start_column"])
        hi = position(p, r["end_line"], r["end_column"])
        found = [
            (i, c)
            for i, c in enumerate(parsed[p]["commands"])
            if c["start_byte"] <= lo and c["end_byte"] >= hi
        ]
        if not found:
            raise ValueError(
                f"{s['source_owner']}: range not contained in parsed command"
            )
        return p, *min(found, key=lambda x: x[1]["end_byte"] - x[1]["start_byte"])

    for row in data["reading_list"]:
        p, i, c = command(row["source"])
        b = sources[p][c["start_byte"] : c["end_byte"]]
        if re.search(
            rb"\bprivate\s+(def|theorem|lemma|abbrev|instance|structure|inductive)\b", b
        ) and not data.get("preserve_private_module"):
            raise ValueError(
                f"{row['name']}: private declarations from multiple modules cannot preserve module identity"
            )
        selected[p].add(i)
        owners.setdefault((p, i), set()).add(row["source"]["source_owner"])
    replacements = {}
    for name, source in data["targets"].items():
        tp, ti, tc = command(source)
        vals = [
            v
            for v in tc["parts"]
            if v["kind"].endswith(("declValSimple", "declValEqns", "whereStructInst"))
        ]
        if len(vals) != 1:
            raise ValueError(
                f"{name}: expected one declaration body span, found {len(vals)}"
            )
        replacements[tp, ti] = (
            sources[tp][tc["start_byte"] : vals[0]["start_byte"]] + b":= by\n  sorry"
        )
        selected[tp].add(ti)
        owners.setdefault((tp, ti), set()).add(name)
    modules = {
        pathlib.Path(p)
        .relative_to(project)
        .with_suffix("")
        .as_posix()
        .replace("/", "."): p
        for p in parsed
    }
    headers = {}

    def read_headers(mod):
        if mod in headers:
            return
        f = project / (mod.replace(".", "/") + ".lean")
        if not f.exists():
            return
        deps = re.findall(
            r"(?m)^\s*(?:public |meta )?import (?:all )?([\w.]+)",
            f.read_text(encoding="utf-8"),
        )
        headers[mod] = deps
        for dep in deps:
            if dep.split(".")[0] not in LIBRARIES | {"Lean"}:
                read_headers(dep)

    read_headers(module)
    ordered = []
    seen = set()

    def visit(mod):
        if mod in seen:
            return
        seen.add(mod)
        for dep in headers.get(mod, []):
            visit(dep)
        if mod in modules:
            ordered.append(modules[mod])

    visit(module)
    for mod in sorted(modules):
        visit(mod)
    imports = sorted(
        {m for deps in headers.values() for m in deps if m.split(".")[0] in LIBRARIES}
        | {"Lean"}
    )
    chunks = [("\n".join("import " + m for m in imports) + "\n\n").encode()]
    records = []
    namespaces = sorted(
        {
            c["namespace_after"]
            for s in parsed.values()
            for c in s["commands"]
            if c["kind"].endswith(".namespace") and c.get("namespace_after")
        }
    )
    needed_namespaces = set()
    for p in ordered:
        if parsed[p]["parse_errors"]:
            raise ValueError(f"{p}: {parsed[p]['parse_errors'][0]}")
        cmds = parsed[p]["commands"]
        keep = set(selected[p])
        last = max(selected[p], default=-1)
        required_scopes = {f for i in selected[p] for f in cmds[i]["scope_parents"]}
        for i, c in enumerate(cmds):
            k = c["kind"].rsplit(".", 1)[-1]
            b = sources[p][c["start_byte"] : c["end_byte"]]
            if "scope_parents" not in c:
                raise ValueError(
                    "Extraction lacks Lean scope transitions; rerun extraction"
                )
            context = (
                k in {"notation", "mixfix", "localNotation", "scoped"}
                and i < last
                and all(f in required_scopes for f in c["scope_parents"])
            )
            targets = set(c.get("attribute_targets", []))
            relevant_attribute = bool(targets & selected_names) or (
                bool(targets & boundary_names)
                and all(f in required_scopes for f in c["scope_parents"])
            )
            if k == "attribute" and i < last and relevant_attribute:
                missing = sorted(
                    targets
                    - selected_names
                    - set(c.get("attribute_external_targets", []))
                )
                if missing:
                    raise ValueError(
                        "Verbatim attribute command also names omitted declarations: "
                        + ", ".join(missing)
                    )
                context = True
            if k == "export":
                name = b.decode().split()[1]
                context = any(
                    o == name or o.startswith(name + ".")
                    for values in owners.values()
                    for o in values
                )
            if i in selected[p] or context:
                keep.update(c["scope_parents"])
                keep.add(i)
        for i, c in enumerate(cmds):
            if any(begin in keep for begin in c["closes_scopes"]):
                keep.add(i)
        last = max(selected[p], default=-1)
        for i, c in enumerate(cmds):
            k = c["kind"].rsplit(".", 1)[-1]
            if (
                k in {"open", "variable", "universe", "set_option"}
                and all(f in keep for f in c["scope_parents"])
                and i < last
            ):
                targets = set(c.get("open_explicit_targets", []))
                if k == "open" and targets and not c.get("open_namespace_targets"):
                    available = selected_names | set(c.get("open_external_targets", []))
                    if not targets & available:
                        continue
                    missing = targets - available
                    if missing:
                        raise ValueError(
                            "Verbatim selective open also names omitted declarations: "
                            + ", ".join(sorted(missing))
                        )
                keep.add(i)
        opened = {
            n.removeprefix("_root_.")
            for i in keep
            if cmds[i]["kind"].endswith(".open")
            for n in cmds[i].get("context_identifiers", [])
        }
        needed_namespaces.update(
            n
            for n in namespaces
            if any(n == token or n.endswith("." + token) for token in opened)
        )
        chunks.append(b"section\n\n")
        if len(ordered) > 1:
            chunks.append(CACHE_RESET)
        for i in sorted(keep):
            c = cmds[i]
            target = (p, i) in replacements
            b = (
                replacements[p, i]
                if target
                else sources[p][c["start_byte"] : c["end_byte"]]
            )
            lo = sum(map(len, chunks))
            chunks.append(b + b"\n\n")
            if i in selected[p]:
                records.append(
                    dict(
                        source=p,
                        start_byte=c["start_byte"],
                        end_byte=c["end_byte"],
                        source_start_line=c["start_line"],
                        source_end_line=c["end_line"],
                        challenge_start_byte=lo,
                        challenge_end_byte=lo + len(b),
                        owners=sorted(owners.get((p, i), {decl})),
                        target_statement=target,
                        sha256=hashlib.sha256(b).hexdigest(),
                        lines=len(b.splitlines()),
                    )
                )
        chunks.append(b"end\n\n")
    prefix = [
        f"namespace {ns}\nend {ns}\n".encode("utf-8")
        for ns in sorted(needed_namespaces)
    ]
    shift = sum(map(len, prefix))
    chunks[1:1] = prefix
    for record in records:
        record["challenge_start_byte"] += shift
        record["challenge_end_byte"] += shift
    chunks.append(
        ("\n".join("#check " + n for n in data["targets"]) + "\n").encode("utf-8")
    )
    content = b"".join(chunks)
    (out / "Challenge.lean").write_bytes(content)
    return dict(
        source_declarations=sum(not r["target_statement"] for r in records),
        source_lines=sum(r["lines"] for r in records if not r["target_statement"]),
        challenge_lines=len(content.splitlines()),
        raw_constant_count_v0=data["header"]["reading_list_definitions"],
        support_constants=data["header"]["source_support_constants"],
        imports=imports,
        records=records,
        sha256=hashlib.sha256(content).hexdigest(),
        matcher_context="reset the two nonpersistent caches at each reconstructed source-module boundary; strict Comparator unchanged"
        if len(ordered) > 1
        else "single source module; no cache reset required",
    )

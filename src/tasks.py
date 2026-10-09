"""Release validation and reproducible result generation."""

import hashlib, json, re

FIXTURES = {
    "CRLF": "def caf\u00e9 : Nat := 7\ntheorem sample : caf\u00e9 = 7 := rfl\n",
    "Nested": "namespace Outer.Inner\ndef quantity : Nat := 7\ntheorem sample : quantity = 7 := rfl\nend Outer.Inner\n",
    "Matchers": "def extract : Option Nat → Nat\n | some n => n\n | none => 0\ntheorem sample : extract (some 7) = 7 := rfl\n",
    "Structures": "structure Packet where\n value : Nat\ndef packet : Packet := ⟨7⟩\ntheorem sample : packet.value = 7 := rfl\n",
    "DefinitionHole": "structure Packet where\n value : Nat\ndef promised : Packet where\n value := 7\ntheorem sample : promised.value = 7 := rfl\n",
    "Classes": "class Amount (α : Type) where\n amount : α → Nat\ninstance : Amount Nat := ⟨id⟩\ndef amountOf (x : Nat) := Amount.amount x\ntheorem sample : amountOf 7 = 7 := rfl\n",
    "Abbrev": "abbrev quantity : Nat := 7\ntheorem sample : quantity = 7 := rfl\n",
    "Inductives": "inductive Code where\n | zero\n | next : Code → Code\nnoncomputable def depth (c : Code) : Nat := Code.rec 0 (fun _ n => n+1) c\ntheorem sample : depth (.next .zero) = 1 := rfl\n",
    "Mutual": "mutual\n def even : Nat → Bool\n | 0 => true\n | n+1 => odd n\n def odd : Nat → Bool\n | 0 => false\n | n+1 => even n\nend\ntheorem sample : even 2 = true := rfl\n",
    "Where": "def transform (n : Nat) : Nat := helper n\nwhere\n helper (x : Nat) := x+1\ntheorem sample : transform 6 = 7 := rfl\n",
    "Private": "private def quantity : Nat := 7\ntheorem sample : quantity = 7 := rfl\n",
    "Scoped": 'namespace Arithmetic\ndef quantity : Nat := 7\nscoped notation "QTY" => quantity\nend Arithmetic\nopen Arithmetic\nopen scoped Arithmetic\ntheorem sample : QTY = 7 := rfl\n',
    "Universes": "universe u\ndef identity {α : Type u} (x : α) : α := x\ntheorem sample {α : Type u} (x : α) : identity x = x := rfl\n",
    "Noncomputable": "noncomputable def pick : Nat := Classical.choice (show Nonempty Nat from ⟨7⟩)\ntheorem sample : pick = pick := rfl\n",
    "Opaque": "opaque quantity : Nat := 7\ntheorem sample : quantity = quantity := rfl\n",
    "Irreducible": "irreducible_def quantity : Nat := 7\ntheorem sample : quantity = quantity := rfl\n",
    "Partial": "partial def loopValue (n : Nat) : Nat := loopValue n\ntheorem sample : loopValue = loopValue := rfl\n",
    "Unsafe": "unsafe def quantity : Nat := 7\ntheorem sample : True := True.intro\n",
}


def setup_fixture_project(app, version, suffix=""):
    p = app.CACHE / "fixtures" / version
    if suffix:
        p /= suffix
    p.mkdir(parents=True, exist_ok=True)
    (p / "lean-toolchain").write_text("leanprover/lean4:v" + version + "\n")
    (p / "lakefile.toml").write_text('name = "fixtures"\nversion = "0.1.0"\n')
    (p / ".lake/build/lib/lean").mkdir(parents=True, exist_ok=True)
    return p


def prepare_fixture_support(app, p):
    support = p / ".lake/packages/fixture_support"
    lib = support / ".lake/build/lib/lean"
    for name in ["NameMap", "Eqns", "Expr", "TermReduce", "Irreducible"]:
        source = support / "Support" / (name + ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        content = (app.ROOT / "tests/Support" / (name + ".lean")).read_bytes()
        if name == "NameMap" and app.toolchain(p).endswith("v4.29.0-rc7"):
            # The newer upstream utility assumes an instance absent in this core.
            # Add fixture compatibility in the import header; upstream bodies stay verbatim.
            header = b"public import Lean"
            compatibility = "\n\n@[expose] public instance fixtureThunkInhabited {a : Type} [Inhabited a] : Inhabited (Thunk a) :=\n  ⟨Thunk.mk (fun _ => default)⟩"
            content = content.replace(header, header + compatibility.encode("utf-8"), 1)
        source.write_bytes(content)
        app.cached_compile(
            p,
            source,
            lib / "Support" / (name + ".olean"),
            [lib],
            module="Support." + name,
        )


def test(app, args):
    results = []
    for version in app.CONFIG["lean_versions"]:
        project = setup_fixture_project(app, version)
        for name, body in FIXTURES.items():
            row = {"lean_version": version, "fixture": name, "status": "FAIL"}
            try:
                if name == "Irreducible":
                    prepare_fixture_support(app, project)
                source = project / (name + ".lean")
                source.write_bytes(
                    (
                        "import Lean\n"
                        + (
                            "import Support.Irreducible\n"
                            if name == "Irreducible"
                            else ""
                        )
                        + "set_option autoImplicit false\n"
                        + body
                    )
                    .encode()
                    .replace(b"\n", b"\r\n")
                    if name == "CRLF"
                    else (
                        "import Lean\n"
                        + (
                            "import Support.Irreducible\n"
                            if name == "Irreducible"
                            else ""
                        )
                        + "set_option autoImplicit false\n"
                        + body
                    ).encode()
                )
                app.cached_compile(
                    project,
                    source,
                    project / ".lake/build/lib/lean" / (name + ".olean"),
                )
                target = "Outer.Inner.sample" if name == "Nested" else "sample"
                out = app.CACHE / "test-results" / version / name
                result = app.review(
                    project,
                    name,
                    [target],
                    out,
                    definitions=["quantity"]
                    if name == "Unsafe"
                    else ["promised"]
                    if name == "DefinitionHole"
                    else [],
                )
                row["comparator"] = result["status"]
                row["definition_holes"] = result["metrics"]["definition_holes"]
                if name in {"Partial", "Unsafe"}:
                    hints = json.loads((out / "hints.json").read_text(encoding="utf-8"))
                    row["safety_flags"] = hints["source_modifiers"] + hints["safety"]
                    if not any(
                        flag.get("modifier") == name.lower()
                        for flag in hints["source_modifiers"]
                    ):
                        raise ValueError("safety flag missing")
                if result["status"]["nanoda_kernel"] != "PASS":
                    row["comparison_diagnostic"] = (out / "comparator.log").read_text(
                        encoding="utf-8", errors="replace"
                    )
                    if (out / "nanoda.log").exists():
                        row["nanoda_diagnostic"] = (out / "nanoda.log").read_text(
                            encoding="utf-8", errors="replace"
                        )
                        if (
                            "DefinitionSafety::Unsafe | DefinitionSafety::Partial"
                            in row["nanoda_diagnostic"]
                        ):
                            raise ValueError(
                                "unsafe definition roots are unsupported by pinned Nanoda (src/parser.rs:784); safety flags emitted, Comparator and Lean replay passed"
                            )
                    raise ValueError("two-kernel comparison did not pass")
                deletions = []
                challenge = (out / "Challenge.lean").read_bytes()
                for i, record in enumerate(result["generation"]["records"]):
                    mutation = result["work"] / f"Delete{i}.lean"
                    mutation.write_bytes(
                        challenge[: record["challenge_start_byte"]]
                        + challenge[record["challenge_end_byte"] :]
                    )
                    try:
                        app.lean(
                            project,
                            ["-R", mutation.parent, mutation],
                            result["work"] / f"delete-{i}.log",
                            [result["lib"]],
                        )
                        broken = False
                    except RuntimeError:
                        diagnostic = (result["work"] / f"delete-{i}.log").read_text(
                            encoding="utf-8", errors="replace"
                        )
                        broken = bool(
                            re.search(r"\berror(?:\([^\n)]*\))?:", diagnostic)
                        )
                    deletions.append(
                        {"owners": record["owners"], "compile_fails": broken}
                    )
                row["deletions"] = deletions
                if not all(x["compile_fails"] for x in deletions):
                    raise ValueError("declaration deletion still compiles")
                row["status"] = "PASS"
            except (ValueError, RuntimeError, OSError) as e:
                row["error"] = str(e)
                if getattr(e, "log_path", None):
                    row["diagnostic"] = e.log_path.read_text(
                        encoding="utf-8", errors="replace"
                    )
                logs = list(
                    (app.CACHE / "fixtures" / version).rglob(name + ".compile.log")
                )
                if logs:
                    row["diagnostic"] = logs[-1].read_text(
                        encoding="utf-8", errors="replace"
                    )
            row["source_safety_modifiers"] = [
                m
                for m in ["partial", "unsafe"]
                if re.search(r"\b" + m + r"\s+def\b", body)
            ]
            results.append(row)
            print(version, name, row["status"], row.get("error", ""), flush=True)
    negatives = []
    project = setup_fixture_project(app, "4.32.0", "negative-controls")
    body = "def quantity : Nat := 7\ntheorem sample (n : Nat) (h : n = 7) : n = quantity := h\n"
    source = project / "Negative.lean"
    source.write_text(body, encoding="utf-8", newline="\n")
    app.cached_compile(project, source, project / ".lake/build/lib/lean/Negative.olean")
    original = app.review(
        project, "Negative", ["sample"], app.CACHE / "test-results/negative-baseline"
    )
    for name, body in [
        (
            "statement",
            "def quantity : Nat := 7\ntheorem sample (n : Nat) (h : n = 7) : n+1 = quantity+1 := congrArg (·+1) h\n",
        ),
        (
            "hypothesis",
            "def quantity : Nat := 7\ntheorem sample (n : Nat) (h : n = 7 ∨ n = 8) : n = quantity := by sorry\n",
        ),
        (
            "definition",
            "def quantity : Nat := 8\ntheorem sample (n : Nat) (h : n = 7) : n = quantity := by sorry\n",
        ),
    ]:
        source.write_text(body, encoding="utf-8", newline="\n")
        app.cached_compile(
            project, source, project / ".lake/build/lib/lean/Negative.olean"
        )
        try:
            app.compare(
                project,
                json.loads(
                    (
                        app.CACHE / "test-results/negative-baseline/config.json"
                    ).read_text(encoding="utf-8")
                ),
                original["lib"],
                original["work"],
            )
            rejected = False
        except (RuntimeError, ValueError):
            log = (
                (original["work"] / "comparator.log").read_text(
                    encoding="utf-8", errors="replace"
                )
                if (original["work"] / "comparator.log").exists()
                else ""
            )
            rejected = "Comparator rejected:" in log and (
                "do not match" in log or "does not match" in log
            )
        negatives.append({"mutation": name, "rejected_by_comparator": rejected})
        print("negative", name, "PASS" if rejected else "FAIL", flush=True)
    evidence = {
        "fixtures": results,
        "negative_controls": negatives,
        "method": "Fixtures explicitly disable automatic implicit parameters so deleting a referenced name cannot silently generalize the statement. Delete each copied source declaration command, including each requested root; #check anchors make root deletion observable. Inductives/structures/mutual blocks are source command units, not separately editable generated constants.",
    }
    app.dump(app.ROOT / "results/core-suite.json", app.scrub(evidence, project))
    return (
        0
        if all(x["status"] == "PASS" for x in results)
        and all(x["rejected_by_comparator"] for x in negatives)
        else 1
    )


def closure(constants, roots, holes=(), bodies=True):
    table = {r["name"]: r for r in constants}
    seen = set()
    todo = list(roots)
    while todo:
        n = todo.pop()
        if n in seen or n not in table:
            continue
        seen.add(n)
        r = table[n]
        todo += r["type_dependencies"] + r.get("related_constants", [])
        if bodies and n not in holes and not (r["kind"] == "theorem" and n in roots):
            todo += r["body_dependencies"]
    return seen


def compare_sets(theirs, ours, cfg):
    st = {r["name"] for r in theirs}
    so = {r["name"] for r in ours}
    checked_roots = cfg["theorem_names"] + cfg.get("definition_names", [])
    needed_t = closure(theirs, checked_roots, cfg.get("definition_names", []))
    needed_o = closure(ours, checked_roots, cfg.get("definition_names", []))
    holes_t = closure(theirs, cfg.get("definition_names", []))
    holes_o = closure(ours, cfg.get("definition_names", []))

    def normalized(n):
        return re.sub(r"^_private\.[\w.]+?\.\d+\.", "_private.", n)

    def classify(n, needed, holes, other):
        if n in needed:
            if any(normalized(n) == normalized(o) for o in other):
                return "naming or namespace difference"
            return "our bug"
        if n in holes:
            return "needed by definition_names"
        return "unused by any listed theorem"

    return {
        "theirs_minus_ours": [
            {"name": n, "classification": classify(n, needed_t, holes_t, so)}
            for n in sorted(st - so)
        ],
        "ours_minus_theirs": [
            {"name": n, "classification": classify(n, needed_o, holes_o, st)}
            for n in sorted(so - st)
        ],
        "theirs_raw_constants": len(st),
        "ours_raw_constants": len(so),
    }


def reproduce(app, args):
    project = args.project.resolve()
    commit = (
        app.command(["git", "rev-parse", "HEAD"], project, app.CACHE / "upstream.log")
        .decode()
        .strip()
    )
    if commit != app.CONFIG["upstream_commit"]:
        raise ValueError("upstream commit is not the pinned commit")
    results = app.ROOT / "results/ten-proofs"
    rows = []
    before = (
        {
            p.relative_to(results).as_posix(): p.read_bytes()
            for p in results.rglob("*")
            if p.is_file()
        }
        if args.verify and results.exists()
        else {}
    )
    for config in sorted((project / "ComparatorChallenges").glob("*.json")):
        cfg = json.loads(config.read_text(encoding="utf-8"))
        name = config.stem
        out = results / name
        out.mkdir(parents=True, exist_ok=True)
        row = {"challenge": name, "status": "FAIL", "upstream_commit": commit}
        try:
            result = app.review(
                project,
                cfg["solution_module"],
                cfg["theorem_names"],
                out,
                cfg.get("definition_names", []),
                bundle=True,
            )
            shipped = project / (cfg["challenge_module"].replace(".", "/") + ".lean")
            if not (
                project
                / ".lake/build/lib/lean"
                / (cfg["challenge_module"].replace(".", "/") + ".olean")
            ).exists():
                # Compile shipped challenge only; imports use existing project/dependency artifacts.
                app.cached_compile(
                    project,
                    shipped,
                    project
                    / ".lake/build/lib/lean"
                    / (cfg["challenge_module"].replace(".", "/") + ".olean"),
                    module=cfg["challenge_module"],
                )
            theirs = app.inventory(project, cfg["challenge_module"])
            diffs = compare_sets(theirs, result["metrics"]["constants"], cfg)
            app.dump(out / "comparison.json", diffs)
            syntax = app.extract(
                project,
                cfg["challenge_module"],
                "SOURCE:" + str(shipped),
                result["local_modules"],
            )
            if syntax["parse_errors"]:
                raise ValueError("shipped challenge source does not parse")
            count = sum(
                c["kind"].endswith(".declaration")
                or c["kind"] == "lemma"
                or c["kind"].endswith(".mutual")
                or any(p["kind"].endswith(".declId") for p in c["parts"])
                for c in syntax["commands"]
            )
            row.update(
                {
                    "theirs_lines": len(shipped.read_bytes().splitlines()),
                    "theirs_declarations": count,
                    "ours_lines": result["metrics"]["lines"],
                    "ours_declarations": result["metrics"]["declarations"],
                    "theirs_constants": len(theirs),
                    "ours_constants": result["metrics"]["raw_constants"],
                    "theirs_minus_ours": len(diffs["theirs_minus_ours"]),
                    "ours_minus_theirs": len(diffs["ours_minus_theirs"]),
                    "our_bugs": sum(
                        d["classification"] == "our bug"
                        for d in diffs["theirs_minus_ours"] + diffs["ours_minus_theirs"]
                    ),
                    "comparator": result["status"],
                }
            )
            row["status"] = (
                "PASS"
                if result["status"]["nanoda_kernel"] == "PASS" and row["our_bugs"] == 0
                else "FAIL"
            )
        except (ValueError, RuntimeError, OSError) as e:
            row["error"] = app.scrub(str(e), project)
        app.dump(
            out / "upstream.json",
            {"commit": commit, "configuration": config.relative_to(project).as_posix()},
        )
        rows.append(row)
        print(
            name, row["status"], row.get("error", row.get("comparator", "")), flush=True
        )
    app.dump(results / "summary.json", rows)
    text = f"# {app.NAME}: shipped challenge comparison\n\nPinned upstream: `{commit}`. Counts are explained in the measurement notes. Checks use the native trusted-cache profile.\n\n"
    text += "| Challenge | Theirs declarations / lines | Ours declarations / lines | Constants theirs / ours | Theirs-only / ours-only | Our bugs | Lean | Nanoda |\n|---|---:|---:|---:|---:|---:|---|---|\n"
    for r in rows:
        get = lambda k: r.get(k, "FAIL")
        text += f"| {r['challenge']} | {get('theirs_declarations')} / {get('theirs_lines')} | {get('ours_declarations')} / {get('ours_lines')} | {get('theirs_constants')} / {get('ours_constants')} | {get('theirs_minus_ours')} / {get('ours_minus_theirs')} | {get('our_bugs')} | {r.get('comparator', {}).get('lean_kernel', 'FAIL')} | {r.get('comparator', {}).get('nanoda_kernel', 'FAIL')} |\n"
    text += "\nSource declarations count Lean parser declaration/lemma commands and mutual command blocks; generated constant counts include constructors, projections and auxiliaries. Physical source lines include comments and blanks. The same source command unit policy is used for both sides. Definition hole bodies are excluded from comparison; their type dependencies remain checked. Each constant difference is recorded in comparison.json.\n"
    (results / "SUMMARY.md").write_text(text, encoding="utf-8", newline="\n")
    if args.verify:
        after = {
            p.relative_to(results).as_posix(): p.read_bytes()
            for p in results.rglob("*")
            if p.is_file()
        }
        differing = sorted(
            k for k in before.keys() | after.keys() if before.get(k) != after.get(k)
        )
        app.dump(
            app.ROOT / "results/reproduction.json",
            {"byte_identical": not differing, "differing_files": differing},
        )
        if differing:
            raise ValueError("reproduction changed " + ", ".join(differing))
    return 0 if all(r["status"] == "PASS" for r in rows) else 1


def docs(app, args):
    failures = []
    suite = app.ROOT / "results/core-suite.json"
    if suite.exists():
        failures = [
            f"- Lean {r['lean_version']}, {r['fixture']}: {r.get('error', 'required checks failed')}."
            for r in json.loads(suite.read_text(encoding="utf-8"))["fixtures"]
            if r["status"] != "PASS"
        ]
    unsupported = (
        "\n".join(failures)
        if failures
        else (
            "Every listed core fixture passed on both pinned toolchains; see results/core-suite.json. The following input restrictions still fail loudly."
            if suite.exists()
            else "Validation is in progress; see results/core-suite.json. No unsupported case is silently accepted."
        )
    )
    for template in [
        app.ROOT / "docs/README.md.in",
        app.ROOT / "CHANGELOG.md.in",
        app.ROOT / "CITATION.cff.in",
        app.ROOT / "docs/RELEASE_NOTES.md.in",
        app.ROOT / "docs/ZULIP_POST.md.in",
    ]:
        out = (
            app.ROOT / "README.md"
            if template.name == "README.md.in"
            else template.with_suffix("")
        )
        out.write_text(
            template.read_text(encoding="utf-8")
            .replace("{{name}}", app.NAME)
            .replace("{{cache_env}}", app.NAME.upper() + "_CACHE")
            .replace("{{unsupported}}", unsupported),
            encoding="utf-8",
            newline="\n",
        )
    return 0


def privacy(app, args):
    patterns = json.loads(args.pattern_file.read_text(encoding="utf-8"))
    hits = []
    for path in app.ROOT.rglob("*"):
        if not path.is_file() or ".git" in path.parts:
            continue
        if path.name == "privacy.json":
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for label, pattern in patterns.items():
            for match in re.finditer(pattern, text):
                hits.append(
                    {
                        "file": path.relative_to(app.ROOT).as_posix(),
                        "pattern": label,
                        "line": text.count("\n", 0, match.start()) + 1,
                    }
                )
    app.dump(
        app.ROOT / "results/privacy.json",
        {
            "pattern_ids": list(patterns),
            "pattern_file_sha256": hashlib.sha256(
                args.pattern_file.read_bytes()
            ).hexdigest(),
            "hits": hits,
            "scope": "all release working-tree files except .git and this self-report; no content exemptions",
        },
    )
    return 1 if hits else 0

"""Single entry point. Uses the target toolchain and cached artifacts serially."""

from __future__ import annotations
import argparse, hashlib, importlib.util, json, os, pathlib, re, shutil, subprocess, sys, tempfile

sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parent
CONFIG = json.loads((ROOT / "tool.json").read_text(encoding="utf-8"))
NAME = CONFIG["name"]
ENV = dict(os.environ, LEAN_NUM_THREADS="2", PYTHONDONTWRITEBYTECODE="1")
ENV["PATH"] = str(pathlib.Path.home() / ".elan/bin") + os.pathsep + ENV.get("PATH", "")
CRASHES = {139, 132, 134, 135, 3221225477, 3221225725, 3221226505, -1073741819, -1073741571, -1073740791}


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def command(args, cwd, log, env=None, stdin=None, stdout_file=None):
    """No parallel subprocesses; bounded crash-only resume, retaining successful files."""
    args = list(map(str, args))
    log.parent.mkdir(parents=True, exist_ok=True)
    attempts = []
    for attempt in range(1, 4):
        if stdout_file is None:
            result = subprocess.run(
                args,
                cwd=cwd,
                env=env or ENV,
                input=stdin,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            log.write_bytes(result.stdout + result.stderr)
        else:
            with stdout_file.open("wb") as stream:
                result = subprocess.run(
                    args,
                    cwd=cwd,
                    env=env or ENV,
                    input=stdin,
                    stdout=stream,
                    stderr=subprocess.PIPE,
                )
            log.write_bytes(result.stderr)
        attempts.append({"attempt": attempt, "exit_code": result.returncode})
        if result.returncode not in CRASHES:
            break
        shutil.copy2(log, log.with_name(log.name + f".crash-{attempt}"))
    if len(attempts) > 1:
        dump(log.with_suffix(".attempts.json"), attempts)
    if result.returncode:
        relative_log = (
            log.relative_to(CACHE)
            if log.is_relative_to(CACHE)
            else pathlib.Path(log.name)
        )
        error = RuntimeError(
            f"{relative_log.as_posix()}: exit {result.returncode}; see private cache log"
        )
        error.log_path = log
        raise error
    return result.stdout


def toolchain(project):
    raw = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    if raw.removeprefix("leanprover/lean4:v") not in CONFIG["lean_versions"]:
        raise ValueError("unsupported Lean toolchain: " + raw)
    return raw


def lean_env(project, extra=()):
    toolchain(project)
    prefix = (
        command(
            ["lake", "env", "lean", "--print-prefix"], project, CACHE / "prefix.log"
        )
        .decode()
        .strip()
    )
    paths = [project / ".lake/build/lib/lean"]
    if (project / ".lake/packages").exists():
        paths += [
            p / ".lake/build/lib/lean"
            for p in (project / ".lake/packages").iterdir()
            if p.is_dir()
        ]
    env = dict(
        ENV,
        LEAN_PATH=os.pathsep.join(map(str, [*extra, *paths])),
        LEAN_SRC_PATH=os.pathsep.join(
            map(
                str,
                [
                    project,
                    *[p for p in (project / ".lake/packages").iterdir() if p.is_dir()],
                ],
            )
        )
        if (project / ".lake/packages").exists()
        else str(project),
    )
    return pathlib.Path(prefix) / "bin" / (
        "lean.exe" if os.name == "nt" else "lean"
    ), env


def lean(project, args, log, extra=(), stdout_file=None):
    binary, env = lean_env(project, extra)
    return command([binary, *args], project, log, env, stdout_file=stdout_file)


def cached_compile(project, source, out, extra=(), module=None):
    out.parent.mkdir(parents=True, exist_ok=True)
    key = hashlib.sha256(
        source.read_bytes() + toolchain(project).encode() + str(extra).encode()
    ).hexdigest()
    stamp = out.with_suffix(".source-hash")
    if out.exists() and stamp.exists() and stamp.read_text(encoding="utf-8") == key:
        ilean = out.with_suffix(".ilean")
        if ilean.exists() and json.loads(ilean.read_text(encoding="utf-8"))[
            "module"
        ] == (module or source.stem):
            return
    root = source.parents[len((module or source.stem).split(".")) - 1]
    args = ["-R", root, "-o", out, "-i", out.with_suffix(".ilean")]
    args += [source]
    lean(project, args, out.with_suffix(".compile.log"), extra)
    stamp.write_text(key)


def clone(url, rev, destination):
    if not (destination / ".git").exists():
        command(
            ["git", "clone", "--quiet", url, destination], ROOT, CACHE / "clone.log"
        )
        command(
            ["git", "checkout", "--quiet", rev], destination, CACHE / "checkout.log"
        )
    actual = (
        command(["git", "rev-parse", "HEAD"], destination, CACHE / "revision.log")
        .decode()
        .strip()
    )
    if actual != rev:
        raise ValueError("dependency cache revision differs: " + destination.name)


def prepare(project):
    version = toolchain(project).split(":v")[-1]
    directory = CACHE / "tools" / version
    directory.mkdir(parents=True, exist_ok=True)
    packages = {
        "Comparator": (
            "https://github.com/leanprover/comparator",
            CONFIG["comparator_revision"],
        ),
        "Lean4Checker": (
            "https://github.com/leanprover/lean4checker",
            CONFIG["checker_revision"],
        ),
        "lean4export": (
            "https://github.com/leanprover/lean4export",
            CONFIG["exporter_revision"],
        ),
    }
    for name, (url, rev) in packages.items():
        p = directory / name
        if not p.exists():
            cached = project / ".lake/packages" / name
            if (cached / ".git").exists():
                got = (
                    command(
                        ["git", "rev-parse", "HEAD"], cached, CACHE / "revision.log"
                    )
                    .decode()
                    .strip()
                )
                if got == rev:
                    shutil.copytree(cached, p, ignore=shutil.ignore_patterns(".lake"))
        clone(url, rev, p)
    builds = {name: directory / name / ".lake/build/lib/lean" for name in packages}
    extra = list(builds.values())
    sources = {}
    for name in packages:
        for file in (directory / name).rglob("*.lean"):
            if (
                ".lake" in file.parts
                or file.name == "Main.lean"
                or "Tests" in file.as_posix()
                or "/tests/" in file.as_posix()
            ):
                continue
            mod = (
                file.relative_to(directory / name)
                .with_suffix("")
                .as_posix()
                .replace("/", ".")
            )
            sources[mod] = (file, builds[name] / (mod.replace(".", "/") + ".olean"))
    done = set()

    def build(mod):
        if mod in done or mod not in sources:
            return
        done.add(mod)
        src, out = sources[mod]
        for dep in re.findall(r"(?m)^import ([\w.]+)", src.read_text(encoding="utf-8")):
            build(dep)
        cached_compile(project, src, out, extra, module=mod)

    for mod in ["Comparator", "Lean4Checker.Replay", "Export"]:
        build(mod)
    return directory, extra


def extract(project, module, decl, local_modules, holes=()):
    digest = hashlib.sha256(
        (
            toolchain(project)
            + "\n"
            + json.dumps(local_modules)
            + json.dumps(list(holes))
        ).encode()
    ).hexdigest()
    script = CACHE / "extractors" / digest / "Extract.lean"
    script.parent.mkdir(parents=True, exist_ok=True)
    text = (
        (ROOT / "src/Extract.lean.in")
        .read_text(encoding="utf-8")
        .replace("__LOCAL_MODULES__", json.dumps(local_modules))
        .replace("__DEFINITION_HOLES__", json.dumps(list(holes)))
    )
    support_text, main_text = text.split("unsafe def main", 1)
    support = script.parent / "ExtractSupport.lean"
    if not support.exists() or support.read_text(encoding="utf-8") != support_text:
        support.write_text(support_text, encoding="utf-8")
    library = script.parent / "lib"
    library.mkdir(exist_ok=True)
    cached_compile(project, support, library / "ExtractSupport.olean", [library])
    main_text = "import ExtractSupport\nopen Lean\nunsafe def main" + main_text
    if not script.exists() or script.read_text(encoding="utf-8") != main_text:
        script.write_text(main_text, encoding="utf-8")
    path = (
        CACHE
        / "extractions"
        / hashlib.sha256((str(project) + module + decl + text).encode()).hexdigest()
        / "extracted.json"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    # Only reuse when the imported environment and all project source bytes match.
    fingerprint = hashlib.sha256()
    for mod in local_modules:
        file = project / (mod.replace(".", "/") + ".lean")
        if file.exists():
            fingerprint.update(file.read_bytes())
    olean = project / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
    if not olean.exists():
        raise ValueError("target module has no cached olean; build it first")
    fingerprint.update(olean.read_bytes())
    key = fingerprint.hexdigest()
    stamp = path.with_suffix(".source-hash")
    if (
        not path.exists()
        or not stamp.exists()
        or stamp.read_text(encoding="utf-8") != key
    ):
        lean(
            project,
            ["--run", script, module, decl, path],
            path.with_suffix(".log"),
            [library],
        )
        stamp.write_text(key)
    return json.loads(path.read_text(encoding="utf-8"))


def inventory_signature(project, module, extra=()):
    h = hashlib.sha256((toolchain(project) + module).encode())
    h.update((ROOT / "src/Inventory.lean").read_bytes())
    directories = [*extra, project / ".lake/build/lib/lean"]
    packages = project / ".lake/packages"
    if packages.exists():
        directories += [
            p / ".lake/build/lib/lean" for p in packages.iterdir() if p.is_dir()
        ]
    for directory in directories:
        base = directory / (module.replace(".", "/") + ".olean")
        if base.exists():
            for suffix in ["", ".private", ".server"]:
                file = pathlib.Path(str(base) + suffix)
                if file.exists():
                    h.update(file.read_bytes())
            return h.hexdigest()
    raise ValueError("compiled inventory module is unavailable: " + module)


def inventory(project, module, extra=()):
    path = (
        CACHE
        / "inventories"
        / hashlib.sha256((str(project) + module + str(extra)).encode()).hexdigest()
        / "constants.json"
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    signature = inventory_signature(project, module, extra)
    stamp = path.with_suffix(".source-hash")
    if (
        not path.exists()
        or not stamp.exists()
        or stamp.read_text(encoding="utf-8") != signature
    ):
        lean(
            project,
            ["--run", ROOT / "src/Inventory.lean", module, path],
            path.with_suffix(".log"),
            extra,
        )
        stamp.write_text(signature)
    return json.loads(path.read_text(encoding="utf-8"))


def scrub(value, project):
    if isinstance(value, str):
        for p in [
            str(project),
            project.as_posix(),
            str(CACHE),
            CACHE.as_posix(),
            str(ROOT),
            ROOT.as_posix(),
        ]:
            value = re.sub(
                re.escape(p), ".", value, flags=re.IGNORECASE if os.name == "nt" else 0
            )
        return value
    if isinstance(value, list):
        return [scrub(x, project) for x in value]
    if isinstance(value, dict):
        return {k: scrub(v, project) for k, v in value.items()}
    return value


def export_signature(project, cfg, challenge_lib):
    h = hashlib.sha256(json.dumps(cfg, sort_keys=True).encode())
    for directory, mod in [
        (challenge_lib, "Challenge"),
        (project / ".lake/build/lib/lean", cfg["solution_module"]),
    ]:
        base = directory / (mod.replace(".", "/") + ".olean")
        for suffix in ["", ".private", ".server"]:
            file = pathlib.Path(str(base) + suffix)
            if file.exists():
                with file.open("rb") as stream:
                    for chunk in iter(lambda: stream.read(1048576), b""):
                        h.update(chunk)
    # Import artifact writes invalidate exports even when the root module is unchanged.
    # The cache is trusted; artifact metadata is not an adversarial integrity check.
    directories = [project / ".lake/build/lib/lean"]
    packages = project / ".lake/packages"
    if packages.exists():
        directories += [
            p / ".lake/build/lib/lean" for p in packages.iterdir() if p.is_dir()
        ]
    for directory in sorted(directories):
        if not directory.exists():
            continue
        for file in sorted(directory.rglob("*.olean*")):
            info = file.stat()
            h.update(str(file.relative_to(project)).encode())
            h.update(f"{info.st_size}:{info.st_mtime_ns}".encode())
    h.update(toolchain(project).encode())
    h.update(CONFIG["exporter_revision"].encode())
    return h.hexdigest()


def comparison_signature(project, cfg, work):
    """Bind a successful receipt to the exact exports, driver, pins and Nanoda binary."""
    nanoda = os.environ.get("COMPARATOR_NANODA")
    if not nanoda:
        raise ValueError("COMPARATOR_NANODA is required; see README setup")
    h = hashlib.sha256(json.dumps(cfg, sort_keys=True).encode())
    h.update(toolchain(project).encode())
    h.update((ROOT / "src/Check.lean").read_bytes())
    for key in [
        "comparator_revision",
        "checker_revision",
        "exporter_revision",
        "nanoda_revision",
    ]:
        h.update(CONFIG[key].encode())
    for path in [
        work / "challenge.export",
        work / "solution.export",
        pathlib.Path(nanoda),
    ]:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1048576), b""):
                h.update(chunk)
    return h.hexdigest()


def compare(project, cfg, challenge_lib, work):
    directory, extra = prepare(project)
    roots = list(
        dict.fromkeys(
            cfg["theorem_names"]
            + cfg["definition_names"]
            + cfg["permitted_axioms"]
            + [
                "Nat",
                "String",
                "String.mk",
                "Char",
                "Char.ofNat",
                "List",
                "Quot",
                "Quot.mk",
                "Quot.lift",
                "Quot.ind",
                "Nat.add",
                "Nat.sub",
                "Nat.mul",
                "Nat.pow",
                "Nat.gcd",
                "Nat.div",
                "Nat.mod",
                "Nat.beq",
                "Nat.ble",
                "Nat.land",
                "Nat.lor",
                "Nat.xor",
                "Nat.shiftLeft",
                "Nat.shiftRight",
                "String.ofList",
            ]
        )
    )
    cp = work / "challenge.export"
    sp = work / "solution.export"
    requested = set(cfg["theorem_names"] + cfg.get("definition_names", []))
    export_options = (
        ["--export-unsafe"]
        if any(
            c["name"] in requested and "unsafe" in c["safety"]
            for c in inventory(project, "Challenge", [challenge_lib])
        )
        else []
    )
    signature = export_signature(project, cfg, challenge_lib)
    if export_options:
        signature = hashlib.sha256(
            (signature + json.dumps(export_options)).encode()
        ).hexdigest()
    stamp = work / "export.source-hash"
    if (
        not cp.exists()
        or not sp.exists()
        or not stamp.exists()
        or stamp.read_text(encoding="utf-8") != signature
    ):
        lean(
            project,
            [
                "--run",
                directory / "lean4export/Main.lean",
                *export_options,
                "Challenge",
                "--",
                *roots,
            ],
            work / "export-challenge.log",
            [challenge_lib, *extra],
            stdout_file=cp,
        )
        lean(
            project,
            [
                "--run",
                directory / "lean4export/Main.lean",
                *export_options,
                cfg["solution_module"],
                "--",
                *roots,
            ],
            work / "export-solution.log",
            extra,
            stdout_file=sp,
        )
        stamp.write_text(signature)
    check_signature = comparison_signature(project, cfg, work)
    receipt = work / "comparison-receipt.json"
    if receipt.exists():
        cached = json.loads(receipt.read_text(encoding="utf-8"))
        if (
            cached.get("signature") == check_signature
            and cached.get("status", {}).get("nanoda_kernel") == "PASS"
        ):
            return cached["status"]
    cfgfile = work / "config.json"
    dump(cfgfile, cfg)
    try:
        lean(
            project,
            ["--run", ROOT / "src/Check.lean", cfgfile, cp, sp],
            work / "comparator.log",
            extra,
        )
    except RuntimeError as e:
        diagnostic = (work / "comparator.log").read_text(
            encoding="utf-8", errors="replace"
        )
        compared = "Comparator comparison and axiom checks: PASS" in diagnostic
        e.check_status = {
            "comparison": "PASS" if compared else "FAIL",
            "lean_kernel": "FAIL" if compared else "NOT RUN",
            "nanoda_kernel": "NOT RUN",
            "error": str(e),
        }
        raise
    nanoda = os.environ.get("COMPARATOR_NANODA")
    if not nanoda:
        raise ValueError("COMPARATOR_NANODA is required; see README setup")
    ncfg = work / "nanoda.json"
    dump(
        ncfg,
        {
            "use_stdin": True,
            "permitted_axioms": cfg["permitted_axioms"],
            "unpermitted_axiom_hard_error": True,
            "nat_extension": True,
            "string_extension": True,
        },
    )
    try:
        command([nanoda, ncfg], work, work / "nanoda.log", stdin=sp.read_bytes())
    except RuntimeError as e:
        e.check_status = {
            "comparison": "PASS",
            "lean_kernel": "PASS",
            "nanoda_kernel": "FAIL",
            "error": str(e),
        }
        raise
    status = {
        "comparison": "PASS",
        "lean_kernel": "PASS",
        "nanoda_kernel": "PASS",
        "profile": "trusted-cache; no sandbox",
    }
    dump(receipt, {"signature": check_signature, "status": status})
    return status


def review(
    project, module, names, out, definitions=(), trusted=(), bundle=False, check=True
):
    project = project.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if len(names) > 1 and not bundle:
        raise ValueError("multiple declarations require --bundle")
    try:
        files = (
            command(
                [
                    "git",
                    "ls-files",
                    "--cached",
                    "--others",
                    "--exclude-standard",
                    "--",
                    "*.lean",
                ],
                project,
                CACHE / "project-files.log",
            )
            .decode()
            .splitlines()
        )
    except RuntimeError:
        files = []
    if not files:
        files = [
            str(p.relative_to(project)).replace("\\", "/")
            for p in project.rglob("*.lean")
            if ".lake" not in p.parts
        ]
    files = sorted(
        {
            p
            for p in files
            if ".lake" not in pathlib.PurePosixPath(p).parts
            and ".git" not in pathlib.PurePosixPath(p).parts
        }
    )
    local = sorted(
        {
            p[:-5].replace("/", ".")
            for p in files
            if p not in ["lakefile.lean"]
            and not p.startswith(("ComparatorChallenges/", "review/"))
            and p.split("/")[0] not in trusted
        }
    )
    if module not in local:
        raise ValueError("requested module is outside target package roots")
    targets = list(dict.fromkeys([*names, *definitions]))
    facts = [extract(project, module, n, local, definitions) for n in targets]
    rows = {
        r["name"]: r
        for f in facts
        for r in f["reading_list"]
        if r["name"] not in targets
    }
    parsed = {p["path"]: p for f in facts for p in f["parsed_sources"]}
    roots = {"Init", "Std", "Lean", *trusted}
    # Every module with no target-package source stays an import.
    for f in files:
        if f == "lakefile.lean":
            continue
        for dep in re.findall(
            r"(?m)^\s*(?:public |meta )?import (?:all )?([\w.]+)",
            (project / f).read_text(encoding="utf-8"),
        ):
            if dep not in local:
                roots.add(dep.split(".")[0])
    private = any(
        r["name"].startswith("_private.")
        or "._@." in r["name"]
        or re.search(r"\bprivate\s+", r["source"]["text"])
        for r in rows.values()
    )
    preserve_private = private and len(parsed) == 1
    if private and not preserve_private:
        raise ValueError(
            "private or hygienic declarations spanning multiple source modules are unsupported"
        )
    data = {
        "reading_list": list(rows.values()),
        "parsed_sources": list(parsed.values()),
        "targets": {n: f["target_source"] for n, f in zip(targets, facts)},
        "trusted_roots": sorted(roots),
        "boundary": sorted({x for f in facts for x in f["boundary"]}),
        "preserve_private_module": preserve_private,
        "header": {
            "reading_list_definitions": len(rows),
            "source_support_constants": sum(
                f["header"]["source_support_constants"] for f in facts
            ),
        },
    }
    spec = importlib.util.spec_from_file_location("assembly", ROOT / "src/assemble.py")
    assembly = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(assembly)
    generation = assembly.generate(project, module, names[0], data, out)
    work = (
        CACHE
        / "reviews"
        / hashlib.sha256(
            (str(project) + json.dumps(targets) + generation["sha256"]).encode()
        ).hexdigest()
    )
    work.mkdir(parents=True, exist_ok=True)
    compilation_module = module if preserve_private else "Challenge"
    challenge = work / (compilation_module.replace(".", "/") + ".lean")
    challenge.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(out / "Challenge.lean", challenge)
    lib = work / "lib"
    lib.mkdir(exist_ok=True)
    cached_compile(
        project, challenge, lib / "Challenge.olean", [lib], module=compilation_module
    )
    constants = inventory(project, "Challenge", [lib])
    cfg = {
        "challenge_module": "Challenge",
        "solution_module": module,
        "theorem_names": list(names),
        "definition_names": list(definitions),
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    dump(out / "config.json", cfg)
    hints = {
        "advisory": True,
        "hypotheses": {n: f["hypotheses"] for n, f in zip(targets, facts)},
        "totalization": [x for f in facts for x in f["totalization_flags"]],
        "stub_hints": [x for f in facts for x in f["stub_hints"]],
        "safety": [
            {"name": c["name"], "safety": c["safety"]}
            for c in constants
            if "unsafe" in c["safety"] or "partial" in c["safety"]
        ],
        "source_modifiers": [
            {"declaration": r["owners"], "modifier": m}
            for r in generation["records"]
            for m in ["partial", "unsafe"]
            if re.search(
                rb"\b" + m.encode() + rb"\b",
                challenge.read_bytes()[
                    r["challenge_start_byte"] : r["challenge_end_byte"]
                ],
            )
        ],
    }
    dump(out / "hints.json", scrub(hints, project))
    dump(out / "provenance.json", scrub(generation, project))
    metrics = {
        "lines": len(challenge.read_bytes().splitlines()),
        "declarations": len(generation["records"]),
        "raw_constants": len(constants),
        "constants": constants,
        "definition_holes": list(definitions),
        "source_sha256": generation["sha256"],
        "lean_version": toolchain(project).split(":v")[-1],
        "compilation_module_identity": compilation_module,
    }
    dump(out / "metrics.json", metrics)
    status = {
        "comparison": "NOT RUN",
        "lean_kernel": "NOT RUN",
        "nanoda_kernel": "NOT RUN",
    }
    if check:
        try:
            status = compare(project, cfg, lib, work)
        except (ValueError, RuntimeError) as e:
            status = getattr(
                e,
                "check_status",
                {
                    "comparison": "FAIL",
                    "lean_kernel": "NOT CONFIRMED",
                    "nanoda_kernel": "NOT CONFIRMED",
                    "error": str(e),
                },
            )
        for filename in ["comparator.log", "nanoda.log", "Challenge.compile.log"]:
            if (work / filename).exists():
                (out / filename).write_text(
                    scrub(
                        (work / filename).read_text(encoding="utf-8", errors="replace"),
                        project,
                    ),
                    encoding="utf-8",
                )
    dump(out / "status.json", status)
    return {
        "metrics": metrics,
        "status": status,
        "generation": generation,
        "work": work,
        "lib": lib,
        "local_modules": local,
    }


def main():
    global CACHE
    parser = argparse.ArgumentParser(prog=NAME)
    parser.add_argument(
        "--cache",
        type=pathlib.Path,
        default=pathlib.Path(
            os.environ.get(
                NAME.upper() + "_CACHE",
                str(pathlib.Path(tempfile.gettempdir()) / (NAME + "-cache")),
            )
        ),
    )
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("review")
    p.add_argument("--project", type=pathlib.Path, default=pathlib.Path.cwd())
    p.add_argument("--module", required=True)
    p.add_argument("declarations", nargs="+")
    p.add_argument("--bundle", action="store_true")
    p.add_argument("--definition", action="append", default=[])
    p.add_argument("--trusted-root", action="append", default=[])
    p.add_argument("--output", type=pathlib.Path, required=True)
    p = sub.add_parser("reproduce")
    p.add_argument("--project", type=pathlib.Path, required=True)
    p.add_argument("--verify", action="store_true")
    sub.add_parser("test")
    sub.add_parser("docs")
    p = sub.add_parser("privacy")
    p.add_argument("--pattern-file", type=pathlib.Path, required=True)
    args = parser.parse_args()
    CACHE = args.cache.resolve()
    CACHE.mkdir(parents=True, exist_ok=True)
    if args.command == "review":
        result = review(
            args.project,
            args.module,
            args.declarations,
            args.output,
            args.definition,
            args.trusted_root,
            args.bundle,
        )
        print(json.dumps(result["status"]))
        return 0 if result["status"].get("nanoda_kernel") == "PASS" else 1
    spec = importlib.util.spec_from_file_location("tasks", ROOT / "src/tasks.py")
    tasks = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tasks)
    return getattr(tasks, args.command)(sys.modules[__name__], args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, OSError) as e:
        print(f"{NAME}: FAIL: {e}", file=sys.stderr)
        sys.exit(1)

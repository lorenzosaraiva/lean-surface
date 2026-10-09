"""Structural comparison of independently typed bodies after proof erasure."""

import hashlib
import json


CHILDREN = ("type", "value", "fn", "arg", "body", "of")


def first_difference(solution, handmade, path="$body"):
    if solution == handmade:
        return None
    # A node's non-expression attributes distinguish that entire subterm.
    child_keys = {k for k in CHILDREN if isinstance(solution.get(k), dict)
                  and isinstance(handmade.get(k), dict)}
    left = {k: v for k, v in solution.items() if k not in child_keys}
    right = {k: v for k, v in handmade.items() if k not in child_keys}
    if left != right:
        return {"path": path, "solution_subterm": solution, "handmade_subterm": handmade}
    for key in CHILDREN:
        if key in child_keys:
            if key not in solution or key not in handmade:
                return {"path": path, "solution_subterm": solution, "handmade_subterm": handmade}
            difference = first_difference(solution[key], handmade[key], path + "." + key)
            if difference:
                return difference
    raise ValueError("unhandled canonical expression difference")


def compare(app, project, module, handmade_module, names, output):
    project = project.resolve()
    sides = []
    for mod in (module, handmade_module):
        signature = hashlib.sha256(
            (app.ROOT / "src/Bodies.lean").read_bytes()
            + app.inventory_signature(project, mod).encode()
            + json.dumps(names).encode()
        ).hexdigest()
        path = app.CACHE / "bodies" / signature / "erased.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists():
            app.lean(project, ["--run", app.ROOT / "src/Bodies.lean", mod, path, *names],
                     path.with_suffix(".log"))
        sides.append({row["name"]: row["erased"] for row in json.loads(path.read_text(encoding="utf-8"))})
    rows = []
    for name in names:
        solution, handmade = sides[0][name], sides[1][name]
        difference = first_difference(solution, handmade)
        rows.append({"name": name, "verdict": "DIFFERENT" if difference else "EQUAL",
                     "first_difference": difference, "solution_erased": solution,
                     "handmade_erased": handmade})
    report = {"solution_module": module, "handmade_module": handmade_module,
              "lean_version": app.toolchain(project).split(":v")[-1],
              "method": "Meta.isProof replaces each proof-valued subterm by one placeholder in its original typing context. Structural comparison ignores binder names and metadata; bound variables and universe parameters use indices. No unfolding, reduction or semantic-equivalence claim.",
              "definitions": rows}
    app.dump(output, report)
    return report

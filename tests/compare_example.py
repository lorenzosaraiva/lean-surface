"""Compare all files emitted by review against a committed example bundle."""
import json
import pathlib
import sys

actual, expected = map(pathlib.Path, sys.argv[1:])
differences = []
for path in sorted(actual.iterdir()):
    if not path.is_file():
        continue
    reference = expected / path.name
    if not reference.exists() or path.read_bytes() != reference.read_bytes():
        differences.append(path.name)
required = {"Challenge.lean", "config.json", "metrics.json", "hints.json", "provenance.json", "status.json"}
differences += sorted(required - {p.name for p in actual.iterdir()})
print(json.dumps({"differing_files": differences}, indent=2))
sys.exit(bool(differences))

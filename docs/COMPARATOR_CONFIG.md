# Exact Comparator configuration semantics

Pinned Comparator revision: `07bc4ea40f2266dcb861820a2ec1fa3244ed307f`.
References below are upstream paths and lines at that revision, not this driver's
interpretation of field names. No additional JSON fields are consumed by its
`Config` structure.

| Field | Exact effect | Upstream source |
|---|---|---|
| `challenge_module` | Required string converted with `String.toName`; Lake builds that module and lean4export exports it. | `Main.lean:273`, `Main.lean:257`, `Main.lean:282` |
| `solution_module` | Required string; same conversion/build/export for the submitted solution. | `Main.lean:273`, `Main.lean:265`, `Main.lean:282` |
| `theorem_names` | Required array of strings. Root pairs must both be theorems or both axioms; their ConstantVal (name, type, universe parameters) must be identical. Their type constants enter recursive comparison. Axiom auditing separately requires solution roots to be theorems. Proofs are replayed, not required to be identical. | `Comparator/Compare.lean:65`, `Comparator/Axioms.lean:54` |
| `definition_names` | Optional array (default empty). Both roots must be definitions. ConstantVal and safety must match. Their types are recursively compared, while their bodies are deliberately excluded from equality comparison. Solution types and bodies still enter axiom checking and kernel replay. | `Main.lean:277`, `Comparator/Compare.lean:61`, `Comparator/Compare.lean:94`, `Comparator/Compare.lean:49`, `Comparator/Axioms.lean:65` |
| `permitted_axioms` | Required array. These names are also exported and compared as root constants; every axiom reachable through solution theorem and definition-hole types/bodies must belong to this exact allowlist. They are an allowance, not a report of axioms actually used. | `Main.lean:250`, `Comparator/Axioms.lean:43`, `Comparator/Util.lean:10` |
| `enable_nanoda` | Required Boolean. True adds Nat/String/Char/List and, if Quot.sound is permitted, quotient builtins to export roots and runs Nanoda on the solution export. Lean replay runs regardless. | `Main.lean:228`, `Main.lean:154`, `Main.lean:244` |

All names are exact Lean names: ordinary recursive comparison looks up the same
name in both exported maps and requires ConstantInfo equality. It includes types,
available values, inductive siblings/constructors and recursor rules through
`Comparator/Util.lean:10`. There is no automatic renaming of private declarations
or compiler-generated matchers (`Comparator/Compare.lean:44`). Required kernel
primitive definitions are checked too (`Main.lean:204`). Unknown JSON keys have
no corresponding Config field; callers should not expect them to change checks.

Environment overrides are `COMPARATOR_LANDRUN`, `COMPARATOR_LEAN4EXPORT` and
`COMPARATOR_NANODA` (`Main.lean:286`). They select executables, not weaker semantic
checks. The upstream launcher builds/exports in a Linux Landrun sandbox
(`Main.lean:79`, `Main.lean:116`, `Main.lean:136`); its README additionally requires
systemd's AF_UNIX restriction. This repository's native driver is explicitly a
trusted-cache profile: it performs serial export, strict `compareAt`,
`checkAxioms`, `Environment.replay'`, and Nanoda; it makes no sandbox assertion.

## GapCVP

`ComparatorChallenges/H_GapCVP.json` lists four theorem roots and four definition
holes: `gapCVP400Promise`, `binaryNearestCodewordPromise`,
`binarySyndromeDecodingPromise`, and `finitePGapCVPPromise`, all in
`GapCVP.Comparator`. The handmade challenge gives these definitions concrete
bodies whose disjointness proofs use `sorry`. Comparator still treats the whole
definition body as a hole, because of the configuration—not just that proof field.

Our bundle preserves exactly the four theorem and four definition root lists,
copying definition signatures with explicit whole-body holes. This can omit
constants needed only by the handmade promise bodies. Those differences are
classified as `needed by definition_names`, with a separately recorded full-body
closure. Comparator verifies the filled project definitions' types, safety,
allowed axioms and kernel acceptance. It **does not** establish that the filled
promise languages implement the human-written challenge bodies. That intent
requires additional human or mechanical review; upstream documents the same
limitation in its README's “Definition Holes” section.

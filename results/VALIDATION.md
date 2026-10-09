# surface validation

Native Windows; LEAN_NUM_THREADS=2; Lean commands execute serially. Existing target and dependency builds were reused. No target source or checker was edited.

| Item | Result | Evidence |
|---|---|---|
| 1a | PASS | Exact fields and pinned file:line references in docs/COMPARATOR_CONFIG.md. |
| 1b | PASS | All shipped theorem lists are bundled as dependency unions. |
| 1c | PASS | Twelve bundles pass Comparator and both kernels; every constant difference classified, zero generator bugs. |
| 1d | PASS | Four GapCVP definition holes supported; 50 body-only and 43 unused extra handmade constants explained. |
| 2 | FAIL | 34/36 required fixtures pass; both unsafe cases fail at Nanoda. All three negative controls are rejected. |
| 3 | FAIL | Fresh local clone runs the documented commands; cached example passes both kernels, but the required full suite is red. |
| 4 | PASS | Twelve complete result directories; cached byte-identical reproduction verified. |
| 5 | PASS | README, Apache-2.0 license, citation, changelog, release notes and 125-word Zulip draft present; claims scoped to evidence. |
| 6 | PASS | Fresh history with one initial commit; twelve-pattern content audit reports zero hits. |
| 7 | FAIL | Windows Actions workflow present and locally parsed; exact core command returns 1 for unsupported unsafe roots. |
| 8 | PASS | Reservoir and GitHub searches recorded; exact/nearby collisions linked in docs/NAME_CHECK.md; working name unchanged. |

The core suite ran in a fresh local Git clone using the exact CI command,
`python run.py test`, with the documented cache environment override. Its exit
was 1. All 17 supported fixtures pass on each pinned version, including every
source-command deletion control. The two unsafe fixtures emit their safety flags
and pass strict comparison and Lean replay, but the pinned Nanoda parser rejects
unsafe definition tags at src/parser.rs:784. They remain failures, not skips.
Statement, weakened-hypothesis and definition-body controls are each rejected
for an actual comparison mismatch.

The README's two-theorem MulticolorTriangleRamsey example returned 0 and passed
Comparator, Lean and Nanoda in the local clone. Core fixture code and checking
code were identical to the candidate snapshot. A subsequent expansion of crash
return-code handling was tested separately with simulated subprocess results;
see driver-retries.json. No actual crash or stress test was induced.

The twelve bundled comparisons and every emitted result file reproduce
byte-identically from the cached upstream, including in the fresh local clone.
Git preserves native comparison-log bytes as well as copied Lean source bytes.
Declaration counts use source command
units, including wrapped declarations and mutual blocks. Raw constant counts
include generated auxiliaries. Physical lines include blanks and comments.
See ten-proofs/SUMMARY.md and each comparison.json for the exact sets and labels.

Remaining blockers to a fully supported release:

- Explicit unsafe roots cannot pass the pinned independent kernel. Supporting
  them needs an upstream-compatible kernel path or a revised supported boundary;
  changing their safety tags or bypassing Nanoda is not a fix.
- Therefore the full required suite, fresh-clone suite acceptance and CI remain
  red. No failing check was weakened or suppressed.
- Source-command minimality is tested on the fixtures. Global minimum line count
  and minimality for arbitrary inputs are not certified; no such claim is made.

The native profile assumes trusted source, caches, imported packages, checking
binaries, operating system and hardware. It provides no adversarial sandbox.
Definition-hole body intent and mathematical statement meaning remain human
review tasks. Hints are advisory.

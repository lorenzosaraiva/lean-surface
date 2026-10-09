# surface release validation

Native Windows, `LEAN_NUM_THREADS=2`, serial Lean commands, and existing target
and dependency artifacts. No target source, upstream checker or repository
visibility was changed. No Mathlib or target rebuild was performed locally.

| Item | Result | Evidence |
|---|---|---|
| 1 | PASS | Both proof-erasure controls pass on both pinned toolchains; all four GapCVP bodies are EQUAL, with full erased trees in ten-proofs/H_GapCVP/bodies.json. Its challenge shows the project bodies verbatim and labels the Comparator exclusion. |
| 2 | PASS | Core suite exits 0: 36 fixture outcomes, including two refusals before export, plus all three Comparator rejection controls. Lean 4.32.0 and 4.29.0-rc7 are tested. |
| 3 | PASS | All twelve regenerated bundles and the summary reproduce byte-identically from cached builds, including physical and nonblank line columns. See reproduction.json. |
| 4 | PASS | Erdos 183 passes with both settings; status differs only in nanoda (PASS/skipped), and the disabled run has no binary configured. See nanoda-option.json. |
| 5 | PASS | Ubuntu core job is green. The single manual example passed both replays but failed its byte diff on log line endings; the failure is retained, and its unchanged eight-file artifact matches the corrected baseline. See CI.json. |
| 6 | PASS | README follows the requested order and measured limits; the Zulip draft is 130 words. Publication files contain zero em dashes and the twelve-pattern privacy audit has zero hits. |

The four definition-hole verdicts are:

| Definition in GapCVP.Comparator | Verdict |
|---|---|
| gapCVP400Promise | EQUAL |
| binaryNearestCodewordPromise | EQUAL |
| binarySyndromeDecodingPromise | EQUAL |
| finitePGapCVPPromise | EQUAL |

EQUAL means the independently typed body syntax agrees after `Meta.isProof`
erases proof-valued subterms. Binder names and metadata are ignored, bound
variables and universe parameters are indexed, and referenced definitions are
not unfolded. This is not a claim about intended mathematical meaning or
semantic equivalence of referenced bodies. The yes-set control returns DIFFERENT
at `$body.fn.arg.body.arg.fn.arg`, where the literals are 7 and 8.

All twelve regenerated bundles pass strict Comparator comparison, Lean replay
and Nanoda replay; all constant-set differences are classified, with zero
generator bugs. Retaining definition-hole bodies also retains their source
dependencies, so the GapCVP challenge is larger than the preceding result.
Source-command deletion minimality is tested on the safe core fixtures, not
certified for arbitrary projects or minimum line counts. Hints are advisory.

The initial local run exposed an extraction type-inference error while the
implementation was being corrected. The subsequent complete run passed.
No actual compiler crash or hardware stress test was induced for this change.
Failed attempt logs remain in the ignored local cache.

GitHub core job 113636313800 in run 37873396120 passed on the recorded commit.
Its fixture, rejection and body-control outcomes are in ci/core-suite.log.
The single manual example job 113636313666 passed comparison, Lean and Nanoda,
then failed the file diff on comparator.log alone: CRLF in the committed log,
LF on Ubuntu. The failure excerpt remains in ci/erdos-example-failure.log.
Cached log publication now uses LF, and all eight unchanged uploaded artifact
files compare byte-identically to the corrected recorded bundle. The original
job remains FAIL and was not rerun. No comparison or replay check was weakened.

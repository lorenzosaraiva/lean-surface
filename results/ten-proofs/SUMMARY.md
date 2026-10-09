# surface: shipped challenge comparison

Pinned upstream: `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`. Counts are explained in the measurement notes. Checks use the native trusted-cache profile.

| Challenge | Theirs declarations / lines | Ours declarations / lines | Constants theirs / ours | Theirs-only / ours-only | Our bugs | Lean | Nanoda |
|---|---:|---:|---:|---:|---:|---|---|
| A_SpherePacking | 20 / 185 | 20 / 289 | 75 / 75 | 0 / 0 | 0 | PASS | PASS |
| B_BinaryCodes | 44 / 197 | 38 / 237 | 61 / 55 | 6 / 0 | 0 | PASS | PASS |
| B_SphericalCodes | 65 / 302 | 63 / 498 | 99 / 97 | 2 / 0 | 0 | PASS | PASS |
| C_PermanentFormulaLowerBound | 10 / 102 | 10 / 114 | 137 / 137 | 0 / 0 | 0 | PASS | PASS |
| D_NonSoficGroup | 5 / 39 | 5 / 66 | 36 / 36 | 0 / 0 | 0 | PASS | PASS |
| E_ConnesRigidity | 25 / 223 | 25 / 241 | 100 / 100 | 0 / 0 | 0 | PASS | PASS |
| F_EhrhartVolumeInequality | 14 / 78 | 14 / 141 | 34 / 34 | 0 / 0 | 0 | PASS | PASS |
| G_QuantumParallelRepetition | 14 / 139 | 14 / 171 | 91 / 91 | 0 / 0 | 0 | PASS | PASS |
| H_GapCVP | 44 / 313 | 17 / 115 | 145 / 52 | 93 / 0 | 0 | PASS | PASS |
| I_MulticolorTriangleRamsey | 7 / 50 | 7 / 61 | 7 / 7 | 0 / 0 | 0 | PASS | PASS |
| J_CompactnessConjecture | 11 / 90 | 11 / 120 | 29 / 29 | 0 / 0 | 0 | PASS | PASS |
| J_TwoDegenerateGraphs | 6 / 47 | 6 / 66 | 6 / 6 | 0 / 0 | 0 | PASS | PASS |

Source declarations count Lean parser declaration/lemma commands and mutual command blocks; generated constant counts include constructors, projections and auxiliaries. Physical source lines include comments and blanks. The same source command unit policy is used for both sides. Definition hole bodies are excluded from comparison; their type dependencies remain checked. Each constant difference is recorded in comparison.json.

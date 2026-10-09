# surface: shipped challenge comparison

Pinned upstream: `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`. Counts are explained in the measurement notes. Checks use the native trusted-cache profile.

| Challenge | Theirs declarations / lines | Theirs nonblank | Ours declarations / lines | Ours nonblank | Constants theirs / ours | Theirs-only / ours-only | Our bugs | Lean | Nanoda |
|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| A_SpherePacking | 20 / 185 | 149 | 20 / 289 | 203 | 75 / 75 | 0 / 0 | 0 | PASS | PASS |
| B_BinaryCodes | 44 / 197 | 142 | 38 / 237 | 162 | 61 / 55 | 6 / 0 | 0 | PASS | PASS |
| B_SphericalCodes | 65 / 302 | 215 | 63 / 498 | 318 | 99 / 97 | 2 / 0 | 0 | PASS | PASS |
| C_PermanentFormulaLowerBound | 10 / 102 | 83 | 10 / 114 | 90 | 137 / 137 | 0 / 0 | 0 | PASS | PASS |
| D_NonSoficGroup | 5 / 39 | 28 | 5 / 66 | 44 | 36 / 36 | 0 / 0 | 0 | PASS | PASS |
| E_ConnesRigidity | 25 / 223 | 183 | 25 / 241 | 195 | 100 / 100 | 0 / 0 | 0 | PASS | PASS |
| F_EhrhartVolumeInequality | 14 / 78 | 55 | 14 / 141 | 104 | 34 / 34 | 0 / 0 | 0 | PASS | PASS |
| G_QuantumParallelRepetition | 14 / 139 | 111 | 14 / 171 | 127 | 91 / 91 | 0 / 0 | 0 | PASS | PASS |
| H_GapCVP | 44 / 313 | 258 | 80 / 853 | 740 | 145 / 320 | 2 / 177 | 0 | PASS | PASS |
| I_MulticolorTriangleRamsey | 7 / 50 | 40 | 7 / 61 | 47 | 7 / 7 | 0 / 0 | 0 | PASS | PASS |
| J_CompactnessConjecture | 11 / 90 | 73 | 11 / 120 | 89 | 29 / 29 | 0 / 0 | 0 | PASS | PASS |
| J_TwoDegenerateGraphs | 6 / 47 | 38 | 6 / 66 | 48 | 6 / 6 | 0 / 0 | 0 | PASS | PASS |

Source declarations count Lean parser declaration/lemma commands and mutual command blocks; generated constant counts include constructors, projections and auxiliaries. Physical source lines include comments and blanks; nonblank lines count lines containing a non-whitespace byte. The same source command unit policy is used for both sides. Definition hole bodies are copied verbatim but excluded from Comparator comparison; their type dependencies remain checked. bodies.json separately compares project and handmade bodies after proof erasure. Each constant difference is recorded in comparison.json.

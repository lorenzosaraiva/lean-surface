surface extracts standalone Lean statement-review challenges from built projects, bundles shared definitions, and checks them with Comparator and Lean replay; Nanoda is enabled by default.

In the pinned ten-proofs checkout, all four GapCVP definition-hole bodies compared EQUAL to the handmade bodies after replacing proof-valued subterms with one placeholder. Comparator itself excludes these bodies from comparison. The generated challenge now displays the project bodies verbatim, and a separate check records the erased trees and any first structural difference. It does not unfold referenced definitions or establish intended mathematical meaning.

The repository includes constant-level bundle comparisons, deletion tests, negative controls and unsafe-root refusal tests. Hints are advisory. The native driver assumes trusted source and caches and provides no adversarial sandbox. Feedback on the supported syntax boundary and definition-body presentation would be useful.

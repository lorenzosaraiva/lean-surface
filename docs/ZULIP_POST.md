I am working on surface, a Lean statement-review tool. Given theorem names in a
built project, it extracts a standalone challenge from the source definitions
used by their types. It can bundle related statements and leaves external
packages as imports. The native trusted-cache driver checks the generated
challenge against the project with Comparator and replays the solution in Lean
and Nanoda. It does not provide an adversarial sandbox.

The repository includes synthetic deletion tests, negative comparison controls,
and constant-level comparisons with the shipped ten-proofs challenges. The
validation reports list failures and unsupported syntax. Hints are advisory;
humans still need to judge statement meaning and definition-hole intent.

This is a release candidate. Feedback on the supported boundary, source command
minimality and definition-hole presentation would be useful.

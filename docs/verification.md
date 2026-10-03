# Verification boundary

The reusable proof gate and predictive renderer are pinned to official
PalomarSubmission commit `65f0154ed776cd26c224254aa57b379137f28b0d`.
Workflow and pipeline pins are equal. Proof mode is `full` and the execution
profile is `palomar-standard-v1`. Proof request identifiers must contain exactly
12 lowercase alphanumeric characters and are passed through the official
request parser before dispatch.

Local checks compile the complete library and economically nonvacuous examples;
the standalone Challenge elaborates using only canonical mathlib/Lean imports.
All 17 `definition_names` are actual Lean definitions in both environments.
The full module-origin audit covers every authored library constant, including
compiler auxiliary declarations, and permits only the three standard axioms.

On this Mac the official Comparator must use its explicit no-sandbox flag:
Linux bubblewrap is unavailable. This local check is recorded as such. Hosted
full verification supplies official source isolation and mandatory Lean,
NanoDa and con-ron kernel replay. Local independent-kernel checks are useful
supporting evidence but do not replace that hosted gate.

The renderer workflow is the official renderer dispatch ported into this public
repository with exact official source checkout and renderer provenance pins.
It keeps official exact-tag Verso selection, core-notation audit, sanitizer,
resource profile, 8 MiB per-file limit and 25 MiB aggregate limit. Rendering
and proof verification are distinct gates. Downloaded reports must bind the
same exact source commit and expected Challenge SHA-256; their artifact
manifests/digests must be inspected, and all required statuses must pass.

A commit is mechanically ready only after both hosted gates pass and their
reports/artifacts are verified. Predictive workflows create no Palomar intake,
registration or editorial-review state. Final immutable source archive and
exact run URLs are delivered separately without changing the verified commit.

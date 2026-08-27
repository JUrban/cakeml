This directory contains tests that evaluate the type inferencer inside
the logic of HOL.

[basisTypeCheckScript.sml](basisTypeCheckScript.sml):
This file checks that the CakeML standard basis library passes the
type inferencer. This file also acts as a test of cv_compute
evaluation of the type inferencer.

[dopenTestsScript.sml](dopenTestsScript.sml):
Executable declaration-open regressions for single and nested paths, missing
and empty paths, exact inference-state preservation, dynamic-state
preservation, and declaration-delta (rather than combined-environment)
results.

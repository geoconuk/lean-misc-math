/-
Copyright (c) 2026 George Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# lean-misc-math

Root module: importing `MiscMath` gives you every result in this library.

Every file under `MiscMath/` other than `MiscMath/Meta/` and `MiscMath/Audit.lean`
must be imported here, in alphabetical order, directly above this docstring.
`scripts/check-imports.sh` enforces this in CI, so that the axiom audit in
`MiscMath/Audit.lean` — which only sees what this file transitively imports — cannot
silently miss a result file.

(Lean requires `import` lines to precede every other command, including this
docstring, so the import block sits above the copyright header's closing delimiter
once there is one.)
-/

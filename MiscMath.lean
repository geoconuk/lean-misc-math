/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MiscMath.Geometry.SphereCoveringExponent
import MiscMath.Probability.PoissonTrialsFixedMean

/-!
# lean-misc-math

Root module: importing `MiscMath` gives you every result in this library.

Every file under `MiscMath/` other than `MiscMath/Meta/` and `MiscMath/Audit.lean`
must be imported here, in alphabetical order. `scripts/check-imports.sh` enforces this
in CI, so that the axiom audit in `MiscMath/Audit.lean` — which only sees what this
file transitively imports — cannot silently miss a result file.

Lean requires `import` lines to precede every other command, including a module
docstring, so they go between the copyright comment above and this docstring:

    /- Copyright … -/
    import MiscMath.Area.First
    import MiscMath.Area.Second
    /-! # lean-misc-math … -/

-/

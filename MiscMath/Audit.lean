/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all MiscMath
import all MiscMath.Analysis.KolmogorovArnold
import all MiscMath.Analysis.KolmogorovArnold.Approximant
import all MiscMath.Analysis.KolmogorovArnold.Cells
import all MiscMath.Analysis.KolmogorovArnold.Density
import all MiscMath.Analysis.KolmogorovArnold.Extend
import all MiscMath.Analysis.KolmogorovArnold.Generic
import all MiscMath.Analysis.KolmogorovArnold.InnerSpace
import all MiscMath.Analysis.KolmogorovArnold.Levels
import all MiscMath.Analysis.KolmogorovArnold.RationalIndependence
import all MiscMath.Analysis.KolmogorovArnold.Representation
import all MiscMath.Analysis.KolmogorovArnold.Staircase
import all MiscMath.Analysis.KolmogorovArnold.StrictlyIncreasing
import all MiscMath.Analysis.KolmogorovArnold.Superposition
import all MiscMath.Computability.RedBluePebbleGame
import all MiscMath.Computability.RedBluePebbleGame.Bounds
import all MiscMath.Computability.RedBluePebbleGame.Butterfly
import all MiscMath.Computability.RedBluePebbleGame.Calculation
import all MiscMath.Computability.RedBluePebbleGame.Domination
import all MiscMath.Computability.RedBluePebbleGame.Feasibility
import all MiscMath.Computability.RedBluePebbleGame.LogBound
import all MiscMath.Computability.RedBluePebbleGame.MatMul
import all MiscMath.Computability.RedBluePebbleGame.MatMulChain
import all MiscMath.Computability.RedBluePebbleGame.Partition
import all MiscMath.Computability.RedBluePebbleGame.Parts
import all MiscMath.Computability.RedBluePebbleGame.Spec
import all MiscMath.Geometry.SphereCoveringExponent
import all MiscMath.Meta.AxiomAudit
import all MiscMath.Probability.PoissonTrialsFixedMean
import all MiscMath.Probability.PoissonTrialsFixedMean.BinomialTail
import all MiscMath.Probability.PoissonTrialsFixedMean.Bridge
import all MiscMath.Probability.PoissonTrialsFixedMean.ConvexExtremum
import all MiscMath.Probability.PoissonTrialsFixedMean.ExtremalShapes
import all MiscMath.Probability.PoissonTrialsFixedMean.Model
import all MiscMath.Probability.PoissonTrialsFixedMean.TailBounds

/-!
# Library-wide axiom audit

This module exists only to run `#audit_axioms` over the whole library. It imports every module
under `MiscMath/` and is itself a build target, so `lake build` fails if any declaration anywhere
in `MiscMath.*` depends on an axiom outside `{propext, Classical.choice, Quot.sound}`.

Every module is imported with `import all`, and every module is named. Under Lean's module system
a plain import shows only a module's public declarations, and the audit must see the private ones
too: a `private` lemma with a `sorry` in it is a hole like any other. `import all` shows them, but
only for the module it names, not for the modules that one imports. So importing the root
`MiscMath` would reach every public declaration and miss the private ones, and naming each module
here is the only way to cover them all. `scripts/check-imports.sh` fails if one is missing, and
`scripts/self-test-audit.sh` checks that a private `sorry` is caught.

Do not put results in this file.
-/

#audit_axioms

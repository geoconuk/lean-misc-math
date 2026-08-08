/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MiscMath
import MiscMath.Meta.AxiomAudit

/-!
# Library-wide axiom audit

This module exists only to run `#audit_axioms` over the whole library. It imports
`MiscMath` (which transitively imports every result) and is itself a build target,
so `lake build` fails if any declaration anywhere in `MiscMath.*` depends on an axiom
outside `{propext, Classical.choice, Quot.sound}`.

Do not put results in this file.
-/

#audit_axioms

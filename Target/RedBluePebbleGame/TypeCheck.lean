/-
Copyright (c) 2026 George A. Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George A. Constantinides (selection, specification), Claude (formalisation, proof)
-/
import Target.RedBluePebbleGame
import MiscMath.Computability.RedBluePebbleGame

/-!
# The proved theorems are the frozen targets

`Target/RedBluePebbleGame.lean` states the advertised theorems of
`MiscMath.Computability.RedBluePebbleGame` as they were read and frozen, with `sorry`. Each
`example` below ascribes a target's type, read off the target by `type_of%`, to the theorem the
library proves. So a library statement that drifts from what was read fails to build here: the
two types must agree up to definitional unfolding, which fixes every binder, hypothesis and
conclusion.

The library's statements are also textually the targets' statements, so that the read covers
them. This module checks the types, not the text.

This module is deliberately outside `MiscMath/` and outside `defaultTargets`, as the target is.
It asserts real theorems and contains no `sorry` of its own; the targets it reads are the only
declarations it sees that do. Build it with `lake build RedBluePebbleGameTypeCheck`.
-/

example : type_of% @Target.RedBluePebbleGame.fft_io_lower_bound :=
  @MiscMath.Computability.fft_io_lower_bound

example : type_of% @Target.RedBluePebbleGame.fft_io_bounds :=
  @MiscMath.Computability.fft_io_bounds

example : type_of% @Target.RedBluePebbleGame.fft_complete_iff :=
  @MiscMath.Computability.fft_complete_iff

example : type_of% @Target.RedBluePebbleGame.fft_io_lower_bound_isBigO :=
  @MiscMath.Computability.fft_io_lower_bound_isBigO

example : type_of% @Target.RedBluePebbleGame.exists_partition_of_hasCompleteCalculation :=
  @MiscMath.Computability.exists_partition_of_hasCompleteCalculation

example : type_of% @Target.RedBluePebbleGame.io_lower_bound_of_parts :=
  @MiscMath.Computability.io_lower_bound_of_parts

example : type_of% @Target.RedBluePebbleGame.minIOTime_lower_bound :=
  @MiscMath.Computability.minIOTime_lower_bound

example : type_of% @Target.RedBluePebbleGame.fft_parts_lower_bound :=
  @MiscMath.Computability.fft_parts_lower_bound

example : type_of% @Target.RedBluePebbleGame.fft_parts_lower_bound_isBigO :=
  @MiscMath.Computability.fft_parts_lower_bound_isBigO

example : type_of% @Target.RedBluePebbleGame.matMul_io_lower_bound :=
  @MiscMath.Computability.matMul_io_lower_bound

example : type_of% @Target.RedBluePebbleGame.matMul_io_bounds :=
  @MiscMath.Computability.matMul_io_bounds

example : type_of% @Target.RedBluePebbleGame.exists_isMatMulEvaluation :=
  @MiscMath.Computability.exists_isMatMulEvaluation

example : type_of% @Target.RedBluePebbleGame.matMul_io_lower_bound_isBigO :=
  @MiscMath.Computability.matMul_io_lower_bound_isBigO

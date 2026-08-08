/-
Copyright (c) 2026 George Constantinides. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Axiom audit

This file provides the `#audit_axioms` command, which is the single most important
automated check in this repository.

Lean's kernel guarantees that every proof here is *correct*. It does not guarantee
that a proof rests only on the axioms we intend, and it does not stop a file from
introducing new axioms of its own. `#audit_axioms` walks every declaration in every
`MiscMath.*` module and fails the build unless its transitive axiom dependencies are
a subset of the three axioms of classical Lean:

* `propext` — propositional extensionality
* `Classical.choice` — the axiom of choice
* `Quot.sound` — soundness of quotient types

This single check subsumes several guards at once. A `sorry` anywhere in a proof
shows up as `sorryAx`; a bespoke `axiom` declaration shows up under its own name;
`native_decide` shows up as `Lean.ofReduceBool` / `Lean.trustCompiler`. All of them
fail the audit.

It is deliberately *semantic* rather than textual: it inspects the elaborated proof
terms, so it cannot be evaded by comments, macros, or clever formatting.

## What this does not check

The audit says nothing about whether a theorem *statement* says what its docstring
claims. That is the one thing no automated check can do, and it is why statements get
a best-effort read from the author and why every result file carries an informal
statement, a citation, and concrete sanity checks. None of that is a review; see
`README.md` for exactly what is and is not guaranteed.
-/

open Lean Elab Command

namespace MiscMath.Meta

/-- The axioms a declaration in this library is permitted to depend on: exactly the
three axioms of classical Lean, which are what ordinary Mathlib proofs use.

Notably absent: `sorryAx`, `Lean.ofReduceBool` and `Lean.trustCompiler` (introduced by
`native_decide`), and any locally declared `axiom`. -/
def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- The module namespace whose declarations are audited. -/
def auditedRoot : Name := `MiscMath

/-- Is `m` a module belonging to this library? -/
def isAuditedModule (m : Name) : Bool :=
  m == auditedRoot || auditedRoot.isPrefixOf m

/-- Audit every declaration in every imported `MiscMath.*` module, and throw an error
listing any declaration that depends on an axiom outside `allowedAxioms`.

Intended to be invoked exactly once, from `MiscMath/Audit.lean`, which imports the
whole library. Because that file is part of the default build target, `lake build`
runs the audit and a violation breaks the build. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let moduleData := env.header.moduleData
  -- The type ascription matters: `checked` is interpolated into a `m!` string below,
  -- and without it the numeral's type unifies with `MessageData`.
  let mut checked : Nat := 0
  let mut audited : Array Name := #[]
  let mut violations : Array (Name × Array Name) := #[]
  for i in [0 : moduleNames.size] do
    let m := moduleNames[i]!
    unless isAuditedModule m do continue
    audited := audited.push m
    for declName in moduleData[i]!.constNames do
      checked := checked + 1
      let axioms ← liftCoreM <| collectAxioms declName
      let bad := axioms.filter fun a => !allowedAxioms.contains a
      unless bad.isEmpty do
        violations := violations.push (declName, bad)
  if violations.isEmpty then
    logInfo m!"axiom audit passed: {checked} declarations across \
      {audited.size} modules depend only on {allowedAxioms.toList}"
  else
    let details := violations.toList.map fun (n, bad) => m!"\n  {n} depends on {bad.toList}"
    throwError m!"axiom audit FAILED: {violations.size} declaration(s) depend on \
      disallowed axioms.{MessageData.joinSep details ""}\n\n\
      Permitted axioms are {allowedAxioms.toList}. A `sorryAx` here means an \
      incomplete proof; `Lean.ofReduceBool` means `native_decide` was used; any \
      other name means an `axiom` was declared."

end MiscMath.Meta

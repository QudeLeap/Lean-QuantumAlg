/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Values
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Preservation

/-!
# Actual candidate words connected to the two complete divisor checks

The source center and square-root destinations become the actual one and
remainder cells only after both candidate words have been materialized. The
five real checker allocations supply their zero word and result bits. Thus
the actual two stored predicates refer to the original source candidates;
there is no caller initialization premise or separate arithmetic witness.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The checks receive exactly the candidate words and the reused old center and root cells. -/
def checkedOperands (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (selector : FirstAccepted.Refs ctx (RSA.quadraticWordWidth width)) :
    CheckLayout.Operands ctx (RSA.quadraticWordWidth width) where
  modulus := modulus
  one := .storage refs.center.toCStorageRef
  remainder := refs.root
  first := .storage refs.first.toCStorageRef
  second := .storage refs.second.toCStorageRef
  selection := selector

/-- Actual candidate-cell separation discharges every still-live source/remainder distinction. -/
lemma nativeQuadratic_checkedOperands_separated
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (selector : FirstAccepted.Refs ctx (RSA.quadraticWordWidth width))
    (separated : Separated modulus refs) :
    CheckLayout.OperandsSeparated (checkedOperands modulus refs selector) where
  remainderModulus := separated.modulusFree refs.root.key (by simp [writeKeys])
  remainderOne := fun present => separated.centerRoot (List.mem_singleton.mp present).symm
  remainderFirst := fun present => separated.rootFirst (List.mem_singleton.mp present)
  remainderSecond := fun present => separated.rootSecond (List.mem_singleton.mp present)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual initialized arithmetic, fresh checker entry and both checks yield the source decisions.
-/
lemma nativeQuadratic_loaded_checks_values (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (selector : FirstAccepted.Refs ctx (RSA.quadraticWordWidth width))
    (separated : Separated modulus refs) (store : Store ctx) :
    let initialized := (Initialized.step (model := model) input modulus refs store).1
    let entered := CheckLayout.pushStore (RSA.quadraticWordWidth width) initialized
    let checked := Pair.checkedStore
      (CheckLayout.pairRefs (checkedOperands modulus refs selector)) entered
    let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
    (checked.read (.storage
        (CheckLayout.firstValid ctx (RSA.quadraticWordWidth width)).toCStorageRef)).toBool =
        decide (1 < source.1 ∧ source.1 < (store.read modulus).toNat ∧
          (store.read modulus).toNat % source.1 = 0) ∧
      (checked.read (.storage
        (CheckLayout.secondValid ctx (RSA.quadraticWordWidth width)).toCStorageRef)).toBool =
        decide (1 < source.2 ∧ source.2 < (store.read modulus).toNat ∧
          (store.read modulus).toNat % source.2 = 0) := by
  let work := RSA.quadraticWordWidth width
  let operands := checkedOperands modulus refs selector
  let initialized := (Initialized.step (model := model) input modulus refs store).1
  let entered := CheckLayout.pushStore work initialized
  have materialized := Initialized.nativeQuadratic_initialized_values (model := model)
    input modulus refs separated store
  have modulusBefore := nativeQuadratic_initialized_read_other (model := model)
    input modulus refs modulus separated.modulusFree store
  have modulusEntered := congrArg CShape.Value.toNat
    (CheckLayout.nativeQuadratic_checkLayout_push_read modulus work initialized)
  have firstEntered := congrArg CShape.Value.toNat
    (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage refs.first.toCStorageRef) work initialized)
  have secondEntered := congrArg CShape.Value.toNat
    (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage refs.second.toCStorageRef) work initialized)
  have oneEntered := congrArg CShape.Value.toNat
    (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage refs.center.toCStorageRef) work initialized)
  have actual := CheckLayout.nativeQuadratic_checks_values operands
    (nativeQuadratic_checkedOperands_separated modulus refs selector separated) entered
    (oneEntered.trans materialized.2)
    (CheckLayout.nativeQuadratic_checkLayout_push_zero_toNat work initialized)
  have modulusOriginal := modulusEntered.trans (congrArg CShape.Value.toNat modulusBefore)
  have firstOriginal := firstEntered.trans (congrArg Prod.fst materialized.1)
  have secondOriginal := secondEntered.trans (congrArg Prod.snd materialized.1)
  refine ⟨actual.1.trans ?_, actual.2.trans ?_⟩
  · exact congrArg₂ (fun modulus candidate : Nat =>
      decide (1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0))
      modulusOriginal firstOriginal
  · exact congrArg₂ (fun modulus candidate : Nat =>
      decide (1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0))
      modulusOriginal secondOriginal

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

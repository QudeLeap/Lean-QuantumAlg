/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Entry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair.Readout

/-!
# Source values from actual initialized checks and local selection

The actual program entry and one loader establish all constants and initial
latch values used here. The same Pair.step executes both complete checks and
both ordered selectors. Its stored result is the first valid source quadratic
candidate, or zero with a false acceptance flag when neither candidate is a
nontrivial divisor. Every input width and every stored modulus are included.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open Execution
open ClassicalRoutines

variable {width : Nat}

private lemma choice_toNat (accepted firstValid secondValid : Bool)
    (old first second : CShape.Value (.unsignedWord width)) :
    (if accepted then old else
      if firstValid then first else if secondValid then second else old).toNat =
      if accepted then old.toNat else
        if firstValid then first.toNat else if secondValid then second.toNat else old.toNat := by
  cases accepted <;> cases firstValid <;> cases secondValid <;> rfl

private lemma choice_replace
    {accepted firstValid secondValid sourceFirstValid sourceSecondValid : Bool}
    {old first second sourceFirst sourceSecond : Nat}
    (acceptedEq : accepted = false)
    (firstTest : firstValid = sourceFirstValid) (secondTest : secondValid = sourceSecondValid)
    (oldEq : old = 0) (firstEq : first = sourceFirst) (secondEq : second = sourceSecond) :
    (if accepted then old else if firstValid then first else if secondValid then second else old) =
      if sourceFirstValid then sourceFirst else if sourceSecondValid then sourceSecond else 0 := by
  cases acceptedEq
  cases firstTest
  cases secondTest
  cases oldEq
  cases firstEq
  cases secondEq
  rfl

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

set_option maxHeartbeats 800000 in -- Normalize reads through the thirteen actual lexical cells.
/-- Actual entry, native arithmetic, both complete checks and selection give the source result. -/
lemma nativeQuadratic_local_pair_values (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) (store : Store ctx) :
    let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
    let firstValid := decide (1 < source.1 ∧ source.1 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.1 = 0)
    let secondValid := decide (1 < source.2 ∧ source.2 < (store.read modulus).toNat ∧
      (store.read modulus).toNat % source.2 = 0)
    let entered := CheckLayout.pushStore (RSA.quadraticWordWidth width)
      (initializedStore (model := model) input modulus store)
    let final := (Pair.step (model := model) (pairRefs modulus) entered).1
    (final.read (FirstAccepted.cellRead (pairRefs modulus).selection.accepted)).toBool =
        (firstValid || secondValid) ∧
      (final.read (FirstAccepted.cellRead (pairRefs modulus).selection.selected)).toNat =
        if firstValid then source.1 else if secondValid then source.2 else 0 := by
  let work := RSA.quadraticWordWidth width
  let initialized : Store (candidateContext ctx width) :=
    initializedStore (model := model) input modulus store
  let entered : Store (CheckLayout.context (candidateContext ctx width) work) :=
    CheckLayout.pushStore work initialized
  let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
  have materialized := nativeQuadratic_local_initialized_values (model := model)
    input modulus store
  have firstOriginal : (entered.read (CheckLayout.underRead (operands modulus).first work)).toNat =
      source.1 :=
    (congrArg CShape.Value.toNat (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage (arithmeticRefs ctx width).first.toCStorageRef) work initialized)).trans
      (congrArg Prod.fst materialized.1)
  have secondOriginal :
      (entered.read (CheckLayout.underRead (operands modulus).second work)).toNat = source.2 :=
    (congrArg CShape.Value.toNat (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage (arithmeticRefs ctx width).second.toCStorageRef) work initialized)).trans
      (congrArg Prod.snd materialized.1)
  have oneValue : (entered.read (CheckLayout.underRead (operands modulus).one work)).toNat = 1 :=
    (congrArg CShape.Value.toNat (CheckLayout.nativeQuadratic_checkLayout_push_read
      (.storage (arithmeticRefs ctx width).center.toCStorageRef) work initialized)).trans
      materialized.2
  have modulusKept := nativeQuadratic_initialized_read_other (model := model)
    (arithmeticRead input width)
    (arithmeticRead modulus width) (arithmeticRefs ctx width) (arithmeticRead modulus width)
    (nativeQuadratic_layout_separated
      (SelectionLayout.underRead modulus work)).modulusFree (entryStore width store)
  have modulusOriginal :
      (entered.read (CheckLayout.underRead (operands modulus).modulus work)).toNat =
        (store.read modulus).toNat :=
    (congrArg CShape.Value.toNat (CheckLayout.nativeQuadratic_checkLayout_push_read
      (arithmeticRead modulus width) work initialized)).trans
      (congrArg CShape.Value.toNat
        (modulusKept.trans (nativeQuadratic_local_entry_read modulus width store)))
  have acceptedBefore :
      (entered.read (CheckLayout.underRead
        (FirstAccepted.cellRead (operands modulus).selection.accepted) work)).toBool = false :=
    congrArg CShape.Value.toBool
      ((CheckLayout.nativeQuadratic_checkLayout_push_read
        (FirstAccepted.cellRead (localRefs ctx width).accepted) work initialized).trans
        (nativeQuadratic_local_initialized_accepted (model := model) input modulus store))
  have selectedBefore :
      (entered.read (CheckLayout.underRead
        (FirstAccepted.cellRead (operands modulus).selection.selected) work)).toNat = 0 :=
    (congrArg CShape.Value.toNat
      ((CheckLayout.nativeQuadratic_checkLayout_push_read
        (FirstAccepted.cellRead (localRefs ctx width).selected) work initialized).trans
        (nativeQuadratic_local_initialized_selected (model := model)
          input modulus store))).trans (Nat.zero_mod _)
  have firstTest := congrArg₂ (fun modulus candidate : Nat =>
    decide (1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0))
    modulusOriginal firstOriginal
  have secondTest := congrArg₂ (fun modulus candidate : Nat =>
    decide (1 < candidate ∧ candidate < modulus ∧ modulus % candidate = 0))
    modulusOriginal secondOriginal
  have actual := CheckLayout.nativeQuadratic_checked_pair_latches (model := model)
    (operands modulus)
    (nativeQuadratic_local_operands_separated modulus)
    (nativeQuadratic_local_selector_separated modulus) entered oneValue
    (CheckLayout.nativeQuadratic_checkLayout_push_zero_toNat work initialized)
  refine ⟨actual.1.trans ?_, (congrArg CShape.Value.toNat actual.2).trans ?_⟩
  · exact congrArg₂ Bool.or (congrArg₂ Bool.or acceptedBefore firstTest) secondTest
  · refine (choice_toNat _ _ _ _ _ _).trans ?_
    exact choice_replace acceptedBefore firstTest secondTest selectedBefore
      firstOriginal secondOriginal

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

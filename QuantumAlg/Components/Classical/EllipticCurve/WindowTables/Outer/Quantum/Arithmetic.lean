/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting
import all QuantumAlg.Components.Classical.ConstantWord.Trace
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# No quantum event is charged by the actual native classical arithmetic

Every bound projects the original physical event pool. The coefficient
engine includes its real constant loader, widened Euclidean steps and
both signed-reduction branches; none is counted as a quantum gate or MZ.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

open Execution ClassicalAlgorithms.Modular Modular.NativePower
open Field.Native Field.Native.Shared
open NumberTheory.XGCD.Native NumberTheory.XGCD
open NumberTheory.Checked.SignedReduction.Native
open Modular.Reduce.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

variable (focus : Resource.Event model)
  (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate)

include model nativeFree

private lemma loader_count_zero (width : Nat) (bits : List Bool) :
    ResourcePool.count focus
      (ResourcePool.ofList (ConstantWord.loaderTrace model width bits)) = 0 := by
  induction bits with
  | nil => simp [ConstantWord.loaderTrace]
  | cons bit remaining ih =>
      change ResourcePool.count focus
        (ResourcePool.ofList (([ConstantWord.shiftEvent model width] ++
          if bit then [ConstantWord.incrementEvent model width] else []) ++
            ConstantWord.loaderTrace model width remaining)) = 0
      rw [ResourcePool.ofList_append, ResourcePool.count_add, ih]
      cases bit <;> simp [ConstantWord.shiftEvent, ConstantWord.incrementEvent,
        fun coordinate => (nativeFree coordinate).symm]

/-- The complete original total coefficient allowance contains only actual classical operations. -/
lemma coefficientEnvelope_count_zero {width : Nat} (spec : ModulusSpec width) :
    ResourcePool.count focus (coefficientEnvelope model spec) = 0 := by
  have reversed (coordinate) : (.classicalOperation coordinate : Resource.Event model) ≠ focus :=
    (nativeFree coordinate).symm
  simp [coefficientEnvelope, loader_count_zero focus nativeFree,
    rawEnvelope, initializationEvents, activeEvents, coefficientUpdateEvents, rawOutputEvents,
    signedReductionEnvelope, signClassificationEvents, signedMagnitudeEvents,
    finalCorrectionEvents, negativeCorrectionEvents, reductionEvents, reversed]

variable {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual loaded total inverse contributes no quantum event on every original input. -/
lemma coefficient_count_zero (spec : ModulusSpec width)
    (input : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientIntoWord (model := model) spec input output).Path) :
    ResourcePool.count focus
      ((coefficientIntoWord (model := model) spec input output).resourcePool path) = 0 := by
  have actual := Multiset.count_le_of_le focus (coefficientIntoWord_pool_le spec input output path)
  have allowance := coefficientEnvelope_count_zero focus nativeFree spec
  change Multiset.count focus (coefficientEnvelope model spec) = 0 at allowance
  change Multiset.count focus ((coefficientIntoWord spec input output).resourcePool path) = 0
  exact Nat.eq_zero_of_le_zero (actual.trans_eq allowance)

/-- Existing full-product/division/resize storage introduces no quantum event. -/
lemma multiply_count_zero (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scopedMultiply (model := model) left right modulus output).Path) :
    ResourcePool.count focus
      ((scopedMultiply (model := model) left right modulus output).resourcePool path) = 0 := by
  rw [nativePower_scopedMultiply_pool]
  simp [multiplyEnvelope, fun coordinate => (nativeFree coordinate).symm]

/-- Shared-modulus addition retains its actual five classical coordinates. -/
lemma add_count_zero (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) left right modulus output).Path) :
    ResourcePool.count focus
      ((addIntoWord (model := model) left right modulus output).resourcePool path) = 0 := by
  rw [sharedAddIntoWord_resourcePool]
  simp [addTrace, Field.Native.additionPrefixTrace, reductionEvents,
    fun coordinate => (nativeFree coordinate).symm]

/-- Shared-modulus subtraction retains its actual six classical coordinates. -/
lemma sub_count_zero (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) left right modulus output).Path) :
    ResourcePool.count focus
      ((subIntoWord (model := model) left right modulus output).resourcePool path) = 0 := by
  rw [sharedSubIntoWord_resourcePool]
  simp [subTrace, reductionEvents, fun coordinate => (nativeFree coordinate).symm]

/-- Every single closed native instruction is charged only at its actual classical coordinate. -/
lemma instruction_count_zero {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (path : (BitWord.instruction (execution := model) op).Path) :
    ResourcePool.count focus
      ((BitWord.instruction (execution := model) op).resourcePool path) = 0 := by
  rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
  simp [fun coordinate => (nativeFree coordinate).symm]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

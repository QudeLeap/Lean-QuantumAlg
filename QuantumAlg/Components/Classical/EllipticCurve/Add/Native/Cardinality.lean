/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Cardinality

/-!
# Original numerical ceiling for actual complete elliptic-curve addition

All original finite arms and their real field loaders contribute to the
independent coordinatewise allowance. The actual dispatch tree retains both
vertical sites. Counting their union is bounded by adding both alternatives;
no equality with a maximum of scalar branch counts is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve Field.Native

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual nine-stage affine allowance includes every original arithmetic call. -/
lemma affineEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) :
    (affineEnvelope model spec).card ≤ 52 * width + 126 := by
  have coefficient := coefficientEnvelope_card_le model spec
  have product := multiplicationTrace_length_le model spec
  have subtraction := subtractionTrace_length_le model spec
  simp only [affineEnvelope, affineStageEnvelope, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

/-- Both real slope subtractions precede the same actual affine allowance. -/
lemma genericEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) :
    (genericEnvelope model spec).card ≤ 60 * width + 146 := by
  have affine := affineEnvelope_card_le model spec
  have subtraction := subtractionTrace_length_le model spec
  simp only [genericEnvelope, Multiset.card_add, ResourcePool.ofList, Multiset.coe_card]
  omega

/-- The actual public curve coefficient loader is charged once per doubling call. -/
lemma doublingLoaderTrace_length_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width) :
    (doublingLoaderTrace model spec).length ≤ 2 * width :=
  ConstantWord.constantLoader_length_le model width (doublingCurveAWord spec).toNat

/-- All seven original doubling stages fit their complete width-linear allowance. -/
lemma doublingEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width) :
    (doublingEnvelope model spec).card ≤ 64 * width + 159 := by
  have product := multiplicationTrace_length_le model spec.field
  have addition := additionTrace_length_le model spec.field
  have loaded := doublingLoaderTrace_length_le model spec
  have affine := affineEnvelope_card_le model spec.field
  simp only [doublingEnvelope, doublingStageEnvelope, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    Multiset.card_add, ResourcePool.ofList, Multiset.coe_card]
  omega

omit [BitWord.Selected model] in
private lemma max_card_le_add (left right : ResourcePool model) :
    (ResourcePool.max left right).card ≤ left.card + right.card :=
  (Multiset.card_le_card (Multiset.union_le_add left right)).trans_eq
    (Multiset.card_add left right)

/-- The complete original dispatch allowance obeys the original public numerical ceiling. -/
lemma additionEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width) :
    (additionEnvelope model spec).card ≤ 124 * width + 322 := by
  have generic := genericEnvelope_card_le model spec.field
  have doubling := doublingEnvelope_card_le model spec
  have branchBound : (additionBranchEnvelope model spec).card ≤
      1 + (1 + (((2 + (doublingEnvelope model spec).card) + 2) +
        (genericEnvelope model spec.field).card)) := by
    unfold additionBranchEnvelope caseMaximum
    refine (max_card_le_add _ _).trans (Nat.add_le_add le_rfl ?_)
    refine (max_card_le_add _ _).trans (Nat.add_le_add le_rfl ?_)
    refine (max_card_le_add _ _).trans (Nat.add_le_add ?_ le_rfl)
    refine (max_card_le_add _ _).trans (Nat.add_le_add ?_ le_rfl)
    exact max_card_le_add _ _
  unfold additionEnvelope
  rw [Multiset.card_add]
  change 5 + (additionBranchEnvelope model spec).card ≤ _
  omega

/-- Every actual complete-addition trace satisfies the same original numerical ceiling. -/
lemma addInto_eventCount_le (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx (PointShape width))
    (path : (addInto spec left right output).Path) :
    ((addInto spec left right output).eventTrace path).length ≤ 124 * width + 322 :=
  (Multiset.card_le_card (addInto_pool_le spec left right output path)).trans
    (additionEnvelope_card_le model spec)

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

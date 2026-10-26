/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation
import all QuantumAlg.Core.Base.Gate.Effect.BasisSlice
import all QuantumAlg.Core.Base.State.Density.Vector
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The same source observation on an unnormalized coherent component

A bounded source vector keeps its original squared norm as probability
mass. Fixing the actual physical input ket gives the same compressed event
weight and complete stage execution, including every original record and
measured Path. No projection is renormalized and no input is prepared here.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Adjoining the original physical ket leaves the source component's norm unchanged. -/
lemma window_source_ket_vector_bounded {R Reference : Register} (label : R.Index)
    (source : HilbertVector Reference) (bounded : ‖source‖ ≤ 1) :
    ‖HilbertVector.prodTensor (NormalizedVector.ket (R := R) label).vec source‖ ≤ 1 := by
  rw [HilbertVector.norm_prodTensor, (NormalizedVector.ket (R := R) label).norm_eq_one, one_mul]
  exact bounded

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

/-- The exact good-component observation retains its original subnormalized mass. -/
lemma window_source_vector_basisSlice_storeWeight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (source : HilbertVector Reference) (bounded : ‖source‖ ≤ 1)
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    (Effect.basisSliceEffect
      (Stage.observation environment stages (fun record => effects record.1) original)
      label).weight (DensityOperator.ofSubnormalizedVector source bounded) =
      Stage.storeWeight environment stages
        (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
          (ctx.register.prod Reference) decision original
          (DensityOperator.ofSubnormalizedVector
            (HilbertVector.prodTensor (NormalizedVector.ket (R := ctx.register) label).vec source)
            (window_source_ket_vector_bounded label source bounded))) effects := by
  let observed := Stage.observation environment stages (History := History)
    (fun record => effects record.1)
  let density : DensityOperator (ctx.register.prod Reference) :=
    DensityOperator.ofSubnormalizedVector
    (HilbertVector.prodTensor (NormalizedVector.ket (R := ctx.register) label).vec source)
    (window_source_ket_vector_bounded label source bounded)
  have factor (left right : ctx.register.Index) (refLeft refRight : Reference.Index) :
      density.matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket (R := ctx.register) label left *
          density.matrix (label, refLeft) (label, refRight) *
            star (NormalizedVector.ket (R := ctx.register) label right) := by
    simp only [density, DensityOperator.ofSubnormalizedVector_matrix,
      HilbertVector.prodTensor_apply, NormalizedVector.ket_apply]
    by_cases sameLeft : left = label <;> by_cases sameRight : right = label <;>
      simp [sameLeft, sameRight]
  have sliced : density.basisSlice label =
      DensityOperator.ofSubnormalizedVector source bounded := by
    apply DensityOperator.ext
    ext left right
    simp only [density, DensityOperator.basisSlice_matrix,
      DensityOperator.ofSubnormalizedVector_matrix, HilbertVector.prodTensor_apply,
      NormalizedVector.ket_apply, if_true, one_mul]
  have compressed := Effect.weight_basisSlice_of_factor (observed original)
    density label factor
  have sameSource := congrArg
    (fun state : DensityOperator Reference =>
      (Effect.basisSliceEffect (observed original) label).weight state) sliced
  calc
    _ = (observed original).weight density := sameSource.symm.trans compressed.symm
    _ = (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
        (ctx.register.prod Reference) decision original density).effectWeight observed :=
      (ExecutionState.effectWeight_ofValue_decision decision original density observed).symm
    _ = _ := (Stage.window_sourceSequence_storeWeight environment stages
      (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
        (ctx.register.prod Reference) decision original density) effects).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

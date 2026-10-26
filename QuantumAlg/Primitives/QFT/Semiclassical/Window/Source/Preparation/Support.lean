/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Vector
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Program
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Complete mixed-state preparation on the internally established zero subspace

The vector identity determines both density indices on the full original
physical, mathematical-source and external-reference carrier. Positivity
annihilates unsupported rows and columns. No independence or purity premise
is imposed on the surviving saved data, and no actual execution is replaced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

/-- The actual bank and the not-yet-prepared selected mathematical block are zero. -/
def doubleZero (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (basis : (ctx.register.prod (S.prod Reference)).Index) : Prop :=
  (bankCoordinates ports.wires ports.qubits basis.1).1 = Partner.zeroBits active ∧
    (partition basis.2.1).1 = 0

/-- Exact complete density equality, including every off-diagonal saved/reference entry. -/
lemma window_source_prepared_feed_density (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (state : DensityOperator (ctx.register.prod (S.prod Reference)))
    (supported : ∀ basis, ¬doubleZero ports partition Reference basis →
      state.matrix basis basis = 0) :
    DensityOperator.applyUnitary
        (selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference)
        (DensityOperator.applyUnitary (referencePreparation (ctx := ctx) partition Reference)
          state) =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor ((preparation active ports).matrix environment)
          (1 : UnitaryOperator (S.prod Reference)))
        state := by
  rw [← DensityOperator.applyUnitary_mul]
  apply DensityOperator.ext
  apply DensityOperator.conjugation_eq_on_basis_support state
    (doubleZero ports partition Reference) _ _ supported
  intro basis allowed row
  have columns := window_source_prepared_feed_column ports partition environment Reference
    basis allowed.1 allowed.2
  rw [← UnitaryOperator.mul_applyVec] at columns
  have entry := congrArg
    (fun vector : HilbertVector (ctx.register.prod (S.prod Reference)) => vector row) columns
  simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    preparationOperator] using entry

/-- Every complete classical record retains the same exact mixed-state preparation law. -/
lemma window_source_prepared_feed_state
    {Record : Type} [Fintype Record] (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (state : ExecutionState Record (ctx.register.prod (S.prod Reference)))
    (supported : ∀ record basis, ¬doubleZero ports partition Reference basis →
      (state.block record).matrix basis basis = 0) :
    ExecutionState.applyUnitary
        (state.applyUnitary (fun _ => referencePreparation (ctx := ctx) partition Reference))
        (fun _ =>
          selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference) =
      state.applyUnitary (fun _ =>
        UnitaryOperator.prodTensor ((preparation active ports).matrix environment)
          (1 : UnitaryOperator (S.prod Reference))) := by
  apply ExecutionState.ext
  intro record
  simp only [ExecutionState.applyUnitary_block]
  exact window_source_prepared_feed_density ports partition environment Reference
    (state.block record) (supported record)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Vector

/-!
# Consuming one source block retains zero and saved support

The mathematical exchange places the real zero bank in the consumed source
coordinates. Its saved source and external-reference coordinates are exactly
unchanged. These complete density identities require no purity, independence
or arithmetic premise, and do not execute a physical permutation.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

private lemma permutation_density_entry {R : Register} (permutation : Equiv.Perm R.Index)
    (state : DensityOperator R) (row column : R.Index) :
    (DensityOperator.applyUnitary (UnitaryOperator.ofPerm permutation) state).matrix row column =
      state.matrix (permutation row) (permutation column) := by
  classical
  change (permutation.permMatrix Complex * state.matrix *
    (permutation.permMatrix Complex).conjTranspose) row column = _
  rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- The selected exchange has its literal full matrix on both density coordinates. -/
lemma window_selectedSourceFeed_density_entry (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (state : DensityOperator (ctx.register.prod (S.prod Reference)))
    (row column : (ctx.register.prod (S.prod Reference)).Index) :
    (DensityOperator.applyUnitary (selectedFeedOperator ports partition Reference) state).matrix
        row column =
      state.matrix (selectedFeedBasis ports partition Reference row)
        (selectedFeedBasis ports partition Reference column) :=
  permutation_density_entry (selectedFeedEquiv ports partition Reference) state row column

/-- The actual internally zero bank makes the consumed mathematical source block zero. -/
lemma window_selectedSourceFeed_zero_support (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (state : DensityOperator (ctx.register.prod (S.prod Reference)))
    (supported : ∀ basis,
      (bankCoordinates ports.wires ports.qubits basis.1).1 ≠ Partner.zeroBits active →
        state.matrix basis basis = 0)
    (row : (ctx.register.prod (S.prod Reference)).Index)
    (absent : (partition row.2.1).1 ≠ 0) :
    (DensityOperator.applyUnitary (selectedFeedOperator ports partition Reference) state).matrix
      row row = 0 := by
  rw [window_selectedSourceFeed_density_entry]
  apply supported
  intro zero
  apply absent
  have actual : (bankCoordinates ports.wires ports.qubits
      (selectedFeedBasis ports partition Reference row).1).1 =
      (binaryEquiv active).symm (partition row.2.1).1 :=
    congrArg Prod.fst ((bankCoordinates ports.wires ports.qubits).apply_symm_apply _)
  have same := congrArg (binaryEquiv active) (actual.symm.trans zero)
  exact ((binaryEquiv active).apply_symm_apply _).symm.trans
    (same.trans (window_source_binary_zero active))

/-- Every established saved-source/reference support condition survives the same exchange. -/
lemma window_selectedSourceFeed_saved_support (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (state : DensityOperator (ctx.register.prod (S.prod Reference)))
    (allowed : (Rest.prod Reference).Index → Prop)
    (supported : ∀ basis, ¬allowed ((partition basis.2.1).2, basis.2.2) →
      state.matrix basis basis = 0)
    (row : (ctx.register.prod (S.prod Reference)).Index)
    (absent : ¬allowed ((partition row.2.1).2, row.2.2)) :
    (DensityOperator.applyUnitary (selectedFeedOperator ports partition Reference) state).matrix
      row row = 0 := by
  rw [window_selectedSourceFeed_density_entry]
  apply supported
  have saved := window_selectedSourceFeed_saved ports partition Reference row
  rw [saved.1, saved.2]
  exact absent

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection
import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# The current source feed retains the entire remaining source

Regrouping the mathematical observation coordinates exhibits the selected
feed as a local permutation tensored with identity on every saved source
and external-reference coordinate. This is an exact operator identity; no
permutation circuit, physical allocation or resource assertion is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

/-- Put the physical register and current source block beside all saved source/reference data. -/
def feedCoordinates (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (Reference : Register) :
    (ctx.register.prod (S.prod Reference)).Index ≃
      ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference)).Index where
  toFun row := ((row.1, (partition row.2.1).1), ((partition row.2.1).2, row.2.2))
  invFun row := (row.1.1, (partition.symm (row.1.2, row.2.1), row.2.2))
  left_inv row := by simp only [Equiv.symm_apply_apply, Prod.eta]
  right_inv row := by simp only [Equiv.apply_symm_apply, Prod.eta]

private def exchangeBasis (ports : Ports ctx totalBits active)
    (row : (ctx.register.prod (Qubits active)).Index) :
    (ctx.register.prod (Qubits active)).Index :=
  ((bankCoordinates ports.wires ports.qubits).symm
    ((binaryEquiv active).symm row.2,
      (bankCoordinates ports.wires ports.qubits row.1).2),
    binaryEquiv active (bankCoordinates ports.wires ports.qubits row.1).1)

private lemma exchange_involutive (ports : Ports ctx totalBits active) :
    Function.Involutive (exchangeBasis ports) := by
  rintro ⟨physical, source⟩
  simp only [exchangeBasis, Equiv.apply_symm_apply, Equiv.symm_apply_apply, Prod.eta]

private def exchangeEquiv (ports : Ports ctx totalBits active) :
    Equiv.Perm (ctx.register.prod (Qubits active)).Index :=
  (exchange_involutive ports).toPerm (exchangeBasis ports)

/-- The feed changes only the local physical/current-block coordinate in this exact grouping. -/
lemma window_source_feed_coordinates (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (row : (ctx.register.prod (S.prod Reference)).Index) :
    feedCoordinates (ctx := ctx) partition Reference
        (selectedFeedBasis ports partition Reference row) =
      (exchangeEquiv ports (feedCoordinates (ctx := ctx) partition Reference row).1,
        (feedCoordinates (ctx := ctx) partition Reference row).2) := by
  simp only [feedCoordinates, Equiv.coe_fn_mk, selectedFeedBasis, exchangeEquiv,
    Function.Involutive.coe_toPerm, exchangeBasis, Equiv.apply_symm_apply]

/-- The same selected feed is a local permutation and literal identity on all remaining data. -/
lemma window_source_feed_local_tensor (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register) :
    selectedFeedOperator ports partition Reference =
      UnitaryOperator.reindex (feedCoordinates (ctx := ctx) partition Reference).symm
        (UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (exchangeEquiv ports))
          (1 : UnitaryOperator (Rest.prod Reference))) := by
  apply Subtype.ext
  ext row column
  let coordinates := feedCoordinates (ctx := ctx) partition Reference
  have same : selectedFeedBasis ports partition Reference row = column ↔
      exchangeEquiv ports (coordinates row).1 = (coordinates column).1 ∧
        (coordinates row).2 = (coordinates column).2 := by
    constructor
    · intro equal
      have paired := congrArg coordinates equal
      rw [window_source_feed_coordinates] at paired
      have localEq := congrArg (fun value :
        ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference)).Index => value.1) paired
      have savedEq := congrArg (fun value :
        ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference)).Index => value.2) paired
      exact ⟨localEq, savedEq⟩
    · rintro ⟨localSame, savedSame⟩
      apply coordinates.injective
      rw [window_source_feed_coordinates]
      exact Prod.ext localSame savedSame
  change UnitaryOperator.ofPerm (selectedFeedEquiv ports partition Reference) row column =
    UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (exchangeEquiv ports))
      (1 : UnitaryOperator (Rest.prod Reference)) (coordinates row) (coordinates column)
  rw [UnitaryOperator.ofPerm_entry, UnitaryOperator.unitaryOperator_prodTensor_apply,
    UnitaryOperator.ofPerm_entry]
  change (if selectedFeedBasis ports partition Reference row = column then (1 : Complex)
      else 0) =
    (if exchangeEquiv ports (coordinates row).1 = (coordinates column).1 then 1 else 0) *
      (if (coordinates row).2 = (coordinates column).2 then 1 else 0)
  by_cases localSame : exchangeEquiv ports (coordinates row).1 = (coordinates column).1
  · by_cases savedSame : (coordinates row).2 = (coordinates column).2
    · simp only [if_pos localSame, if_pos savedSame,
        if_pos (same.mpr ⟨localSame, savedSame⟩), one_mul]
    · simp only [if_pos localSame, if_neg savedSame,
        if_neg (fun equal => savedSame (same.mp equal).2), one_mul]
  · simp only [if_neg localSame, zero_mul,
      if_neg (fun equal => localSame (same.mp equal).1)]

/-- A source observation may prepare arbitrary saved coordinates beside the current feed. -/
def savedPreparation (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (Reference : Register) (operator : UnitaryOperator (Rest.prod Reference)) :
    UnitaryOperator (ctx.register.prod (S.prod Reference)) :=
  UnitaryOperator.reindex (feedCoordinates (ctx := ctx) partition Reference).symm
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (ctx.register.prod (Qubits active)))
      operator)

/-- The current mathematical feed commutes with any preparation on the full saved coordinates. -/
lemma window_source_feed_saved_commute (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (operator : UnitaryOperator (Rest.prod Reference)) :
    selectedFeedOperator ports partition Reference *
        savedPreparation (ctx := ctx) partition Reference operator =
      savedPreparation (ctx := ctx) partition Reference operator *
        selectedFeedOperator ports partition Reference := by
  rw [window_source_feed_local_tensor]
  unfold savedPreparation
  rw [← UnitaryOperator.unitaryOperator_reindex_mul,
    ← UnitaryOperator.unitaryOperator_reindex_mul]
  congr 1
  apply Subtype.ext
  have localFactor :
      (UnitaryOperator.prodTensor (UnitaryOperator.ofPerm (exchangeEquiv ports))
        (1 : UnitaryOperator (Rest.prod Reference)) :
          HilbertOperator ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference))) =
      Execution.Instrument.referenceLift (Rest.prod Reference)
        (UnitaryOperator.ofPerm (exchangeEquiv ports) :
          HilbertOperator (ctx.register.prod (Qubits active))) := by
    ext row column
    rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
    rfl
  have savedFactor :
      (UnitaryOperator.prodTensor (1 : UnitaryOperator (ctx.register.prod (Qubits active)))
        operator :
          HilbertOperator ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference))) =
      Execution.Instrument.referenceAction (ctx.register.prod (Qubits active))
        (operator : HilbertOperator (Rest.prod Reference)) := by
    ext row column
    rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
    rfl
  change (_ : HilbertOperator
    ((ctx.register.prod (Qubits active)).prod (Rest.prod Reference))) * _ = _ * _
  rw [localFactor, savedFactor]
  exact Execution.Instrument.reference_matrix_commute _ _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

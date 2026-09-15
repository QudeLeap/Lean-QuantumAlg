/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Execution.Laws
import all QuantumAlg.Algorithms.QPE.Preparation
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Execution.Owned.Borrowed.Pure
import all QuantumAlg.Core.Execution.Owned.Borrowed.Positions
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Selection
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Exact restoration of the supplied QPE eigenstate and its reference

The promised local eigenstate forces its joint support with every external
reference. The exact coherent QPE action changes only the owned phase factor
on that support, and the actual local unitary preserves the reference
marginal. Together these facts restore the entire borrowed joint state.

Fresh preparation and classical allocations preserve all borrowed blocks.
The actual Z measurements touch only owned phase wires, and the closed
packing operation writes only retained classical storage. No stronger
product-state premise is imposed on the caller's joint input.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

private instance pre_borrowedSubsingleton (t n : Nat) :
    Subsingleton (pre t n).borrowedClassicalShape.Value where
  allEq left right := by
    change CShape.Value .unit at left right
    cases left
    cases right
    rfl

private instance prepared_borrowedSubsingleton (t n : Nat) :
    Subsingleton (preparedContext t n).borrowedClassicalShape.Value := by
  change Subsingleton (pre t n).borrowedClassicalShape.Value
  infer_instance

private instance post_borrowedSubsingleton (t n : Nat) :
    Subsingleton (post t n).borrowedClassicalShape.Value := by
  rw [(allocationCode t n).borrowedClassicalShape_preserved]
  infer_instance

theorem preparationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference H) :
    (preparationCode t n).BorrowedRestored Reference state
      ((preparationCode t n).execute Reference state) :=
  Circuit.borrowedRestored_prepare state ⟨0⟩ (phaseRuntimeLayout t)
    (preparationFresh t n) (preparationDisjoint t n) (inputPreparation t)

/-- The promised source input is sufficient for joint restoration by the actual QPE unitary. -/
theorem nativeProgram_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference H)
    (initialPure : state.quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (qpeInput P t)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm) :
    (Circuit.unitary (nativeProgram P t) (nativeProgram_placement P t)).BorrowedRestored
      Reference state
      ((Circuit.unitary (nativeProgram P t) (nativeProgram_placement P t)).execute
        Reference state) := by
  let : Subsingleton (OwnedBorrowedQubits.context t n).borrowedClassicalShape.Value :=
    prepared_borrowedSubsingleton t n
  let phase := (qpeReadoutCircuit t).applyNormalized (phaseState t P.phase)
  have finalPure :
      ((Circuit.unitary (nativeProgram P t) (nativeProgram_placement P t)).execute
        Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (phase.tensor P.eigenstate)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm := by
    rw [Circuit.unitary_localDensity, initialPure, nativeProgram_input]
    change (DensityOperator.ofPure
      ((qpeCircuit t P.unitary).applyNormalized (qpeInput P t))).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm = _
    rw [qpeCircuit_applyNormalized_input]
  change observeBorrowed Reference _ = observeBorrowed Reference state
  exact OwnedBorrowedQubits.observeBorrowed_pureTensor_eq t n state _
    (NormalizedVector.ket (R := Qubits t) 0) phase P.eigenstate initialPure finalPure
    (Circuit.unitary_reference_entry (nativeProgram P t) (nativeProgram_placement P t) state)

theorem allocationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference H) :
    (allocationCode t n).BorrowedRestored Reference state
      ((allocationCode t n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain ⟨2⟩ (.bits t) (resultFresh t n) state)
    (MeasurementCells.allocate_borrowedRestored (resultContext t n) 2 t _)

theorem beforeMeasurement_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference H)
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    (beforeMeasurement P t).BorrowedRestored Reference state
      ((beforeMeasurement P t).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (preparationCode_borrowedRestored t n state)
    (Circuit.borrowedRestored_seq _ _ _
      (nativeProgram_borrowedRestored P t _ (preparationCode_localDensity P t state promised))
      (allocationCode_borrowedRestored t n _))

private theorem phaseWire_not_borrowed (t n : Nat) (index : Fin t) :
    phaseWire t n index ∉ (post t n).borrowedSelection := by
  rw [RuntimeCtx.mem_borrowedSelection, phaseWire, MeasurementCells.wireEquiv_preserved,
    (allocationCode t n).borrowedQuantumWires_preserved]
  change (preparedContext t n).quantumLayout.wire
    (preparedWire t n (Fin.castAdd n index)) ∉ (preparedContext t n).borrowedQuantumWires
  rw [← RuntimeCtx.mem_borrowedSelection]
  exact Finset.mem_compl.mp
    ((OwnedBorrowedQubits.owned_position_iff t n (Fin.castAdd n index)).mpr index.isLt)

private theorem readouts_not_borrowed (t n : Nat) :
    ∀ item ∈ readouts t n, item.wire ∉ (post t n).borrowedSelection := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_not_borrowed t n index

theorem readoutCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (post t n) Reference H) :
    (readoutCode t n).BorrowedRestored Reference state
      ((readoutCode t n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_measurementSequence_complement
      (readouts t n) (readouts_not_borrowed t n) state)
    (Circuit.borrowedRestored_classical (packing t n) _)

/-- Every promised execution restores its complete original borrowed quantum-reference state. -/
theorem code_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference H)
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    (code P t).BorrowedRestored Reference state ((code P t).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (beforeMeasurement_borrowedRestored P t state promised)
    (readoutCode_borrowedRestored t n _)

end

end QuantumAlg.QuantumPhaseEstimation

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
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

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

local instance {α : Type} : DecidableEq α := Classical.decEq α

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

lemma preparationCode_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (preparationCode n t).BorrowedRestored Reference state
      ((preparationCode n t).execute (sourceEnvironment P.unitary) Reference state) :=
  Circuit.borrowedRestored_prepareZero (environment := sourceEnvironment P.unitary) state ⟨0⟩
    (phaseRuntimeLayout t)
    (preparationFresh t n) (preparationDisjoint t n)

/-- The promised source input is sufficient for joint restoration by the actual QPE unitary. -/
lemma nativeProgram_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (initialPure : state.quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (qpeInput P t)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm) :
    (Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty)
      (nativeProgram n t)).BorrowedRestored
      Reference state
      ((Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
        (classicalOracles := .empty)
      (nativeProgram n t)).execute (sourceEnvironment P.unitary) Reference state) := by
  let : Subsingleton (OwnedBorrowedQubits.context t n).borrowedClassicalShape.Value :=
    prepared_borrowedSubsingleton t n
  let phase := (invQFT t).apply (phaseState t P.phase)
  have finalPure :
      ((Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
        (classicalOracles := .empty)
      (nativeProgram n t)).execute (sourceEnvironment P.unitary) Reference
        state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (phase.tensor P.eigenstate)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm := by
    rw [Circuit.unitary_localDensity, initialPure]
    change DensityOperator.applyUnitary
      ((nativeProgram n t).matrix (UnitarySource.interpretation P.unitary true)) _ = _
    rw [nativeProgram_input]
    change (DensityOperator.ofPure
      (((Native.circuit t n).binaryMatrix (UnitarySource.interpretation P.unitary true)).apply
        (qpeInput P t))).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm = _
    rw [qpeCircuit_applyNormalized_input]
  change observeBorrowed Reference _ = observeBorrowed Reference state
  exact OwnedBorrowedQubits.observeBorrowed_pureTensor_eq t n state _
    (NormalizedVector.ket (R := Qubits t) 0) phase P.eigenstate initialPure finalPure
    (Circuit.unitary_reference_entry (environment := sourceEnvironment P.unitary) (nativeProgram
      n t) state)

lemma allocationCode_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (allocationCode n t).BorrowedRestored Reference state
      ((allocationCode n t).execute (sourceEnvironment P.unitary) Reference state) :=
  Circuit.borrowedRestored_seq (environment := sourceEnvironment P.unitary) (model := model n) _
    _ state
    (Circuit.borrowedRestored_retain (environment := sourceEnvironment P.unitary) (model :=
      model n) ⟨2⟩ (.bits t) (resultFresh t n) state)
    (MeasurementCells.allocate_borrowedRestored (environment := sourceEnvironment P.unitary)
      (model := model n) (resultContext t n) 2 t _)

lemma beforeMeasurement_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    (beforeMeasurement n t).BorrowedRestored Reference state
      ((beforeMeasurement n t).execute (sourceEnvironment P.unitary) Reference state) :=
  Circuit.borrowedRestored_seq (environment := sourceEnvironment P.unitary) (model := model n) _
    _ state
    (preparationCode_borrowedRestored P t state)
    (Circuit.borrowedRestored_seq (environment := sourceEnvironment P.unitary) (model := model
      n) _ _ _
      (nativeProgram_borrowedRestored P t _ (preparationCode_localDensity P t state promised))
      (allocationCode_borrowedRestored P t _))

private lemma phaseWire_not_borrowed (n t : Nat)
    (index : Fin t) :
    phaseWire t n index ∉ (post t n).borrowedSelection := by
  rw [RuntimeCtx.mem_borrowedSelection, phaseWire, MeasurementCells.wireEquiv_preserved,
    (allocationCode n t).borrowedQuantumWires_preserved]
  change (preparedContext t n).quantumLayout.wire
    (preparedWire t n (Fin.castAdd n index)) ∉ (preparedContext t n).borrowedQuantumWires
  rw [← RuntimeCtx.mem_borrowedSelection]
  exact Finset.mem_compl.mp
    ((OwnedBorrowedQubits.owned_position_iff t n (Fin.castAdd n index)).mpr index.isLt)

private lemma readouts_not_borrowed (n t : Nat) :
    ∀ item ∈ readouts t n, item.wire ∉ (post t n).borrowedSelection := by
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  exact phaseWire_not_borrowed n t index

lemma readoutCode_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (post t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (readoutCode n t).BorrowedRestored Reference state
      ((readoutCode n t).execute (sourceEnvironment P.unitary) Reference state) := by
  let : Subsingleton (post t n).borrowedClassicalShape.Value := by
    rw [(allocationCode n t).borrowedClassicalShape_preserved]
    exact prepared_borrowedSubsingleton t n
  exact Circuit.borrowedRestored_seq (environment := sourceEnvironment P.unitary) (model :=
    model n) _ _ state
    (Circuit.borrowedRestored_measurementSequence_complement (environment := sourceEnvironment
      P.unitary)
      (readouts t n) (readouts_not_borrowed n t) state)
    (Circuit.borrowedRestored_classical (environment := sourceEnvironment P.unitary) (model :=
      model n)
      (BitWord.application (packing t n)) _)

/-- Every promised execution restores its complete original borrowed quantum-reference state. -/
lemma code_borrowedRestored {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    (code n t).BorrowedRestored Reference state ((code n t).execute (sourceEnvironment
      P.unitary) Reference state) :=
  Circuit.borrowedRestored_seq (environment := sourceEnvironment P.unitary) (model := model n) _
    _ state
    (beforeMeasurement_borrowedRestored P t state promised)
    (readoutCode_borrowedRestored P t _)

end

end QuantumAlg.QuantumPhaseEstimation

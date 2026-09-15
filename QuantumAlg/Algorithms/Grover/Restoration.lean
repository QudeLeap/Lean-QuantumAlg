/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Grover preserves its entire borrowed input and external reference

The mandatory borrowed observation includes the actual unit input together
with every external-reference correlation. Actual preparation, the local
unitary, retained-cell allocation, measurement and classical packing preserve
that same observation, independently of whether an index is marked.

-/

namespace QuantumAlg.GroverSearch

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

open QuantumAlg.Execution

private instance pre_borrowedSubsingleton : Subsingleton pre.borrowedClassicalShape.Value where
  allEq left right := by
    change CShape.Value (.product .unit .unit) at left right
    cases left with
    | product leftHead leftTail =>
        cases leftHead
        cases leftTail
        cases right with
        | product rightHead rightTail =>
            cases rightHead
            cases rightTail
            rfl

private instance prepared_borrowedSubsingleton (n : Nat) :
    Subsingleton (preparedContext n).borrowedClassicalShape.Value := by
  change Subsingleton pre.borrowedClassicalShape.Value
  infer_instance

private instance post_borrowedSubsingleton (n k : Nat) :
    Subsingleton (post n k).borrowedClassicalShape.Value := by
  rw [(allocationCode n k).borrowedClassicalShape_preserved]
  infer_instance

private theorem post_noBorrowedQuantum (n k : Nat) : (post n k).borrowedQuantumWires = [] :=
  (allocationCode n k).borrowedQuantumWires_preserved.trans rfl

theorem preparationCode_borrowedRestored (n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (preparationCode n).BorrowedRestored Reference state
      ((preparationCode n).execute Reference state) :=
  Circuit.borrowedRestored_prepare_noBorrowedQuantum (by rfl) state ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (inputPreparation n)

theorem allocationCode_borrowedRestored (n k : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext (totalQubits n k)) Reference H) :
    (allocationCode n k).BorrowedRestored Reference state
      ((allocationCode n k).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain ⟨2⟩ (.bits n) (resultFresh n k) state)
    (MeasurementCells.allocate_borrowedRestored (resultContext n k) 2 n _)

theorem beforeMeasurement_borrowedRestored {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (beforeMeasurement marked k).BorrowedRestored Reference state
      ((beforeMeasurement marked k).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (preparationCode_borrowedRestored (totalQubits n k) state)
    (Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_unitary_noBorrowedQuantum (by rfl)
        (program marked k) (program_placement marked k) _)
      (allocationCode_borrowedRestored n k _))

theorem readoutCode_borrowedRestored (n k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (post n k) Reference H) :
    (readoutCode n k).BorrowedRestored Reference state
      ((readoutCode n k).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_measurementSequence_noBorrowedQuantum
      (post_noBorrowedQuantum n k) (readouts n k) state)
    (Circuit.borrowedRestored_classical (packing n k) _)

/-- Every real execution preserves the borrowed unit and its complete external reference. -/
theorem code_borrowedRestored {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (code marked k).BorrowedRestored Reference state ((code marked k).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (beforeMeasurement_borrowedRestored marked k state)
    (readoutCode_borrowedRestored n k _)

end

end QuantumAlg.GroverSearch

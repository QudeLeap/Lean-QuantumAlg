/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Walsh-Hadamard query readout restores its complete borrowed interface

The borrowed unit input has one possible value. The arbitrary external
reference remains part of its mandatory joint observation. Actual owned
preparation, the local unitary, retained-cell allocation, query-wire
measurement, and classical packing each preserve that same observation.
The proof does not depend on the oracle promise or an output-state promise.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

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

private instance post_borrowedSubsingleton (n : Nat) :
    Subsingleton (post n).borrowedClassicalShape.Value := by
  rw [(allocationCode n).borrowedClassicalShape_preserved]
  infer_instance

private theorem post_noBorrowedQuantum (n : Nat) : (post n).borrowedQuantumWires = [] :=
  (allocationCode n).borrowedQuantumWires_preserved.trans rfl

theorem preparationCode_borrowedRestored (n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (preparationCode n).BorrowedRestored Reference state
      ((preparationCode n).execute Reference state) :=
  Circuit.borrowedRestored_prepare_noBorrowedQuantum (by rfl) state ⟨1⟩ (runtimeLayout n)
    preparationFresh (preparationDisjoint n) (inputPreparation n)

theorem allocationCode_borrowedRestored (n : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext n) Reference H) :
    (allocationCode n).BorrowedRestored Reference state
      ((allocationCode n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain ⟨2⟩ (.bits n) (resultFresh n) state)
    (MeasurementCells.allocate_borrowedRestored (resultContext n) 2 n _)

theorem beforeMeasurement_borrowedRestored {n : Nat} (f : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (beforeMeasurement f).BorrowedRestored Reference state
      ((beforeMeasurement f).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (preparationCode_borrowedRestored n state)
    (Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_unitary_noBorrowedQuantum (by rfl)
        (program f) (program_placement f) _)
      (allocationCode_borrowedRestored n _))

theorem readoutCode_borrowedRestored (n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (post n) Reference H) :
    (readoutCode n).BorrowedRestored Reference state
      ((readoutCode n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_measurementSequence_noBorrowedQuantum
      (post_noBorrowedQuantum n) (readouts n) state)
    (Circuit.borrowedRestored_classical (packing n) _)

/-- Every real execution preserves the borrowed unit and its complete external reference. -/
theorem code_borrowedRestored {n : Nat} (f : WalshHadamard.Oracle n)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (code f).BorrowedRestored Reference state ((code f).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (beforeMeasurement_borrowedRestored f state)
    (readoutCode_borrowedRestored n _)

end

end QuantumAlg.WalshHadamard.Readout

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Execution
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Complete external-reference restoration in amplitude estimation

The runtime begins with no borrowed storage. Its arbitrary external
reference is preserved by actual basis preparation, the local source
unitary, result allocation, each phase measurement, and final packing.
The complete output keeps every prepared system and retained classical cell.

-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

private instance pre_borrowedSubsingleton : Subsingleton pre.borrowedClassicalShape.Value where
  allEq left right := by
    change CShape.Value .unit at left right
    cases left
    cases right
    rfl

private instance prepared_borrowedSubsingleton (t n : Nat) :
    Subsingleton (preparedContext t n).borrowedClassicalShape.Value := by
  change Subsingleton pre.borrowedClassicalShape.Value
  infer_instance

private instance post_borrowedSubsingleton (t n : Nat) :
    Subsingleton (post t n).borrowedClassicalShape.Value := by
  rw [(allocationCode t n).borrowedClassicalShape_preserved]
  infer_instance

private theorem post_noBorrowedQuantum (t n : Nat) : (post t n).borrowedQuantumWires = [] :=
  (allocationCode t n).borrowedQuantumWires_preserved.trans rfl

theorem preparationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (preparationCode t n).BorrowedRestored Reference state
      ((preparationCode t n).execute Reference state) :=
  Circuit.borrowedRestored_prepare_noBorrowedQuantum (by rfl) state ⟨0⟩ (runtimeLayout t n)
    preparationFresh (preparationDisjoint t n) (inputPreparation t n)

theorem allocationCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (preparedContext t n) Reference H) :
    (allocationCode t n).BorrowedRestored Reference state
      ((allocationCode t n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_retain ⟨1⟩ (.bits t) (resultFresh t n) state)
    (MeasurementCells.allocate_borrowedRestored (resultContext t n) 2 t _)

theorem beforeMeasurement_borrowedRestored {n : Nat}
    (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (beforeMeasurement E t).BorrowedRestored Reference state
      ((beforeMeasurement E t).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (preparationCode_borrowedRestored t n state)
    (Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_unitary_noBorrowedQuantum (by rfl)
        (nativeProgram E t) (nativeProgram_placement E t) _)
      (allocationCode_borrowedRestored t n _))

theorem readoutCode_borrowedRestored (t n : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (post t n) Reference H) :
    (readoutCode t n).BorrowedRestored Reference state
      ((readoutCode t n).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_measurementSequence_noBorrowedQuantum
      (post_noBorrowedQuantum t n) (readouts t n) state)
    (Circuit.borrowedRestored_classical (packing t n) _)

/-- Every real execution preserves its complete external reference. -/
theorem code_borrowedRestored {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (code E t).BorrowedRestored Reference state ((code E t).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (beforeMeasurement_borrowedRestored E t state)
    (readoutCode_borrowedRestored t n _)

end

end QuantumAlg.AmplitudeEstimation

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Measurement.Reference

/-!
# Complete Hadamard-test borrowed and reference restoration

The supplied input word is owned and may change. Actual local preparation,
unitary execution and the stored Z measurement preserve the complete external
reference. Every live system and the measured classical result remain in
Output [AJL06, qf2.tex:625-645; dW19, qcnotes.tex:6827].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

private instance pre_borrowedSubsingleton (width : Nat) :
    Subsingleton (pre width).borrowedClassicalShape.Value where
  allEq left right := by
    change CShape.Value .unit at left right
    cases left
    cases right
    rfl

private instance prepared_borrowedSubsingleton (width : Nat) :
    Subsingleton (prepared width).borrowedClassicalShape.Value := by
  change Subsingleton (pre width).borrowedClassicalShape.Value
  infer_instance

private instance post_borrowedSubsingleton (width : Nat) :
    Subsingleton (post width).borrowedClassicalShape.Value := by
  change Subsingleton (pre width).borrowedClassicalShape.Value
  infer_instance

/-- Actual preparation, supplied unitary access, and result allocation restore every reference. -/
theorem beforeMeasurement_borrowedRestored {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference H) :
    (beforeMeasurement unitary).BorrowedRestored Reference state
      ((beforeMeasurement unitary).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_prepare_noBorrowedQuantum
      (OwnedQubitPrefix.pre_noBorrowedQuantum 1 width) state ⟨0⟩
      (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
      (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width)
      (OwnedQubitPrefix.zeroPreparation 1))
    (Circuit.borrowedRestored_seq _ _ _
      (Circuit.borrowedRestored_unitary_noBorrowedQuantum
        (OwnedQubitPrefix.post_noBorrowedQuantum 1 width)
        (nativeProgram unitary) (nativeProgram_placement unitary) _)
      (Circuit.borrowedRestored_retain ⟨2⟩ (.finite 2) (resultFresh width) _))

/-- Complete borrowed restoration follows the real execution, independently of its input promise. -/
theorem code_borrowedRestored {width : Nat} (unitary : UnitaryOperator (Qubits width))
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre width) Reference H) :
    (code unitary).BorrowedRestored Reference state ((code unitary).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (beforeMeasurement_borrowedRestored unitary state)
    (Circuit.borrowedRestored_measurementSequence_noBorrowedQuantum
      (post_noBorrowedQuantum width) [readout width] _)

end

end QuantumAlg.HadamardTest

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Preparation.Borrowed.General
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

local instance {α : Type} : DecidableEq α := Classical.decEq α

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
lemma beforeMeasurement_borrowedRestored (width : Nat) (actual : (model width).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (beforeMeasurement width).BorrowedRestored Reference state
      ((beforeMeasurement width).execute actual Reference state) :=
  Circuit.borrowedRestored_seq (model := model width) actual _ _ state
    (Circuit.borrowedRestored_prepareZero actual state ⟨0⟩
      (OwnedQubitPrefix.prefixLayout 1).toQuantumLayout
      (OwnedQubitPrefix.prefix_fresh 1 width) (OwnedQubitPrefix.prefix_disjoint 1 width))
    (Circuit.borrowedRestored_seq (model := model width) actual _ _ _
      (Circuit.borrowedRestored_unitary_noBorrowedQuantum actual
        (OwnedQubitPrefix.post_noBorrowedQuantum 1 width)
        (nativeProgram width) _)
      (Circuit.borrowedRestored_retain (model := model width) actual
        ⟨2⟩ (.finite 2) (resultFresh width) _))

/-- Complete borrowed restoration follows the real execution, independently of its input promise. -/
lemma code_borrowedRestored (width : Nat) (actual : (model width).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (code width).BorrowedRestored Reference state ((code width).execute actual Reference state) :=
  Circuit.borrowedRestored_seq (model := model width) actual _ _ state
    (beforeMeasurement_borrowedRestored width actual state)
    (Circuit.borrowedRestored_measurementSequence_noBorrowedQuantum actual
      (post_noBorrowedQuantum width) [readout width] _)

end

end QuantumAlg.HadamardTest

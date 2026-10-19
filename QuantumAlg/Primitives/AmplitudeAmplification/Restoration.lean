/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Core.Execution.Preparation.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Restoration of the full reference by actual amplification

No runtime resource is borrowed initially. The charged local preparation
and the exact local unitary preserve every entry of the same external
reference, independently of the optional output-state promise.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

open QuantumAlg.Execution

private instance pre_borrowedSubsingleton : Subsingleton pre.borrowedClassicalShape.Value where
  allEq left right := by
    change CShape.Value .unit at left right
    cases left
    cases right
    rfl

lemma preparationCode_borrowedRestored (n : Nat) (k : Nat) (environment : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (preparationCode n k).BorrowedRestored Reference state
      ((preparationCode n k).execute environment Reference state) :=
  Circuit.borrowedRestored_prepareZero_noBorrowedQuantum
    rfl environment state ⟨0⟩ (runtimeLayout n k)
    preparationFresh (preparationDisjoint n k)

/-- Every actual complete run preserves the same external reference. -/
lemma code_borrowedRestored (n : Nat) (k : Nat) (environment : (model n).Environment)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    (code n k).BorrowedRestored Reference state
      ((code n k).execute environment Reference state) := by
  have unitaryRestores := Circuit.borrowedRestored_unitary_noBorrowed (environment := environment)
    (allowAllocation := true)
    (operations := .empty) (classicalOracles := .empty)
    (ctx := post n k) rfl rfl (nativeProgram n k)
    ((preparationCode n k).execute environment Reference state)
  exact Circuit.borrowedRestored_seq (model := model n)
    (environment := environment) (preparationCode n k)
    (.unitary (nativeProgram n k)) state (preparationCode_borrowedRestored n k environment state)
    unitaryRestores

end

end QuantumAlg.AmplitudeAmplification

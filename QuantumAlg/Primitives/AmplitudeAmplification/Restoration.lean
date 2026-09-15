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

theorem preparationCode_borrowedRestored (n k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (preparationCode n k).BorrowedRestored Reference state
      ((preparationCode n k).execute Reference state) :=
  Circuit.borrowedRestored_prepare_noBorrowedQuantum rfl state ⟨0⟩ (runtimeLayout n k)
    preparationFresh (preparationDisjoint n k) (inputPreparation n k)

/-- Every actual complete run preserves the same external reference. -/
theorem code_borrowedRestored {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State pre Reference H) :
    (code M k).BorrowedRestored Reference state ((code M k).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (preparationCode_borrowedRestored n k state)
    (Circuit.borrowedRestored_unitary_noBorrowed rfl rfl
      (nativeProgram M k) (nativeProgram_placement M k) _)

end

end QuantumAlg.AmplitudeAmplification

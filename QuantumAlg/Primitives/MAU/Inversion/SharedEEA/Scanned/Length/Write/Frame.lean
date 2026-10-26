/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Write.Original
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Schedule

/-!
# Native scanned length write on the complete original record and pool

The physical copy word is the original retained length field in the same
least-significant-first order. Its complete finite XOR therefore changes
exactly that field. The clean-pool native writer implements the original
dynamic region-size action under arbitrary retained Ctrl and arbitrary
original work, target, metadata and Iter values. No original selector
enumeration is executed by this new program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma xorConstantStep_source (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    Word.xorConstantStep (LengthCopy.target width field) mask state =
      (Word.xorConstantStep (LengthWrite.target width field) mask state.1, state.2) := by
  rw [Word.xorConstantStep_eq_indicesStep, Word.xorConstantStep_eq_indicesStep]
  generalize Word.constantOneIndices mask = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      change Word.xorConstantIndicesStep (LengthCopy.target width field) rest
          (((LengthWrite.target width field).bit bit).flip state.1, state.2) = _
      exact ih (((LengthWrite.target width field).bit bit).flip state.1, state.2)

/-- The actual full writer equals the original controlled dynamic length action. -/
lemma step_eq_source (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    step width field first capacity state =
      (if state.1.control then LengthSchedule.step width field first state.1 else state.1,
        state.2) := by
  rw [step_eq_original width field first capacity state prefixZero addressZero borrowZero
    sentinelFits]
  split
  · rw [xorConstantStep_source, LengthField.constant_step_eq]
    rfl
  · rfl

/-- The exact native ket endpoint includes every original field and the same entire pool. -/
lemma program_apply_source (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (program width field first capacity).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (if state.1.control then LengthSchedule.step width field first state.1 else state.1,
            state.2))) := by
  have actual := (program_realizes width field first capacity environment).apply_encoded_ket state
  rw [step_eq_source width field first capacity state prefixZero addressZero borrowZero
    sentinelFits] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

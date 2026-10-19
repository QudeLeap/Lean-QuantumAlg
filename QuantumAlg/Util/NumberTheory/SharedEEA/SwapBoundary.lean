/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Packing
import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division.Phase
import Mathlib.Data.Nat.Prime.Basic

/-!
# The actual quotient-boundary positions before and after extraction

The baseline source increments quotient length before its phase-2 swap
[LYL+26, sec_EEA/sub_regshare.tex:281-287], but phase 3 swaps before the
decrement [LYL+26, sec_EEA/sub_regshare.tex:288-296].
Moving the phase-2 increment after the swap
therefore requires adding one to its old-length position. The optimized
pseudocode moves that update but retains the earlier index
[LYL+26, sec_EEA/sub_opt.tex:52-59]. The smallest original prime input below
exhibits the resulting separator corruption.

These are exact physical packing and signed-instruction facts. They do
not assume that a native program already implements the corrected index,
and do not change the original positive-residue caller domain.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SwapBoundary

/-- Phase 2 writes the next quotient bit in the highest bit of the old remainder region. -/
def phase2Position (coefficientLength quotientLength : Nat) : Nat :=
  coefficientLength + quotientLength + 1

/-- Phase 3 reads the final existing quotient bit before its length decreases. -/
def phase3Position (coefficientLength quotientLength : Nat) : Nat :=
  coefficientLength + quotientLength

/-- The source's post-increment one-based phase-2 index becomes this old-length physical index. -/
lemma phase2_from_baseline (coefficientLength quotientLength : Nat) :
    (coefficientLength + (quotientLength + 1) + 1) - 1 =
      phase2Position coefficientLength quotientLength := by
  unfold phase2Position
  omega

/-- The corrected phase-2 index is the actual beginning of the old packed remainder. -/
lemma phase2_remainder_start (coefficientLength quotientLength : Nat) :
    phase2Position coefficientLength quotientLength = coefficientLength + 1 + quotientLength := by
  unfold phase2Position
  omega

/-- Every actual old remainder bit is located relative to that exact physical boundary. -/
lemma phase2_reads_old_remainder {coefficientWidth quotientWidth remainderWidth : Nat}
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth) :
    (WordPacking.packWork1 payload).getMsbD
        (phase2Position coefficientWidth quotientWidth) = payload.remainderBits.getMsbD 0 := by
  rw [phase2_remainder_start]
  exact WordPacking.packWork1_remainder_bit payload 0

/-- For a nonempty quotient, the phase-3 position is its final actual existing bit. -/
lemma phase3_last_quotient (coefficientLength quotientLength : Nat)
    (nonempty : 0 < quotientLength) :
    phase3Position coefficientLength quotientLength =
      coefficientLength + 1 + (quotientLength - 1) := by
  unfold phase3Position
  omega

/-- The optimized literal index is one position before the phase-2 write boundary. -/
lemma literal_phase2_is_previous (coefficientLength quotientLength : Nat) :
    phase3Position coefficientLength quotientLength + 1 =
      phase2Position coefficientLength quotientLength := rfl

/-- At the first extracted quotient bit, the uncorrected position is the prescribed separator. -/
lemma literal_first_reads_separator {coefficientWidth remainderWidth : Nat}
    (payload : WordPacking.Work1Payload coefficientWidth 0 remainderWidth) :
    (WordPacking.packWork1 payload).getMsbD (coefficientWidth + 0) = false :=
  WordPacking.packWork1_separator payload

/-- The counterexample lies in the original positive-residue domain at the smallest prime. -/
lemma smallest_initial_admissible :
    (IterationState.initial 2 (foldInput 2 1).2).Admissible :=
  folded_initial_admissible 2 1 (by decide) (by decide)

/-- The actual first division microstep on that original input is the equality branch. -/
lemma smallest_actual_microstep :
    let state := IterationState.initial 2 (foldInput 2 1).2
    Nat.Prime 2 ∧ state.coefficient = 1 ∧
      (DivisionProgress.current state 0).written = 0 ∧
      (DivisionProgress.current state 0).remainder = 2 ∧
      DivisionThreshold.threshold state 0 = 2 ∧
      (DivisionProgress.current state 1).written = 1 ∧
      (DivisionProgress.current state 1).quotientPrefix = 1 ∧
      (DivisionProgress.current state 1).remainder = 0 := by
  decide

/-- The actual signed subtraction selects equality and leaves zero remainder at p=2,x=1. -/
lemma smallest_signed_instruction :
    SignedDivision.corrected (2 : BitVec 3) (2 : BitVec 3) = (0 : BitVec 3) ∧
      (SignedDivision.extract (2 : BitVec 3) (2 : BitVec 3)).1 = false ∧
      (SignedDivision.extract (2 : BitVec 3) (2 : BitVec 3)).2 = (4 : BitVec 3) := by
  decide

/-- The complete optimized word differs from the next true packed payload. -/
lemma smallest_phase2_word_counterexample :
    let corrected := WordPacking.packWork1
      (⟨1, 0, 0⟩ : WordPacking.Work1Payload 1 0 3)
    let next := WordPacking.packWork1
      (⟨1, 1, 0⟩ : WordPacking.Work1Payload 1 1 2)
    corrected = (16 : BitVec 5) ∧
      (corrected ^^^ (8 : BitVec 5)) = (24 : BitVec 5) ∧
      (corrected ^^^ (4 : BitVec 5)) = next ∧
      next = (20 : BitVec 5) ∧ (corrected ^^^ (8 : BitVec 5)) ≠ next := by
  decide

/-- The concrete differing bits are exactly zero-based old-length positions one and two. -/
lemma smallest_positions :
    phase3Position 1 0 = 1 ∧ phase2Position 1 0 = 2 ∧
      (24 : BitVec 5).getMsbD 1 = true ∧ (20 : BitVec 5).getMsbD 1 = false ∧
      (24 : BitVec 5).getMsbD 2 = false ∧ (20 : BitVec 5).getMsbD 2 = true := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.SwapBoundary

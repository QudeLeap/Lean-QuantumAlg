/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.BlockLaws
import all QuantumAlg.Util.NumberTheory.SharedEEA.PhysicalWindow

/-!
# Complete Work2 replacement by the actual coefficient block

The executed coefficient arithmetic changes its left integer region and
retains the entire rotated fractional suffix
[LYL+26, sec_EEA/sub_regshare.tex:20,263-264,291-296]. Combining the actual
signed output with that exact suffix equation identifies the complete
physical Work2 word, not merely its arithmetic readout. The result is the
same finite `PhysicalWindow.replace` used in the proved packed coefficient
microstep, so subsequent packed-state refinement can reuse its full-word
reassembly and rotation laws without assuming that the fraction is zero.

These are equations about the existing native coefficient program. No
replacement circuit, allocation, or extra cleanup operation is introduced.
Phase and physical-fit premises remain local reachable-state obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientReplacement

noncomputable section

open ArithmeticWindowRegisters CoefficientWindowLaws
open NumberTheory.SharedEEA

private lemma replace_eq_of_suffix {wordWidth length : Nat}
    (before after : BitVec wordWidth) (fits : length ≤ wordWidth)
    (same : after.extractLsb' 0 (wordWidth - length) =
      before.extractLsb' 0 (wordWidth - length)) :
    after = PhysicalWindow.replace before (PhysicalWindow.read length after) fits := by
  calc
    after = PhysicalWindow.replace after (PhysicalWindow.read length after) fits :=
      (PhysicalWindow.replace_read after fits).symm
    _ = _ := by
      unfold PhysicalWindow.replace
      rw [same]

private lemma secondWord_suffix {width length : Nat} (fits : length ≤ width + 3)
    (before after : Registers width)
    (same :
      (CoefficientWindowOrientation.grouping
        (CoefficientWindowOrientation.coefficientWindow width length fits) after).2 =
      (CoefficientWindowOrientation.grouping
        (CoefficientWindowOrientation.coefficientWindow width length fits) before).2) :
    after.secondWord.extractLsb' 0 (width + 3 - length) =
      before.secondWord.extractLsb' 0 (width + 3 - length) := by
  let window := CoefficientWindowOrientation.coefficientWindow width length fits
  have suffix := congrArg (fun value : Complement window => value.2.1.2) same
  change (wordEquiv window after.secondWord).2.2 =
    (wordEquiv window before.secondWord).2.2 at suffix
  exact (wordEquiv_below window after.secondWord).symm.trans
    (suffix.trans (wordEquiv_below window before.secondWord))

/-- Every actual coefficient arithmetic mode updates whole Work2 by exact physical replacement. -/
lemma step_secondWord {width length : Nat} (fits : length ≤ width + 3)
    (operation : ArithmeticWindowProgram.Operation) (state : Registers width) :
    let window := CoefficientWindowOrientation.coefficientWindow width length fits
    (CoefficientWindowProgram.step window operation state).secondWord =
      PhysicalWindow.replace state.secondWord
        (targetWord window (CoefficientWindowProgram.step window operation state)) fits := by
  dsimp only
  let window := CoefficientWindowOrientation.coefficientWindow width length fits
  exact replace_eq_of_suffix _ _ fits
    (secondWord_suffix fits state (CoefficientWindowProgram.step window operation state)
      (step_complement window operation state))

/-- The complete source block writes the signed instruction's low word into original Work2. -/
lemma source_secondWord {width : Nat} (state : Registers width)
    (first : state.flags.first = true) (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    (ArithmeticBlocks.coefficientSource state).secondWord =
      PhysicalWindow.replace state.secondWord
        ((SignedCoefficient.addBit (targetWord window state) (sourceWord window state)
          state.flags.sign).setWidth window.length) fits := by
  dsimp only
  let window := CoefficientWindowOrientation.coefficientWindow width
    (state.coefficientLength.toNat + 1) fits
  have complete := replace_eq_of_suffix state.secondWord
    (ArithmeticBlocks.coefficientSource state).secondWord fits
    (secondWord_suffix fits state (ArithmeticBlocks.coefficientSource state)
      (CoefficientBlockLaws.source_complement state first second fits))
  have low := congrArg (fun word : BitVec (window.length + 1) => word.setWidth window.length)
    (CoefficientBlockLaws.source_signed_word state first second fits)
  change (signedTarget window (ArithmeticBlocks.coefficientSource state)).setWidth window.length =
    (SignedCoefficient.addBit (targetWord window state) (sourceWord window state)
      state.flags.sign).setWidth window.length at low
  rw [signedTarget, BitVec.setWidth_cons] at low
  change targetWord window (ArithmeticBlocks.coefficientSource state) = _ at low
  change (ArithmeticBlocks.coefficientSource state).secondWord =
    PhysicalWindow.replace state.secondWord
      (targetWord window (ArithmeticBlocks.coefficientSource state)) fits at complete
  exact complete.trans
    (congrArg (fun word => PhysicalWindow.replace state.secondWord word fits) low)

/-- The actual emitted program has that same whole-word result on internally prepared frames. -/
lemma native_secondWord (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false) (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    let window := CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits
    (ArithmeticBlocks.coefficientStep width state).secondWord =
      PhysicalWindow.replace state.secondWord
        ((SignedCoefficient.addBit (targetWord window state) (sourceWord window state)
          state.flags.sign).setWidth window.length) fits := by
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean]
  exact source_secondWord state first second fits

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientReplacement

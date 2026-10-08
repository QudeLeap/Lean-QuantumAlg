/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Semantics

/-!
# Compiled boundary cases for arithmetic modular exponentiation

These cases specialize the exact matrix theorem for the emitted gate list and
check the independent action on clean work. The supplied XOR target is not
assumed to be zero.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

private def five : Fin (2 ^ 3 + 1) := ⟨5, by decide⟩
private def six : Fin (2 ^ 3 + 1) := ⟨6, by decide⟩
private def oneAtThreeBits : Fin (2 ^ 3 + 1) := ⟨1, by decide⟩
private def oneAtZeroWidth : Fin (2 ^ 0 + 1) := ⟨1, by decide⟩

private theorem five_pos : 0 < five.val := by decide
private theorem six_pos : 0 < six.val := by decide
private theorem oneAtThreeBits_pos : 0 < oneAtThreeBits.val := by decide
private theorem oneAtZeroWidth_pos : 0 < oneAtZeroWidth.val := by decide

private def twoModFive : (ZMod 5)ˣ :=
  ZMod.unitOfCoprime 2 (by decide)

private def fiveModSix : (ZMod 6)ˣ :=
  ZMod.unitOfCoprime 5 (by decide)

/-- An odd modulus, nonzero exponent and nonzero target exercise the exact
compiled permutation: `6 XOR (2^2 mod 5) = 2`. -/
example :
    nativeArithmeticStep 2 3 five five_pos twoModFive
        ((0, 0), (⟨2, by decide⟩, ⟨6, by decide⟩)) =
      ((0, 0), (⟨2, by decide⟩, ⟨2, by decide⟩)) := by
  exact (nativeArithmeticStep_clean 2 3 five five_pos twoModFive
    ⟨2, by decide⟩ ⟨6, by decide⟩).trans (by decide)

/-- The even modulus remains admitted; `3 XOR (5 mod 6) = 6`. -/
example :
    nativeArithmeticStep 1 3 six six_pos fiveModSix
        ((0, 0), (⟨1, by decide⟩, ⟨3, by decide⟩)) =
      ((0, 0), (⟨1, by decide⟩, ⟨6, by decide⟩)) := by
  exact (nativeArithmeticStep_clean 1 3 six six_pos fiveModSix
    ⟨1, by decide⟩ ⟨3, by decide⟩).trans (by decide)

/-- Width zero and modulus one still produce a well-defined zero-work XOR. -/
example :
    nativeArithmeticStep 0 0 oneAtZeroWidth oneAtZeroWidth_pos (1 : (ZMod 1)ˣ)
        ((0, 0), (0, 0)) = ((0, 0), (0, 0)) := by
  exact (nativeArithmeticStep_clean 0 0 oneAtZeroWidth oneAtZeroWidth_pos
    (1 : (ZMod oneAtZeroWidth.val)ˣ) 0 0).trans (by decide)

/-- With no exponent wires, the power is one and an arbitrary target is XORed with one. -/
example :
    nativeArithmeticStep 0 3 six six_pos fiveModSix
        ((0, 0), (0, ⟨3, by decide⟩)) =
      ((0, 0), (0, ⟨2, by decide⟩)) := by
  exact (nativeArithmeticStep_clean 0 3 six six_pos fiveModSix
    0 ⟨3, by decide⟩).trans (by decide)

/-- Modulus one has zero canonical residue even when the word and target are nonzero. -/
example :
    nativeArithmeticStep 2 3 oneAtThreeBits oneAtThreeBits_pos
        (1 : (ZMod oneAtThreeBits.val)ˣ)
        ((0, 0), (⟨2, by decide⟩, ⟨7, by decide⟩)) =
      ((0, 0), (⟨2, by decide⟩, ⟨7, by decide⟩)) := by
  exact (nativeArithmeticStep_clean 2 3 oneAtThreeBits oneAtThreeBits_pos
    (1 : (ZMod oneAtThreeBits.val)ˣ) ⟨2, by decide⟩ ⟨7, by decide⟩).trans (by decide)

/-- The actual even-modulus gate list has exactly the independently specified
phase-sensitive operator, including for every dirty-work basis label. -/
example :
    (arithmeticNativeSourceProgram 1 3 six six_pos fiveModSix).matrix =
      arithmeticNativeSourceOperator 1 3 six six_pos fiveModSix :=
  arithmeticNativeSourceProgram_matrix 1 3 six six_pos fiveModSix

end

end QuantumAlg.MAU.Exponentiation.Gidney

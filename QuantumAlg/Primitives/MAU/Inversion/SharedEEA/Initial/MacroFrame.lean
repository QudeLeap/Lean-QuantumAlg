/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Initial.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.Trajectory
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.PackedStep

/-!
# Actual prepared-input preprocessing reaches the canonical macro frame

The real input fold retains its choice in Iter, then the native length
writer computes the size of that folded Work2 value. Every physical word,
length field, phase bit, Sign, and Ctrl consequently agrees with the
canonical initial Euclidean frame
[LYL+26, sec_EEA/sub_4phase.tex:107-117].

The unchanged Work1 is the literal `100,p`, and Work2 is the complete
folded residue with its existing zero padding. The length computation
uses the corrected fold-before-length order; it is not a supplied
input-dependent preparation. This equality joins the existing real
preprocessing program to the existing four-phase native trajectory.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InitialMacroFrame

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA

private lemma firstWord_value (modulus input : Nat)
    (valid : (IterationState.initial modulus input).Admissible) :
    (PackingBoundary.firstWord (IterationState.initial modulus input) modulus valid
      (IterationState.initial_balance modulus input)).toNat =
        4 * 2 ^ modulus.size + modulus := by
  have coefficientValue :
      (PackingBoundary.firstPayload (IterationState.initial modulus input) modulus valid
        (IterationState.initial_balance modulus input)).coefficientBits.reverse.toNat = 1 := by
    change (BitVec.ofNatLT 1 (Nat.lt_size_self 1)).reverse.toNat = 1
    decide
  have quotientValue :
      (PackingBoundary.firstPayload (IterationState.initial modulus input) modulus valid
        (IterationState.initial_balance modulus input)).quotientBits.toNat = 0 := rfl
  have remainderValue :
      (PackingBoundary.firstPayload (IterationState.initial modulus input) modulus valid
        (IterationState.initial_balance modulus input)).remainderBits.toNat = modulus := rfl
  have width : PackingBoundary.firstRemainderWidth
      (IterationState.initial modulus input) modulus = modulus.size + 1 := by
    dsimp only [PackingBoundary.firstRemainderWidth, IterationState.initial]
    rw [show Nat.size 1 = 1 by decide]
    omega
  rw [PackingBoundary.firstWord, BitVec.toNat_cast, WordPacking.packWork1,
    DivisionPackedStep.append_toNat, DivisionPackedStep.append_toNat,
    DivisionPackedStep.append_toNat, coefficientValue, quotientValue, remainderValue, width]
  change 2 * 2 ^ (0 + (modulus.size + 1)) +
      (0 * 2 ^ (modulus.size + 1) + modulus) = _
  rw [Nat.zero_add, Nat.zero_mul, Nat.zero_add, Nat.pow_succ]
  omega

private lemma secondWord_value (modulus input : Nat)
    (valid : (IterationState.initial modulus input).Admissible) :
    (PackingBoundary.secondWord (IterationState.initial modulus input) modulus valid
      (IterationState.initial_balance modulus input)).toNat = input := by
  let payload := DivisionCapacity.work2Payload (IterationState.initial modulus input) modulus
    valid (IterationState.initial_balance modulus input)
  have zero : payload.coefficientBits = 0#_ := by
    apply BitVec.eq_of_toNat_eq
    rfl
  have reversed : payload.coefficientBits.reverse = 0#_ :=
    BitVec.reverse_eq_zero_iff.mpr zero
  change ((WordPacking.packWork2 payload).cast _).toNat = input
  rw [BitVec.toNat_cast, WordPacking.packWork2, DivisionPackedStep.append_toNat, reversed]
  change 0 * 2 ^ input.size + input = input
  omega

/-- Real folding and real length computation supply every field of the initial macro frame. -/
lemma result_eq_frame (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    InitialFrame.result modulus input =
      MacroBoundary.frame
        (IterationState.initial modulus (foldInput modulus input.val).2) modulus
        (folded_initial_admissible modulus input.val positive bounded)
        (IterationState.initial_balance modulus (foldInput modulus input.val).2)
        (foldInput modulus input.val).1 := by
  have record := InitialFrame.result_record_value modulus input bounded
  have foldedValue := congrArg (fun pair : Bool × Nat => pair.2) record
  have retained := congrArg (fun pair : Bool × Nat => pair.1) record
  apply Registers.ext_fields
  · apply BitVec.eq_of_toNat_eq
    exact (congrArg BitVec.toNat (InitialFrame.result_firstWord modulus input)).trans
      ((InitialFrame.initial_firstWord modulus input).trans
        (firstWord_value modulus (foldInput modulus input.val).2
          (folded_initial_admissible modulus input.val positive bounded)).symm)
  · apply BitVec.eq_of_toNat_eq
    exact foldedValue.trans
      (secondWord_value modulus (foldInput modulus input.val).2
        (folded_initial_admissible modulus input.val positive bounded)).symm
  · rw [InitialFrame.result_eq]
    change BitVec.ofNat modulus.size.size 1 = BitVec.ofNat modulus.size.size (Nat.size 1)
    exact congrArg (BitVec.ofNat modulus.size.size) (by decide : 1 = Nat.size 1)
  · rw [InitialFrame.result_eq]
    rfl
  · exact InitialFrame.result_divisorLength modulus input bounded
  · rw [InitialFrame.result_eq]
    rfl
  · rw [InitialFrame.result_eq]
    rfl
  · rw [InitialFrame.result_eq]
    rfl
  · rw [InitialFrame.result_eq]
    rfl
  · exact retained
  · rw [InitialFrame.result_eq]
    rfl

/-- The same native preprocessing program reaches the canonical frame with exact ket amplitude. -/
lemma program_initial (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (InitialFrame.program modulus).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (InitialFrame.initial modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode
            (MacroBoundary.frame
              (IterationState.initial modulus (foldInput modulus input.val).2) modulus
              (folded_initial_admissible modulus input.val positive bounded)
              (IterationState.initial_balance modulus (foldInput modulus input.val).2)
              (foldInput modulus input.val).1))) := by
  rw [InitialFrame.program_initial, result_eq_frame modulus input positive bounded]

end

end QuantumAlg.MAU.Inversion.SharedEEA.InitialMacroFrame

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Coefficient

/-!
# Shift data path

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Cyclic-shift data-path atoms -/

/-- Cyclic qubit-shift scaffold for the RNSL17 `/2` operation on the `u`
register.  The source identifies the `/2` and `·2` round blocks as cyclic
qubit shifts; the arithmetic invariant that makes this a division-by-two
branch update is proved only at the later round-composition layer [RNSL17,
ECDLP.tex:425-465]. -/
def coeffWorkUDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.adjacentShiftLeftStep
    (coeffAdderUWord n counterWidth)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the `u` `/2` cyclic qubit-shift scaffold. -/
def coeffWorkUDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.adjacentShiftLeftProgram (QubitLayout.canonical _) .empty
    (coeffAdderUWord n counterWidth)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- The `u` `/2` cyclic qubit-shift circuit realizes its semantic step. -/
theorem coeffWorkUDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkUDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.adjacentShiftLeftWitness (QubitLayout.canonical _) .empty
    (coeffAdderUWord n counterWidth)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- Cyclic qubit-shift scaffold for the RNSL17 `/2` operation on the `v`
register [RNSL17, ECDLP.tex:425-465]. -/
def coeffWorkVDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.adjacentShiftLeftStep
    (coeffAdderVWord n counterWidth)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the `v` `/2` cyclic qubit-shift scaffold. -/
def coeffWorkVDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.adjacentShiftLeftProgram (QubitLayout.canonical _) .empty
    (coeffAdderVWord n counterWidth)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- The `v` `/2` cyclic qubit-shift circuit realizes its semantic step. -/
theorem coeffWorkVDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkVDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.adjacentShiftLeftWitness (QubitLayout.canonical _) .empty
    (coeffAdderVWord n counterWidth)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Inverse cyclic qubit-shift scaffold for the RNSL17 `·2` operation on the
`s` coefficient register.  This is the concrete reversible shift block; the
later round theorem must still discharge the coefficient-range/invariant facts
that connect it to arithmetic doubling [RNSL17, ECDLP.tex:425-465]. -/
def coeffWorkSMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.adjacentShiftRightStep
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the `s` `·2` cyclic qubit-shift scaffold. -/
def coeffWorkSMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.adjacentShiftRightProgram (QubitLayout.canonical _) .empty
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The `s` `·2` cyclic qubit-shift circuit realizes its semantic step. -/
theorem coeffWorkSMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkSMul2CyclicShiftProgram n counterWidth)
      (coeffWorkSMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.adjacentShiftRightWitness (QubitLayout.canonical _) .empty
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Inverse cyclic qubit-shift scaffold for the RNSL17 `·2` operation on the
`r` coefficient register [RNSL17, ECDLP.tex:425-465]. -/
def coeffWorkRMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.adjacentShiftRightStep
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the `r` `·2` cyclic qubit-shift scaffold. -/
def coeffWorkRMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.adjacentShiftRightProgram (QubitLayout.canonical _) .empty
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The `r` `·2` cyclic qubit-shift circuit realizes its semantic step. -/
theorem coeffWorkRMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkRMul2CyclicShiftProgram n counterWidth)
      (coeffWorkRMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.adjacentShiftRightWitness (QubitLayout.canonical _) .empty
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The unconditioned `u / 2` cyclic-shift atom preserves the active flag. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUDiv2CyclicShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  simpa [coeffWorkUDiv2CyclicShiftStep] using
    adjacentShiftLeftStep_get_observed_of_word_ne
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderActiveBit_coeffAdderUWordBit_wire_ne n counterWidth i))
      x

/-- The unconditioned `v / 2` cyclic-shift atom preserves the active flag. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVDiv2CyclicShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  simpa [coeffWorkVDiv2CyclicShiftStep] using
    adjacentShiftLeftStep_get_observed_of_word_ne
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i))
      x

/-- The unconditioned `s * 2` cyclic-shift atom preserves the active flag. -/
theorem coeffWorkSMul2CyclicShiftStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  simpa [coeffWorkSMul2CyclicShiftStep] using
    adjacentShiftRightStep_get_observed_of_word_ne
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne
            n counterWidth i))
      x

/-- The unconditioned `r * 2` cyclic-shift atom preserves the active flag. -/
theorem coeffWorkRMul2CyclicShiftStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  simpa [coeffWorkRMul2CyclicShiftStep] using
    adjacentShiftRightStep_get_observed_of_word_ne
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne
            n counterWidth i))
      x

/-- The unconditioned `u / 2` cyclic-shift atom exposes its exact
source-index permutation on `u` word bits. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_uBit_source
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit target).get
        (coeffWorkUDiv2CyclicShiftStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit
        (EncodedBit.Word.adjacentSwapIndexPerm n
          (List.ofFn fun i : Fin (n - 1) => i) target)).get x := by
  simpa [coeffWorkUDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_indexPerm
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      target x

/-- The unconditioned `v / 2` cyclic-shift atom exposes its exact
source-index permutation on `v` word bits. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_vBit_source
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit target).get
        (coeffWorkVDiv2CyclicShiftStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit
        (EncodedBit.Word.adjacentSwapIndexPerm n
          (List.ofFn fun i : Fin (n - 1) => i) target)).get x := by
  simpa [coeffWorkVDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_indexPerm
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      target x

/-- The unconditioned `s * 2` cyclic-shift atom exposes its exact inverse
source-index permutation on `s` coefficient word bits. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeffBit_source
    (n counterWidth : Nat) (target : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit target).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit
        ((EncodedBit.Word.adjacentSwapIndexPerm (n + 1)
          (List.ofFn fun i : Fin ((n + 1) - 1) => i)).symm target)).get
        x := by
  simpa [coeffWorkSMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_indexPerm
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      target x

/-- The unconditioned `r * 2` cyclic-shift atom exposes its exact inverse
source-index permutation on `r` coefficient word bits. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeffBit_source
    (n counterWidth : Nat) (target : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit target).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit
        ((EncodedBit.Word.adjacentSwapIndexPerm (n + 1)
          (List.ofFn fun i : Fin ((n + 1) - 1) => i)).symm target)).get
        x := by
  simpa [coeffWorkRMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_indexPerm
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      target x

/-- The unconditioned `u / 2` cyclic-shift atom reads each non-last target
`u` bit from the next higher source bit.  This is a bit-level cyclic-shift
endpoint, not yet the numeric division invariant. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_uBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderUWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderUWord tail.succ counterWidth).bit target.succ).get x := by
  simpa [coeffWorkUDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_castSucc
      (coeffAdderUWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne tail.succ counterWidth
          i j hij)
      target x

/-- The unconditioned `u / 2` cyclic-shift atom wraps the last target `u` bit
from source bit zero.  This is a bit-level cyclic-shift endpoint, not yet the
numeric division invariant. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_uBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderUWord tail.succ counterWidth).bit (Fin.last tail)).get
        (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderUWord tail.succ counterWidth).bit 0).get x := by
  simpa [coeffWorkUDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_last
      (coeffAdderUWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne tail.succ counterWidth
          i j hij)
      x

/-- The unconditioned `v / 2` cyclic-shift atom reads each non-last target
`v` bit from the next higher source bit.  This is a bit-level cyclic-shift
endpoint, not yet the numeric division invariant. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_vBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderVWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderVWord tail.succ counterWidth).bit target.succ).get x := by
  simpa [coeffWorkVDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_castSucc
      (coeffAdderVWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne tail.succ counterWidth
          i j hij)
      target x

/-- The unconditioned `v / 2` cyclic-shift atom wraps the last target `v` bit
from source bit zero.  This is a bit-level cyclic-shift endpoint, not yet the
numeric division invariant. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_vBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderVWord tail.succ counterWidth).bit (Fin.last tail)).get
        (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderVWord tail.succ counterWidth).bit 0).get x := by
  simpa [coeffWorkVDiv2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_last
      (coeffAdderVWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne tail.succ counterWidth
          i j hij)
      x

/-- The unconditioned `s * 2` cyclic-shift atom wraps target coefficient bit
zero from the last source coefficient bit.  This is a bit-level cyclic-shift
endpoint, not yet the numeric doubling invariant. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeffBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit 0).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit (Fin.last n)).get x := by
  simpa [coeffWorkSMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_zero
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      x

/-- The unconditioned `s * 2` cyclic-shift atom reads each successor target
coefficient bit from the previous lower source coefficient bit.  This is a
bit-level cyclic-shift endpoint, not yet the numeric doubling invariant. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeffBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit target.succ).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get
        x := by
  simpa [coeffWorkSMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_succ
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      target x

/-- The unconditioned `r * 2` cyclic-shift atom wraps target coefficient bit
zero from the last source coefficient bit.  This is a bit-level cyclic-shift
endpoint, not yet the numeric doubling invariant. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeffBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit 0).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit (Fin.last n)).get x := by
  simpa [coeffWorkRMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_zero
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      x

/-- The unconditioned `r * 2` cyclic-shift atom reads each successor target
coefficient bit from the previous lower source coefficient bit.  This is a
bit-level cyclic-shift endpoint, not yet the numeric doubling invariant. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeffBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit target.succ).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get
        x := by
  simpa [coeffWorkRMul2CyclicShiftStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_succ
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      target x

private theorem littleEndianWire_castSucc_eq_succ_littleEndianWire
    (n : Nat) (target : Fin n) :
    (WireAddress.littleEndianWire target).succ =
      WireAddress.littleEndianWire (Fin.castSucc target) := by
  ext
  simp [WireAddress.littleEndianWire, WireAddress.bitIndex]
  omega

private theorem littleEndianWire_succ_eq_castSucc_littleEndianWire
    (n : Nat) (target : Fin n) :
    Fin.castSucc (WireAddress.littleEndianWire target) =
      WireAddress.littleEndianWire target.succ := by
  ext
  simp [WireAddress.littleEndianWire, WireAddress.bitIndex]
  omega

private theorem littleEndianWire_last_eq_zero (n : Nat) :
    (0 : Fin (n + 1)) =
      WireAddress.littleEndianWire (Fin.last n) := by
  ext
  simp [WireAddress.littleEndianWire, WireAddress.bitIndex]

private theorem littleEndianWire_zero_eq_last (n : Nat) :
    Fin.last n =
      WireAddress.littleEndianWire (0 : Fin (n + 1)) := by
  ext
  simp [WireAddress.littleEndianWire, WireAddress.bitIndex]

/-- Value-bit form of the unconditioned `u / 2` cyclic-shift atom: each
non-last little-endian target bit reads the next higher source bit. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_uValueBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderUWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderUWord tail.succ counterWidth).bit target.succ).get x :=
  coeffWorkUDiv2CyclicShiftStep_get_uBit_next tail counterWidth target x

/-- Value-bit form of the unconditioned `u / 2` cyclic-shift atom: the last
little-endian target bit wraps from source bit zero. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_uValueBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderUWord tail.succ counterWidth).bit (Fin.last tail)).get
        (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderUWord tail.succ counterWidth).bit 0).get x :=
  coeffWorkUDiv2CyclicShiftStep_get_uBit_wrap tail counterWidth x

/-- Value-bit form of the unconditioned `v / 2` cyclic-shift atom: each
non-last little-endian target bit reads the next higher source bit. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_vValueBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderVWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderVWord tail.succ counterWidth).bit target.succ).get x :=
  coeffWorkVDiv2CyclicShiftStep_get_vBit_next tail counterWidth target x

/-- Value-bit form of the unconditioned `v / 2` cyclic-shift atom: the last
little-endian target bit wraps from source bit zero. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_vValueBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderVWord tail.succ counterWidth).bit (Fin.last tail)).get
        (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((coeffAdderVWord tail.succ counterWidth).bit 0).get x :=
  coeffWorkVDiv2CyclicShiftStep_get_vBit_wrap tail counterWidth x

/-- Value-bit form of the unconditioned `s * 2` cyclic-shift atom: each
successor little-endian target coefficient bit reads the previous lower source
coefficient bit. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeffValueBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit target.succ).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get
        x :=
  coeffWorkSMul2CyclicShiftStep_get_sCoeffBit_succ n counterWidth target x

/-- Value-bit form of the unconditioned `s * 2` cyclic-shift atom: target
coefficient bit zero wraps from the last source coefficient bit. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeffValueBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit 0).get
        (coeffWorkSMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit (Fin.last n)).get x :=
  coeffWorkSMul2CyclicShiftStep_get_sCoeffBit_zero n counterWidth x

/-- Value-bit form of the unconditioned `r * 2` cyclic-shift atom: each
successor little-endian target coefficient bit reads the previous lower source
coefficient bit. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeffValueBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit target.succ).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get
        x :=
  coeffWorkRMul2CyclicShiftStep_get_rCoeffBit_succ n counterWidth target x

/-- Value-bit form of the unconditioned `r * 2` cyclic-shift atom: target
coefficient bit zero wraps from the last source coefficient bit. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeffValueBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit 0).get
        (coeffWorkRMul2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit (Fin.last n)).get x :=
  coeffWorkRMul2CyclicShiftStep_get_rCoeffBit_zero n counterWidth x

/-- `testBit` form of the unconditioned `u / 2` cyclic-shift atom: each
non-last target bit reads the next higher source bit. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_u_testBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x).1.1.u).val.testBit
        (Fin.castSucc target).val =
      x.1.1.u.val.testBit target.succ.val := by
  have h :=
    coeffWorkUDiv2CyclicShiftStep_get_uValueBit_next tail counterWidth target x
  simpa [coeffAdderUWord_get_testBit] using h

/-- `testBit` form of the unconditioned `u / 2` cyclic-shift atom: the last
target bit wraps from source bit zero. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_u_testBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x).1.1.u).val.testBit
        (Fin.last tail).val =
      x.1.1.u.val.testBit (0 : Fin tail.succ).val := by
  have h := coeffWorkUDiv2CyclicShiftStep_get_uValueBit_wrap tail counterWidth x
  simpa [coeffAdderUWord_get_testBit] using h

/-- `testBit` form of the unconditioned `v / 2` cyclic-shift atom: each
non-last target bit reads the next higher source bit. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_v_testBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x).1.1.v).val.testBit
        (Fin.castSucc target).val =
      x.1.1.v.val.testBit target.succ.val := by
  have h :=
    coeffWorkVDiv2CyclicShiftStep_get_vValueBit_next tail counterWidth target x
  simpa [coeffAdderVWord_get_testBit] using h

/-- `testBit` form of the unconditioned `v / 2` cyclic-shift atom: the last
target bit wraps from source bit zero. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_v_testBit_wrap
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x).1.1.v).val.testBit
        (Fin.last tail).val =
      x.1.1.v.val.testBit (0 : Fin tail.succ).val := by
  have h := coeffWorkVDiv2CyclicShiftStep_get_vValueBit_wrap tail counterWidth x
  simpa [coeffAdderVWord_get_testBit] using h

/-- `testBit` form of the unconditioned `s * 2` cyclic-shift atom: each
successor target coefficient bit reads the previous lower source bit. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkSMul2CyclicShiftStep n counterWidth x).1.1.sCoeff).val.testBit
        target.succ.val =
      x.1.1.sCoeff.val.testBit (Fin.castSucc target).val := by
  have h :=
    coeffWorkSMul2CyclicShiftStep_get_sCoeffValueBit_succ n counterWidth
      target x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- `testBit` form of the unconditioned `s * 2` cyclic-shift atom: target bit
zero wraps from the last source bit. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkSMul2CyclicShiftStep n counterWidth x).1.1.sCoeff).val.testBit
        (0 : Fin (n + 1)).val =
      x.1.1.sCoeff.val.testBit (Fin.last n).val := by
  have h := coeffWorkSMul2CyclicShiftStep_get_sCoeffValueBit_zero n counterWidth
    x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- `testBit` form of the unconditioned `r * 2` cyclic-shift atom: each
successor target coefficient bit reads the previous lower source bit. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkRMul2CyclicShiftStep n counterWidth x).1.1.rCoeff).val.testBit
        target.succ.val =
      x.1.1.rCoeff.val.testBit (Fin.castSucc target).val := by
  have h :=
    coeffWorkRMul2CyclicShiftStep_get_rCoeffValueBit_succ n counterWidth
      target x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- `testBit` form of the unconditioned `r * 2` cyclic-shift atom: target bit
zero wraps from the last source bit. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkRMul2CyclicShiftStep n counterWidth x).1.1.rCoeff).val.testBit
        (0 : Fin (n + 1)).val =
      x.1.1.rCoeff.val.testBit (Fin.last n).val := by
  have h := coeffWorkRMul2CyclicShiftStep_get_rCoeffValueBit_zero n counterWidth
    x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- The unconditioned `u / 2` source shift preserves every `s` coefficient value
bit. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_sCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkUDiv2CyclicShiftStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  simpa [coeffWorkUDiv2CyclicShiftStep] using
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit)
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        coeffAdderUWordBit_coeffAdderSCoeffValueWordBit_wire_ne n counterWidth
          i bit)
      x

/-- The unconditioned `v / 2` source shift preserves every `r` coefficient value
bit. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_rCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkVDiv2CyclicShiftStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  simpa [coeffWorkVDiv2CyclicShiftStep] using
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit)
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        coeffAdderVWordBit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth
          i bit)
      x

/-- `testBit` form of the `u / 2` source-shift preservation endpoint for `s`. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_sCoeff_testBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkUDiv2CyclicShiftStep n counterWidth x).1.1.sCoeff).val.testBit
        bit.val =
      x.1.1.sCoeff.val.testBit bit.val := by
  have h :=
    coeffWorkUDiv2CyclicShiftStep_get_sCoeffValueBit n counterWidth bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- `testBit` form of the `v / 2` source-shift preservation endpoint for `r`. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_rCoeff_testBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkVDiv2CyclicShiftStep n counterWidth x).1.1.rCoeff).val.testBit
        bit.val =
      x.1.1.rCoeff.val.testBit bit.val := by
  have h :=
    coeffWorkVDiv2CyclicShiftStep_get_rCoeffValueBit n counterWidth bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- Arithmetic form of the unconditioned `u / 2` cyclic-shift atom on an even
source word: the cyclic wrap bit is false, so the concrete cyclic shift agrees
with natural halving. -/
theorem coeffWorkUDiv2CyclicShiftStep_get_u_wordHalf_of_lsb_false
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hlsb : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x).1.1.u =
      wordHalf tail.succ x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.lastCases ?last ?cast bit
  · have hwrap :=
      coeffWorkUDiv2CyclicShiftStep_get_u_testBit_wrap tail counterWidth x
    have hzero :
        x.1.1.u.val.testBit (0 : Fin tail.succ).val = false := by
      simpa using hlsb
    have hhigh :
        x.1.1.u.val.testBit ((Fin.last tail).val + 1) = false := by
      have hpow : 2 ^ tail.succ <= 2 ^ ((Fin.last tail).val + 1) := by
        simp
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.1.1.u.isLt hpow)
    rw [wordHalf_val, Nat.testBit_div_two, hwrap, hzero, hhigh]
  · intro target
    have hnext :=
      coeffWorkUDiv2CyclicShiftStep_get_u_testBit_next tail counterWidth
        target x
    rw [wordHalf_val, Nat.testBit_div_two]
    simpa using hnext

/-- Arithmetic form of the unconditioned `v / 2` cyclic-shift atom on an even
source word: the cyclic wrap bit is false, so the concrete cyclic shift agrees
with natural halving. -/
theorem coeffWorkVDiv2CyclicShiftStep_get_v_wordHalf_of_lsb_false
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hlsb : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x).1.1.v =
      wordHalf tail.succ x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.lastCases ?last ?cast bit
  · have hwrap :=
      coeffWorkVDiv2CyclicShiftStep_get_v_testBit_wrap tail counterWidth x
    have hzero :
        x.1.1.v.val.testBit (0 : Fin tail.succ).val = false := by
      simpa using hlsb
    have hhigh :
        x.1.1.v.val.testBit ((Fin.last tail).val + 1) = false := by
      have hpow : 2 ^ tail.succ <= 2 ^ ((Fin.last tail).val + 1) := by
        simp
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.1.1.v.isLt hpow)
    rw [wordHalf_val, Nat.testBit_div_two, hwrap, hzero, hhigh]
  · intro target
    have hnext :=
      coeffWorkVDiv2CyclicShiftStep_get_v_testBit_next tail counterWidth
        target x
    rw [wordHalf_val, Nat.testBit_div_two]
    simpa using hnext

/-- Arithmetic form of the unconditioned `s * 2` cyclic-shift atom when the
source coefficient top bit is false: the cyclic wrap bit is zero, so the
concrete cyclic shift agrees with width-preserving natural doubling. -/
theorem coeffWorkSMul2CyclicShiftStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkSMul2CyclicShiftStep n counterWidth x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_succ n counterWidth
        target x
    rw [hsucc, wordDouble_testBit]
    simp

/-- Arithmetic form of the unconditioned `r * 2` cyclic-shift atom when the
source coefficient top bit is false: the cyclic wrap bit is zero, so the
concrete cyclic shift agrees with width-preserving natural doubling. -/
theorem coeffWorkRMul2CyclicShiftStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkRMul2CyclicShiftStep n counterWidth x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_succ n counterWidth
        target x
    rw [hsucc, wordDouble_testBit]
    simp

/-! ## Active-controlled cyclic-shift data-path atoms -/

/-- Active-flag-controlled cyclic qubit-shift scaffold for the RNSL17 `/2`
operation on the `u` register.  The active flag is the source `f` mode bit
that separates Kaliski-mode from counter-mode; this remains a controlled shift
atom, not the complete branch dispatch [RNSL17, ECDLP.tex:425-471]. -/
def coeffWorkActiveUDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftLeftStep
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the active-controlled `u` `/2` cyclic-shift scaffold. -/
def coeffWorkActiveUDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftLeftProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- The active-controlled `u` `/2` circuit realizes its semantic step. -/
theorem coeffWorkActiveUDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveUDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkActiveUDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftLeftWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- Active-flag-controlled cyclic qubit-shift scaffold for the RNSL17 `/2`
operation on the `v` register [RNSL17, ECDLP.tex:425-471]. -/
def coeffWorkActiveVDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftLeftStep
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the active-controlled `v` `/2` cyclic-shift scaffold. -/
def coeffWorkActiveVDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftLeftProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- The active-controlled `v` `/2` circuit realizes its semantic step. -/
theorem coeffWorkActiveVDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveVDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftLeftWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Active-flag-controlled inverse cyclic qubit-shift scaffold for the RNSL17
`·2` operation on the `s` coefficient register [RNSL17, ECDLP.tex:425-471]. -/
def coeffWorkActiveSMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftRightStep
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the active-controlled `s` `·2` cyclic-shift scaffold. -/
def coeffWorkActiveSMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftRightProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The active-controlled `s` `·2` circuit realizes its semantic step. -/
theorem coeffWorkActiveSMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveSMul2CyclicShiftProgram n counterWidth)
      (coeffWorkActiveSMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftRightWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Active-flag-controlled inverse cyclic qubit-shift scaffold for the RNSL17
`·2` operation on the `r` coefficient register [RNSL17, ECDLP.tex:425-471]. -/
def coeffWorkActiveRMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftRightStep
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the active-controlled `r` `·2` cyclic-shift scaffold. -/
def coeffWorkActiveRMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftRightProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The active-controlled `r` `·2` circuit realizes its semantic step. -/
theorem coeffWorkActiveRMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveRMul2CyclicShiftProgram n counterWidth)
      (coeffWorkActiveRMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftRightWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-! ## Aux-code-controlled cyclic-shift data-path atoms -/

/-- ScratchA-controlled cyclic qubit-shift scaffold for the RNSL17 `/2`
operation on the `u` register.  In the round circuit, clean scratchA carries
the auxiliary branch-code bit `a`, whose true cases are exactly the `u`-update
branches [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkAuxUDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftLeftStep
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the scratchA-controlled `u` `/2` cyclic-shift scaffold. -/
def coeffWorkAuxUDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftLeftProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- The scratchA-controlled `u` `/2` circuit realizes its semantic step. -/
theorem coeffWorkAuxUDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxUDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftLeftWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)

/-- ScratchA-controlled cyclic qubit-shift scaffold for the RNSL17 `/2`
operation on the `v` register [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkAuxVDiv2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftLeftStep
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Circuit for the scratchA-controlled `v` `/2` cyclic-shift scaffold. -/
def coeffWorkAuxVDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftLeftProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- The scratchA-controlled `v` `/2` circuit realizes its semantic step. -/
theorem coeffWorkAuxVDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxVDiv2CyclicShiftProgram n counterWidth)
      (coeffWorkAuxVDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftLeftWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- ScratchA-controlled inverse cyclic qubit-shift scaffold for the RNSL17
`·2` operation on the `s` coefficient register [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkAuxSMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftRightStep
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the scratchA-controlled `s` `·2` cyclic-shift scaffold. -/
def coeffWorkAuxSMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftRightProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The scratchA-controlled `s` `·2` circuit realizes its semantic step. -/
theorem coeffWorkAuxSMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxSMul2CyclicShiftProgram n counterWidth)
      (coeffWorkAuxSMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftRightWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- ScratchA-controlled inverse cyclic qubit-shift scaffold for the RNSL17
`·2` operation on the `r` coefficient register [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkAuxRMul2CyclicShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.Word.controlledAdjacentShiftRightStep
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Circuit for the scratchA-controlled `r` `·2` cyclic-shift scaffold. -/
def coeffWorkAuxRMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledAdjacentShiftRightProgram
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- The scratchA-controlled `r` `·2` circuit realizes its semantic step. -/
theorem coeffWorkAuxRMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxRMul2CyclicShiftProgram n counterWidth)
      (coeffWorkAuxRMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.Word.controlledAdjacentShiftRightWitness
    (QubitLayout.canonical _) .empty
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)

/-- Paired cyclic-shift scaffold for RNSL17 branches that update
`u := u / 2` and `s := 2 * s`.  This is still only the concrete reversible
qubit-shift data path; the arithmetic invariant tying the cyclic shifts to the
integer update is discharged at the later round layer [RNSL17,
ECDLP.tex:425-465]. -/
def coeffWorkUDiv2ThenSMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkSMul2CyclicShiftStep n counterWidth
      (coeffWorkUDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the paired `u / 2`, `s * 2` cyclic-shift scaffold. -/
def coeffWorkUDiv2ThenSMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkSMul2CyclicShiftProgram n counterWidth)

/-- The paired `u / 2`, `s * 2` circuit realizes its semantic step. -/
theorem coeffWorkUDiv2ThenSMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUDiv2ThenSMul2Program n counterWidth)
      (coeffWorkUDiv2ThenSMul2Step n counterWidth) := by
  unfold coeffWorkUDiv2ThenSMul2Program coeffWorkUDiv2ThenSMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkUDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkSMul2CyclicShiftStep n counterWidth)
    (coeffWorkUDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkSMul2CyclicShift_realizes n counterWidth)

/-- Paired cyclic-shift scaffold for RNSL17 branches that update
`v := v / 2` and `r := 2 * r` [RNSL17, ECDLP.tex:425-465]. -/
def coeffWorkVDiv2ThenRMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkRMul2CyclicShiftStep n counterWidth
      (coeffWorkVDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the paired `v / 2`, `r * 2` cyclic-shift scaffold. -/
def coeffWorkVDiv2ThenRMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkRMul2CyclicShiftProgram n counterWidth)

/-- The paired `v / 2`, `r * 2` circuit realizes its semantic step. -/
theorem coeffWorkVDiv2ThenRMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVDiv2ThenRMul2Program n counterWidth)
      (coeffWorkVDiv2ThenRMul2Step n counterWidth) := by
  unfold coeffWorkVDiv2ThenRMul2Program coeffWorkVDiv2ThenRMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkVDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkRMul2CyclicShiftStep n counterWidth)
    (coeffWorkVDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkRMul2CyclicShift_realizes n counterWidth)

/-- The paired `u / 2`, `s * 2` shift group preserves the active flag. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUDiv2ThenSMul2Step n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUDiv2ThenSMul2Step]
  rw [coeffWorkSMul2CyclicShiftStep_get_active]
  exact coeffWorkUDiv2CyclicShiftStep_get_active n counterWidth x

/-- The paired `v / 2`, `r * 2` shift group preserves the active flag. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVDiv2ThenRMul2Step n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVDiv2ThenRMul2Step]
  rw [coeffWorkRMul2CyclicShiftStep_get_active]
  exact coeffWorkVDiv2CyclicShiftStep_get_active n counterWidth x

/-- In the paired `u / 2`, `s * 2` shift group, each successor target
coefficient bit reads the previous source `s` bit before the source shift. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_sCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkUDiv2ThenSMul2Step n counterWidth x).1.1.sCoeff).val.testBit
        target.succ.val =
      x.1.1.sCoeff.val.testBit (Fin.castSucc target).val := by
  unfold coeffWorkUDiv2ThenSMul2Step
  have hshift :=
    coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_succ n counterWidth
      target (coeffWorkUDiv2CyclicShiftStep n counterWidth x)
  rw [hshift]
  exact
    coeffWorkUDiv2CyclicShiftStep_get_sCoeff_testBit n counterWidth
      (Fin.castSucc target) x

/-- In the paired `u / 2`, `s * 2` shift group, target coefficient bit zero
wraps from the last source `s` bit before the source shift. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_sCoeff_testBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkUDiv2ThenSMul2Step n counterWidth x).1.1.sCoeff).val.testBit
        (0 : Fin (n + 1)).val =
      x.1.1.sCoeff.val.testBit (Fin.last n).val := by
  unfold coeffWorkUDiv2ThenSMul2Step
  have hshift :=
    coeffWorkSMul2CyclicShiftStep_get_sCoeff_testBit_zero n counterWidth
      (coeffWorkUDiv2CyclicShiftStep n counterWidth x)
  rw [hshift]
  exact
    coeffWorkUDiv2CyclicShiftStep_get_sCoeff_testBit n counterWidth
      (Fin.last n) x

/-- In the paired `v / 2`, `r * 2` shift group, each successor target
coefficient bit reads the previous source `r` bit before the source shift. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_rCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkVDiv2ThenRMul2Step n counterWidth x).1.1.rCoeff).val.testBit
        target.succ.val =
      x.1.1.rCoeff.val.testBit (Fin.castSucc target).val := by
  unfold coeffWorkVDiv2ThenRMul2Step
  have hshift :=
    coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_succ n counterWidth
      target (coeffWorkVDiv2CyclicShiftStep n counterWidth x)
  rw [hshift]
  exact
    coeffWorkVDiv2CyclicShiftStep_get_rCoeff_testBit n counterWidth
      (Fin.castSucc target) x

/-- In the paired `v / 2`, `r * 2` shift group, target coefficient bit zero
wraps from the last source `r` bit before the source shift. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_rCoeff_testBit_zero
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffWorkVDiv2ThenRMul2Step n counterWidth x).1.1.rCoeff).val.testBit
        (0 : Fin (n + 1)).val =
      x.1.1.rCoeff.val.testBit (Fin.last n).val := by
  unfold coeffWorkVDiv2ThenRMul2Step
  have hshift :=
    coeffWorkRMul2CyclicShiftStep_get_rCoeff_testBit_zero n counterWidth
      (coeffWorkVDiv2CyclicShiftStep n counterWidth x)
  rw [hshift]
  exact
    coeffWorkVDiv2CyclicShiftStep_get_rCoeff_testBit n counterWidth
      (Fin.last n) x

/-- Arithmetic form of the paired `u / 2`, `s * 2` shift group when the source
coefficient top bit is false. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkUDiv2ThenSMul2Step n counterWidth x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      coeffWorkUDiv2ThenSMul2Step_get_sCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      coeffWorkUDiv2ThenSMul2Step_get_sCoeff_testBit_succ n counterWidth
        target x
    rw [hsucc, wordDouble_testBit]
    simp

/-- Arithmetic form of the paired `v / 2`, `r * 2` shift group when the source
coefficient top bit is false. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkVDiv2ThenRMul2Step n counterWidth x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      coeffWorkVDiv2ThenRMul2Step_get_rCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      coeffWorkVDiv2ThenRMul2Step_get_rCoeff_testBit_succ n counterWidth
        target x
    rw [hsucc, wordDouble_testBit]
    simp

/-- Arithmetic form of the paired `u / 2`, `s * 2` shift group for the source
word when the shifted source is even. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hlsb : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth x).1.1.u =
      wordHalf tail.succ x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have hpres :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderUWord tail.succ counterWidth).bit bit)
      (coeffAdderSCoeffValueWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          tail.succ counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderUWordBit_coeffAdderSCoeffValueWordBit_wire_ne
            tail.succ counterWidth bit i))
      (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x)
  have hhalf :=
    congrArg (fun word => word.val.testBit bit.val)
      (coeffWorkUDiv2CyclicShiftStep_get_u_wordHalf_of_lsb_false
        tail counterWidth x hlsb)
  rw [coeffWorkUDiv2ThenSMul2Step]
  calc
    ((coeffWorkSMul2CyclicShiftStep tail.succ counterWidth
        (coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x)).1.1.u).val.testBit
        bit.val =
      ((coeffWorkUDiv2CyclicShiftStep tail.succ counterWidth x).1.1.u).val.testBit
        bit.val := by
        simpa [coeffWorkSMul2CyclicShiftStep, coeffAdderUWord_get_testBit]
          using hpres
    _ = (wordHalf tail.succ x.1.1.u).val.testBit bit.val := hhalf

/-- Arithmetic form of the paired `v / 2`, `r * 2` shift group for the source
word when the shifted source is even. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hlsb : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth x).1.1.v =
      wordHalf tail.succ x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have hpres :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderVWord tail.succ counterWidth).bit bit)
      (coeffAdderRCoeffValueWord tail.succ counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          tail.succ counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderVWordBit_coeffAdderRCoeffValueWordBit_wire_ne
            tail.succ counterWidth bit i))
      (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x)
  have hhalf :=
    congrArg (fun word => word.val.testBit bit.val)
      (coeffWorkVDiv2CyclicShiftStep_get_v_wordHalf_of_lsb_false
        tail counterWidth x hlsb)
  rw [coeffWorkVDiv2ThenRMul2Step]
  calc
    ((coeffWorkRMul2CyclicShiftStep tail.succ counterWidth
        (coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x)).1.1.v).val.testBit
        bit.val =
      ((coeffWorkVDiv2CyclicShiftStep tail.succ counterWidth x).1.1.v).val.testBit
        bit.val := by
        simpa [coeffWorkRMul2CyclicShiftStep, coeffAdderVWord_get_testBit]
          using hpres
    _ = (wordHalf tail.succ x.1.1.v).val.testBit bit.val := hhalf

/-- The paired `u / 2`, `s * 2` shift group preserves the untouched `r`
coefficient. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUDiv2ThenSMul2Step n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hsecond :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit)
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        coeffAdderSCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          n counterWidth i bit)
      (coeffWorkUDiv2CyclicShiftStep n counterWidth x)
  have hfirst :=
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit)
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        coeffAdderUWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          n counterWidth i bit)
      x
  rw [coeffWorkUDiv2ThenSMul2Step]
  calc
    ((coeffWorkSMul2CyclicShiftStep n counterWidth
        (coeffWorkUDiv2CyclicShiftStep n counterWidth x)).1.1.rCoeff).val.testBit
        bit.val =
      ((coeffWorkUDiv2CyclicShiftStep n counterWidth x).1.1.rCoeff).val.testBit
        bit.val := by
        simpa [coeffWorkSMul2CyclicShiftStep,
          coeffAdderRCoeffValueWord_get_testBit] using hsecond
    _ = x.1.1.rCoeff.val.testBit bit.val := by
        simpa [coeffWorkUDiv2CyclicShiftStep,
          coeffAdderRCoeffValueWord_get_testBit] using hfirst

/-- The paired `u / 2`, `s * 2` shift group preserves the untouched `v`
source word. -/
theorem coeffWorkUDiv2ThenSMul2Step_get_v
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUDiv2ThenSMul2Step n counterWidth x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have hsecond :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderVWord n counterWidth).bit bit)
      (coeffAdderSCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderVWordBit_coeffAdderSCoeffValueWordBit_wire_ne
            n counterWidth bit i))
      (coeffWorkUDiv2CyclicShiftStep n counterWidth x)
  have hfirst :=
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderVWord n counterWidth).bit bit)
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        coeffAdderUWordBit_coeffAdderVWordBit_wire_ne n counterWidth i bit)
      x
  rw [coeffWorkUDiv2ThenSMul2Step]
  calc
    ((coeffWorkSMul2CyclicShiftStep n counterWidth
        (coeffWorkUDiv2CyclicShiftStep n counterWidth x)).1.1.v).val.testBit
        bit.val =
      ((coeffWorkUDiv2CyclicShiftStep n counterWidth x).1.1.v).val.testBit
        bit.val := by
        simpa [coeffWorkSMul2CyclicShiftStep, coeffAdderVWord_get_testBit]
          using hsecond
    _ = x.1.1.v.val.testBit bit.val := by
        simpa [coeffWorkUDiv2CyclicShiftStep, coeffAdderVWord_get_testBit]
          using hfirst

/-- The paired `v / 2`, `r * 2` shift group preserves the untouched `s`
coefficient. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVDiv2ThenRMul2Step n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have hsecond :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderSCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
            n counterWidth bit i))
      (coeffWorkVDiv2CyclicShiftStep n counterWidth x)
  have hfirst :=
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit)
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        coeffAdderVWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          n counterWidth i bit)
      x
  rw [coeffWorkVDiv2ThenRMul2Step]
  calc
    ((coeffWorkRMul2CyclicShiftStep n counterWidth
        (coeffWorkVDiv2CyclicShiftStep n counterWidth x)).1.1.sCoeff).val.testBit
        bit.val =
      ((coeffWorkVDiv2CyclicShiftStep n counterWidth x).1.1.sCoeff).val.testBit
        bit.val := by
        simpa [coeffWorkRMul2CyclicShiftStep,
          coeffAdderSCoeffValueWord_get_testBit] using hsecond
    _ = x.1.1.sCoeff.val.testBit bit.val := by
        simpa [coeffWorkVDiv2CyclicShiftStep,
          coeffAdderSCoeffValueWord_get_testBit] using hfirst

/-- The paired `v / 2`, `r * 2` shift group preserves the untouched `u`
source word. -/
theorem coeffWorkVDiv2ThenRMul2Step_get_u
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVDiv2ThenRMul2Step n counterWidth x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have hsecond :=
    adjacentShiftRightStep_get_observed_of_word_ne
      ((coeffAdderUWord n counterWidth).bit bit)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderUWordBit_coeffAdderRCoeffValueWordBit_wire_ne
            n counterWidth bit i))
      (coeffWorkVDiv2CyclicShiftStep n counterWidth x)
  have hfirst :=
    adjacentShiftLeftStep_get_observed_of_word_ne
      ((coeffAdderUWord n counterWidth).bit bit)
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderUWordBit_coeffAdderVWordBit_wire_ne n counterWidth bit i))
      x
  rw [coeffWorkVDiv2ThenRMul2Step]
  calc
    ((coeffWorkRMul2CyclicShiftStep n counterWidth
        (coeffWorkVDiv2CyclicShiftStep n counterWidth x)).1.1.u).val.testBit
        bit.val =
      ((coeffWorkVDiv2CyclicShiftStep n counterWidth x).1.1.u).val.testBit
        bit.val := by
        simpa [coeffWorkRMul2CyclicShiftStep, coeffAdderUWord_get_testBit]
          using hsecond
    _ = x.1.1.u.val.testBit bit.val := by
        simpa [coeffWorkVDiv2CyclicShiftStep, coeffAdderUWord_get_testBit]
          using hfirst

private theorem coeffWorkUDiv2ThenSMul2Step_get_observed_of_u_s_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hu : ∀ i,
      ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire)
    (hs : ∀ i,
      ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkUDiv2ThenSMul2Step n counterWidth x) =
      observed.get x := by
  unfold coeffWorkUDiv2ThenSMul2Step
  have hsValue :
      ∀ i : Fin (n + 1),
        ((coeffAdderSCoeffValueWord n counterWidth).bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coeffAdderSCoeffValueWord, coeffAdderSCoeffWord,
      liftedSCoeffValueWord, liftedSCoeffWord, RegisterBits.sCoeffValueBit]
      using hs (WireAddress.littleEndianWire i)
  calc
    observed.get
        (coeffWorkSMul2CyclicShiftStep n counterWidth
          (coeffWorkUDiv2CyclicShiftStep n counterWidth x)) =
      observed.get (coeffWorkUDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkSMul2CyclicShiftStep] using
          adjacentShiftRightStep_get_observed_of_word_ne
            observed
            (coeffAdderSCoeffValueWord n counterWidth)
            (fun i j hij =>
              coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            hsValue
            (coeffWorkUDiv2CyclicShiftStep n counterWidth x)
    _ = observed.get x := by
        simpa [coeffWorkUDiv2CyclicShiftStep] using
          adjacentShiftLeftStep_get_observed_of_word_ne
            observed
            (coeffAdderUWord n counterWidth)
            (fun i j hij =>
              coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
                hij)
            hu
            x

private theorem coeffWorkVDiv2ThenRMul2Step_get_observed_of_v_r_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hv : ∀ i,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkVDiv2ThenRMul2Step n counterWidth x) =
      observed.get x := by
  unfold coeffWorkVDiv2ThenRMul2Step
  have hrValue :
      ∀ i : Fin (n + 1),
        ((coeffAdderRCoeffValueWord n counterWidth).bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coeffAdderRCoeffValueWord, coeffAdderRCoeffWord,
      liftedRCoeffValueWord, liftedRCoeffWord, RegisterBits.rCoeffValueBit]
      using hr (WireAddress.littleEndianWire i)
  calc
    observed.get
        (coeffWorkRMul2CyclicShiftStep n counterWidth
          (coeffWorkVDiv2CyclicShiftStep n counterWidth x)) =
      observed.get (coeffWorkVDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkRMul2CyclicShiftStep] using
          adjacentShiftRightStep_get_observed_of_word_ne
            observed
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            hrValue
            (coeffWorkVDiv2CyclicShiftStep n counterWidth x)
    _ = observed.get x := by
        simpa [coeffWorkVDiv2CyclicShiftStep] using
          adjacentShiftLeftStep_get_observed_of_word_ne
            observed
            (coeffAdderVWord n counterWidth)
            (fun i j hij =>
              coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
                hij)
            hv
            x

theorem coeffWorkUDiv2ThenSMul2Step_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUDiv2ThenSMul2Step n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x :=
  coeffWorkUDiv2ThenSMul2Step_get_observed_of_u_s_ne
    n counterWidth (coeffAdderCompareBit n counterWidth)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedUWordBit_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth i)))
    x

theorem coeffWorkVDiv2ThenRMul2Step_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVDiv2ThenRMul2Step n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x :=
  coeffWorkVDiv2ThenRMul2Step_get_observed_of_v_r_ne
    n counterWidth (coeffAdderCompareBit n counterWidth)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedVWordBit_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth i)))
    x

theorem coeffWorkUDiv2ThenSMul2Step_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUDiv2ThenSMul2Step n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x :=
  coeffWorkUDiv2ThenSMul2Step_get_observed_of_u_s_ne
    n counterWidth (coeffAdderHistoryBit n counterWidth historyIndex)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.sCoeff_history_wire_ne n counterWidth i historyIndex)))
    x

theorem coeffWorkVDiv2ThenRMul2Step_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVDiv2ThenRMul2Step n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x :=
  coeffWorkVDiv2ThenRMul2Step_get_observed_of_v_r_ne
    n counterWidth (coeffAdderHistoryBit n counterWidth historyIndex)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.rCoeff_history_wire_ne n counterWidth i historyIndex)))
    x

/-- Active-controlled paired cyclic-shift scaffold for the RNSL17
`u := u / 2`, `s := 2 * s` group.  This records the Kaliski-mode guard for
the `u/s` shift path; branch-code dispatch on the auxiliary bit is represented
by the separate scratchA-controlled group below [RNSL17, ECDLP.tex:425-475]. -/
def coeffWorkActiveUDiv2ThenSMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveSMul2CyclicShiftStep n counterWidth
      (coeffWorkActiveUDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the active-controlled `u / 2`, `s * 2` scaffold. -/
def coeffWorkActiveUDiv2ThenSMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkActiveUDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkActiveSMul2CyclicShiftProgram n counterWidth)

/-- The active-controlled `u / 2`, `s * 2` circuit realizes its step. -/
theorem coeffWorkActiveUDiv2ThenSMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveUDiv2ThenSMul2Program n counterWidth)
      (coeffWorkActiveUDiv2ThenSMul2Step n counterWidth) := by
  unfold coeffWorkActiveUDiv2ThenSMul2Program
    coeffWorkActiveUDiv2ThenSMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkActiveUDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkActiveSMul2CyclicShiftStep n counterWidth)
    (coeffWorkActiveUDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkActiveSMul2CyclicShift_realizes n counterWidth)

/-- Active-controlled paired cyclic-shift scaffold for the RNSL17
`v := v / 2`, `r := 2 * r` group.  This is a mode guard for Kaliski-mode,
not yet the branch-code dispatch on the auxiliary bit [RNSL17,
ECDLP.tex:425-475]. -/
def coeffWorkActiveVDiv2ThenRMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveRMul2CyclicShiftStep n counterWidth
      (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the active-controlled `v / 2`, `r * 2` scaffold. -/
def coeffWorkActiveVDiv2ThenRMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkActiveVDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkActiveRMul2CyclicShiftProgram n counterWidth)

/-- The active-controlled `v / 2`, `r * 2` circuit realizes its step. -/
theorem coeffWorkActiveVDiv2ThenRMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveVDiv2ThenRMul2Program n counterWidth)
      (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth) := by
  unfold coeffWorkActiveVDiv2ThenRMul2Program
    coeffWorkActiveVDiv2ThenRMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkActiveVDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkActiveRMul2CyclicShiftStep n counterWidth)
    (coeffWorkActiveVDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkActiveRMul2CyclicShift_realizes n counterWidth)

/-- ScratchA-controlled paired cyclic-shift scaffold for the RNSL17
`u := u / 2`, `s := 2 * s` branch-code group.  Under clean branch-code
staging, scratchA is the auxiliary bit `a`, so this group fires exactly for
the `a = 1` branches once the later round theorem supplies the staging
preconditions [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkAuxUDiv2ThenSMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxSMul2CyclicShiftStep n counterWidth
      (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the scratchA-controlled `u / 2`, `s * 2` scaffold. -/
def coeffWorkAuxUDiv2ThenSMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkAuxUDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkAuxSMul2CyclicShiftProgram n counterWidth)

/-- The scratchA-controlled `u / 2`, `s * 2` circuit realizes its step. -/
theorem coeffWorkAuxUDiv2ThenSMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxUDiv2ThenSMul2Program n counterWidth)
      (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth) := by
  unfold coeffWorkAuxUDiv2ThenSMul2Program coeffWorkAuxUDiv2ThenSMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkAuxUDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkAuxSMul2CyclicShiftStep n counterWidth)
    (coeffWorkAuxUDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkAuxSMul2CyclicShift_realizes n counterWidth)

/-- ScratchA-controlled paired cyclic-shift scaffold for the RNSL17
`v := v / 2`, `r := 2 * r` branch-code group.  This is paired with an explicit
inverse scaffold below so that later branch-dispatch proofs can establish the
`a = 1` cancellation from the same concrete gate-level objects [RNSL17,
ECDLP.tex:468-475]. -/
def coeffWorkAuxVDiv2ThenRMul2Step (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxRMul2CyclicShiftStep n counterWidth
      (coeffWorkAuxVDiv2CyclicShiftStep n counterWidth x)

/-- Circuit for the scratchA-controlled `v / 2`, `r * 2` scaffold. -/
def coeffWorkAuxVDiv2ThenRMul2Program (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkAuxVDiv2CyclicShiftProgram n counterWidth)
    (coeffWorkAuxRMul2CyclicShiftProgram n counterWidth)

/-- The scratchA-controlled `v / 2`, `r * 2` circuit realizes its step. -/
theorem coeffWorkAuxVDiv2ThenRMul2_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxVDiv2ThenRMul2Program n counterWidth)
      (coeffWorkAuxVDiv2ThenRMul2Step n counterWidth) := by
  unfold coeffWorkAuxVDiv2ThenRMul2Program coeffWorkAuxVDiv2ThenRMul2Step
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkAuxVDiv2CyclicShiftStep n counterWidth)
    (secondStep := coeffWorkAuxRMul2CyclicShiftStep n counterWidth)
    (coeffWorkAuxVDiv2CyclicShift_realizes n counterWidth)
    (coeffWorkAuxRMul2CyclicShift_realizes n counterWidth)

/-- ScratchA-controlled inverse of the `v := v / 2`, `r := 2 * r` shift
group.  It is used by the auxiliary-bit dispatch scaffold to cancel the
active-controlled `v/r` shift group in the `a = 1` branches; the cancellation
theorem itself is left to the later round-correctness layer [RNSL17,
ECDLP.tex:468-475]. -/
def coeffWorkAuxVDiv2ThenRMul2InverseShiftStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    EncodedBit.Word.controlledAdjacentShiftRightStep
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (EncodedBit.Word.controlledAdjacentShiftLeftStep
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderRCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        x)

/-- Circuit for the scratchA-controlled inverse `v/r` shift group. -/
def coeffWorkAuxVDiv2ThenRMul2InverseShiftProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (EncodedBit.Word.controlledAdjacentShiftLeftProgram
      (QubitLayout.canonical _) .empty
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij))
    (EncodedBit.Word.controlledAdjacentShiftRightProgram
      (QubitLayout.canonical _) .empty
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij))

/-- The scratchA-controlled inverse `v/r` circuit realizes its step. -/
theorem coeffWorkAuxVDiv2ThenRMul2InverseShift_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxVDiv2ThenRMul2InverseShiftProgram n counterWidth)
      (coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth) := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftProgram
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      EncodedBit.Word.controlledAdjacentShiftLeftStep
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderRCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i j hij))
    (secondStep :=
      EncodedBit.Word.controlledAdjacentShiftRightStep
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderVWord n counterWidth)
        (fun i =>
          coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
        (fun i j hij =>
          coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
            hij))
    (EncodedBit.Word.controlledAdjacentShiftLeftWitness
      (QubitLayout.canonical _) .empty
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij))
    (EncodedBit.Word.controlledAdjacentShiftRightWitness
      (QubitLayout.canonical _) .empty
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
          hij))

/-- If the staged auxiliary branch-code bit is false, the scratchA-controlled
`u/s` shift group is inactive. -/
theorem coeffWorkAuxUDiv2ThenSMul2Step_eq_self_of_scratchA_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x = x := by
  unfold coeffWorkAuxUDiv2ThenSMul2Step
    coeffWorkAuxUDiv2CyclicShiftStep coeffWorkAuxSMul2CyclicShiftStep
  rw [controlledAdjacentShiftLeftStep_eq_self_of_control_false
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
    x h]
  exact controlledAdjacentShiftRightStep_eq_self_of_control_false
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij)
    x h

/-- If the staged auxiliary branch-code bit is false, the scratchA-controlled
inverse `v/r` shift group is inactive. -/
theorem coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_eq_self_of_scratchA_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth x = x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  rw [controlledAdjacentShiftLeftStep_eq_self_of_control_false
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij)
    x h]
  exact controlledAdjacentShiftRightStep_eq_self_of_control_false
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
    x h

/-- The scratchA-controlled inverse `v/r` shift group undoes the
scratchA-controlled forward `v/r` shift group.  This proves only the local
cancellation of the concrete shift scaffold; branch-code staging and
arithmetic correctness remain later round-layer obligations. -/
theorem coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_comp_forward
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth
        (coeffWorkAuxVDiv2ThenRMul2Step n counterWidth x) =
      x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
    coeffWorkAuxVDiv2ThenRMul2Step coeffWorkAuxVDiv2CyclicShiftStep
    coeffWorkAuxRMul2CyclicShiftStep
  rw [EncodedBit.Word.controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep]
  exact
    EncodedBit.Word.controlledAdjacentShiftRightStep_controlledAdjacentShiftLeftStep
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      x

/-- The scratchA-controlled forward `v/r` shift group also undoes the explicit
scratchA-controlled inverse group. -/
theorem coeffWorkAuxVDiv2ThenRMul2Step_comp_inverseShift
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    coeffWorkAuxVDiv2ThenRMul2Step n counterWidth
        (coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
    coeffWorkAuxVDiv2ThenRMul2Step coeffWorkAuxVDiv2CyclicShiftStep
    coeffWorkAuxRMul2CyclicShiftStep
  rw [EncodedBit.Word.controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep]
  exact
    EncodedBit.Word.controlledAdjacentShiftRightStep_controlledAdjacentShiftLeftStep
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      x

/-- Prefix of the auxiliary-bit shift dispatch: first run the `a = 1`
`u/s` shift group, then run the active-mode `v/r` shift group. -/
def coeffWorkAuxActiveShiftDispatchPrefixStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveVDiv2ThenRMul2Step n counterWidth
      (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x)

/-- Circuit for the auxiliary-bit shift-dispatch prefix. -/
def coeffWorkAuxActiveShiftDispatchPrefixProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkAuxUDiv2ThenSMul2Program n counterWidth)
    (coeffWorkActiveVDiv2ThenRMul2Program n counterWidth)

/-- The auxiliary-bit shift-dispatch prefix circuit realizes its step. -/
theorem coeffWorkAuxActiveShiftDispatchPrefix_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxActiveShiftDispatchPrefixProgram n counterWidth)
      (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth) := by
  unfold coeffWorkAuxActiveShiftDispatchPrefixProgram
    coeffWorkAuxActiveShiftDispatchPrefixStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkAuxUDiv2ThenSMul2Step n counterWidth)
    (secondStep := coeffWorkActiveVDiv2ThenRMul2Step n counterWidth)
    (coeffWorkAuxUDiv2ThenSMul2_realizes n counterWidth)
    (coeffWorkActiveVDiv2ThenRMul2_realizes n counterWidth)

/-- Auxiliary-bit shift dispatch scaffold for the Kaliski round.  It implements
the reversible control skeleton: scratchA controls the `u/s` shift group,
active controls the `v/r` shift group, and scratchA then controls the inverse
`v/r` group so that the `v/r` shift is canceled in the `a = 1` branches.  This
is still a dispatch scaffold, not the proof that branch-code staging and the
arithmetic invariant make it equal to the source round update [RNSL17,
ECDLP.tex:425-475]. -/
def coeffWorkAuxActiveShiftDispatchStep (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth
      (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x)

/-- Gate list for the auxiliary-bit shift dispatch scaffold.  It expands the
semantic dispatch into the concrete order: auxiliary `u/s`, active `v/r`, then
the auxiliary inverse `v/r` group. -/
def coeffWorkAuxActiveShiftDispatchGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  EncodedBit.Word.controlledAdjacentShiftLeftGates
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderUWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij) ++
  EncodedBit.Word.controlledAdjacentShiftRightGates
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderSCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
        counterWidth i j hij) ++
  EncodedBit.Word.controlledAdjacentShiftLeftGates
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij) ++
  EncodedBit.Word.controlledAdjacentShiftRightGates
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij) ++
  EncodedBit.Word.controlledAdjacentShiftLeftGates
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderRCoeffValueWord n counterWidth)
    (fun i =>
      coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i)
    (fun i j hij =>
      coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
        counterWidth i j hij) ++
  EncodedBit.Word.controlledAdjacentShiftRightGates
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderVWord n counterWidth)
    (fun i => coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
    (fun i j hij =>
      coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)

/-- Base-gate program for the auxiliary-bit shift dispatch scaffold. -/
def coeffWorkAuxActiveShiftDispatchProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkAuxActiveShiftDispatchGates n counterWidth)

/-- The explicit auxiliary-bit shift dispatch gate list has the existing
semantic dispatch action. -/
theorem coeffWorkAuxActiveShiftDispatchStep_eq_gateList
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkAuxActiveShiftDispatchGates n counterWidth) x =
      coeffWorkAuxActiveShiftDispatchStep n counterWidth x := by
  unfold coeffWorkAuxActiveShiftDispatchGates
    coeffWorkAuxActiveShiftDispatchStep
    coeffWorkAuxActiveShiftDispatchPrefixStep
    coeffWorkAuxUDiv2ThenSMul2Step
    coeffWorkAuxUDiv2CyclicShiftStep
    coeffWorkAuxSMul2CyclicShiftStep
    coeffWorkActiveVDiv2ThenRMul2Step
    coeffWorkActiveVDiv2CyclicShiftStep
    coeffWorkActiveRMul2CyclicShiftStep
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  repeat rw [EncodedBit.GateSpec.stepList_append]
  rfl

/-- The auxiliary-bit shift dispatch program realizes the existing semantic
dispatch action. -/
theorem coeffWorkAuxActiveShiftDispatch_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkAuxActiveShiftDispatchProgram n counterWidth)
      (coeffWorkAuxActiveShiftDispatchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkAuxActiveShiftDispatchGates n counterWidth)
    (coeffWorkAuxActiveShiftDispatchStep_eq_gateList n counterWidth)

/-- Exact physical length of the six controlled adjacent-shift sweeps. -/
theorem coeffWorkAuxActiveShiftDispatchGates_length
    (n counterWidth : Nat) :
    (coeffWorkAuxActiveShiftDispatchGates n counterWidth).length =
      9 * (n - 1) + 9 * n := by
  simp only [coeffWorkAuxActiveShiftDispatchGates, List.length_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_length,
    EncodedBit.Word.controlledAdjacentShiftRightGates_length]
  omega

/-- The auxiliary shift dispatcher contains no X leaf. -/
theorem coeffWorkAuxActiveShiftDispatchGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkAuxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp only [coeffWorkAuxActiveShiftDispatchGates, List.map_append,
    List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_xMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_xMultiplicity_sum,
    Nat.zero_add]

/-- The auxiliary shift dispatcher contains no CNOT leaf. -/
theorem coeffWorkAuxActiveShiftDispatchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkAuxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [coeffWorkAuxActiveShiftDispatchGates, List.map_append,
    List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_cnotMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_cnotMultiplicity_sum,
    Nat.zero_add]

/-- Exact Toffoli coordinate of the six controlled adjacent-shift sweeps. -/
theorem coeffWorkAuxActiveShiftDispatchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkAuxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      9 * (n - 1) + 9 * n := by
  simp only [coeffWorkAuxActiveShiftDispatchGates, List.map_append,
    List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_toffoliMultiplicity_sum]
  omega

/-- The active-controlled `v / 2` cyclic-shift atom agrees with the
scratchA-controlled atom when the active flag and staged auxiliary branch-code
bit have the same readout. -/
theorem
    coeffWorkActiveVDiv2CyclicShiftStep_eq_auxVDiv2CyclicShiftStep_of_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x =
      coeffWorkAuxVDiv2CyclicShiftStep n counterWidth x := by
  simpa [coeffWorkActiveVDiv2CyclicShiftStep,
    coeffWorkAuxVDiv2CyclicShiftStep] using
    controlledAdjacentShiftLeftStep_eq_of_control_get_eq
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i =>
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      x h

/-- The active-controlled `r * 2` cyclic-shift atom agrees with the
scratchA-controlled atom when the active flag and staged auxiliary branch-code
bit have the same readout. -/
theorem
    coeffWorkActiveRMul2CyclicShiftStep_eq_auxRMul2CyclicShiftStep_of_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    coeffWorkActiveRMul2CyclicShiftStep n counterWidth x =
      coeffWorkAuxRMul2CyclicShiftStep n counterWidth x := by
  simpa [coeffWorkActiveRMul2CyclicShiftStep,
    coeffWorkAuxRMul2CyclicShiftStep] using
    controlledAdjacentShiftRightStep_eq_of_control_get_eq
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i =>
        coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i =>
        coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      x h

private theorem coeffWorkActiveVDiv2CyclicShiftStep_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) := by
  rw [show
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x by
      simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
        controlledAdjacentShiftLeftStep_get_observed_of_word_ne
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (fun i => Ne.symm
            (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i))
          x]
  rw [show
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x by
      simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
        controlledAdjacentShiftLeftStep_get_observed_of_word_ne
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (fun i => Ne.symm
            (coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n
              counterWidth i))
          x]
  exact h

/-- The active-controlled `v / 2`, `r * 2` shift group agrees with the
scratchA-controlled group when the active flag and staged auxiliary branch-code
bit have the same readout. -/
theorem
    coeffWorkActiveVDiv2ThenRMul2Step_eq_auxVDiv2ThenRMul2Step_of_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x =
      coeffWorkAuxVDiv2ThenRMul2Step n counterWidth x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step coeffWorkAuxVDiv2ThenRMul2Step
  have hfirst :
      coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x =
        coeffWorkAuxVDiv2CyclicShiftStep n counterWidth x :=
    coeffWorkActiveVDiv2CyclicShiftStep_eq_auxVDiv2CyclicShiftStep_of_active_eq_scratchA
      n counterWidth x h
  have hcontrolsAfter :
      (coeffAdderActiveBit n counterWidth).get
          (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) =
        (coeffAdderScratchABit n counterWidth).get
          (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) :=
    coeffWorkActiveVDiv2CyclicShiftStep_active_eq_scratchA
      n counterWidth x h
  calc
    coeffWorkActiveRMul2CyclicShiftStep n counterWidth
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) =
      coeffWorkAuxRMul2CyclicShiftStep n counterWidth
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) := by
        exact
          coeffWorkActiveRMul2CyclicShiftStep_eq_auxRMul2CyclicShiftStep_of_active_eq_scratchA
            n counterWidth
            (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)
            hcontrolsAfter
    _ =
      coeffWorkAuxRMul2CyclicShiftStep n counterWidth
        (coeffWorkAuxVDiv2CyclicShiftStep n counterWidth x) := by
        rw [hfirst]

private theorem coeffWorkActiveVDiv2ThenRMul2Step_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step
  calc
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveRMul2CyclicShiftStep n counterWidth
          (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)) =
      (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkActiveRMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            (fun i => Ne.symm
              (coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i))
            (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)
    _ = (coeffAdderActiveBit n counterWidth).get x := by
        simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderVWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
                hij)
            (fun i => Ne.symm
              (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i))
            x

private theorem coeffWorkActiveVDiv2ThenRMul2Step_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step
  calc
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveRMul2CyclicShiftStep n counterWidth
          (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)) =
      (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkActiveRMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            (fun i => Ne.symm
              (coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i))
            (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)
    _ = (coeffAdderScratchABit n counterWidth).get x := by
        simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderVWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
                hij)
            (fun i => Ne.symm
              (coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n
                counterWidth i))
            x

/-- If the staged auxiliary branch-code bit is false, the auxiliary-bit shift
dispatch invokes only the active-controlled `v/r` shift group. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_activeVDiv2ThenRMul2Step_of_scratchA_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x := by
  unfold coeffWorkAuxActiveShiftDispatchStep
    coeffWorkAuxActiveShiftDispatchPrefixStep
  have hauxUS :
      coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x = x :=
    coeffWorkAuxUDiv2ThenSMul2Step_eq_self_of_scratchA_false
      n counterWidth x h
  have hscratchAfterActive :
      (coeffAdderScratchABit n counterWidth).get
          (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x) =
        false := by
    rw [coeffWorkActiveVDiv2ThenRMul2Step_get_scratchA]
    exact h
  rw [hauxUS]
  exact
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_eq_self_of_scratchA_false
      n counterWidth (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x)
      hscratchAfterActive

private theorem coeffWorkAuxUDiv2ThenSMul2Step_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  unfold coeffWorkAuxUDiv2ThenSMul2Step
  calc
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxSMul2CyclicShiftStep n counterWidth
          (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)) =
      (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkAuxSMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderSCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            (fun i => Ne.symm
              (coeffAdderActiveBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i))
            (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)
    _ = (coeffAdderActiveBit n counterWidth).get x := by
        simpa [coeffWorkAuxUDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderUWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
                hij)
            (fun i => Ne.symm
              (coeffAdderActiveBit_coeffAdderUWordBit_wire_ne n counterWidth i))
            x

private theorem coeffWorkAuxUDiv2ThenSMul2Step_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  unfold coeffWorkAuxUDiv2ThenSMul2Step
  calc
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxSMul2CyclicShiftStep n counterWidth
          (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)) =
      (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkAuxSMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderSCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            (fun i => Ne.symm
              (coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i))
            (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)
    _ = (coeffAdderScratchABit n counterWidth).get x := by
        simpa [coeffWorkAuxUDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderUWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
                hij)
            (fun i => Ne.symm
              (coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n
                counterWidth i))
            x

/-- If the active flag equals the staged auxiliary branch-code bit, the
auxiliary-bit shift dispatch cancels the active-controlled `v/r` shift group
and leaves only the scratchA-controlled `u/s` shift group. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_auxUDiv2ThenSMul2Step_of_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x := by
  unfold coeffWorkAuxActiveShiftDispatchStep
    coeffWorkAuxActiveShiftDispatchPrefixStep
  have hcontrolsAfterUS :
      (coeffAdderActiveBit n counterWidth).get
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) =
        (coeffAdderScratchABit n counterWidth).get
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) := by
    rw [coeffWorkAuxUDiv2ThenSMul2Step_get_active,
      coeffWorkAuxUDiv2ThenSMul2Step_get_scratchA, h]
  have hactiveAux :
      coeffWorkActiveVDiv2ThenRMul2Step n counterWidth
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) =
        coeffWorkAuxVDiv2ThenRMul2Step n counterWidth
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) :=
    coeffWorkActiveVDiv2ThenRMul2Step_eq_auxVDiv2ThenRMul2Step_of_active_eq_scratchA
      n counterWidth (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x)
      hcontrolsAfterUS
  calc
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth
        (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x)) =
      coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth
        (coeffWorkAuxVDiv2ThenRMul2Step n counterWidth
          (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x)) := by
        rw [hactiveAux]
    _ = coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x := by
        exact coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_comp_forward
          n counterWidth (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x)

/-- When the staged auxiliary branch-code bit is true, the scratchA-controlled
`u/s` shift group acts as the unconditioned `u / 2`, `s * 2` pair. -/
theorem coeffWorkAuxUDiv2ThenSMul2Step_eq_uDiv2ThenSMul2Step_of_scratchA_true
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderScratchABit n counterWidth).get x = true) :
    coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x =
      coeffWorkUDiv2ThenSMul2Step n counterWidth x := by
  unfold coeffWorkAuxUDiv2ThenSMul2Step coeffWorkUDiv2ThenSMul2Step
    coeffWorkAuxUDiv2CyclicShiftStep coeffWorkUDiv2CyclicShiftStep
    coeffWorkAuxSMul2CyclicShiftStep coeffWorkSMul2CyclicShiftStep
  have hfirst :
      EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderUWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
              hij)
          x =
        EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderUWord n counterWidth)
          (fun i j hij =>
            coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
              hij)
          x :=
    controlledAdjacentShiftLeftStep_eq_adjacentShiftLeftStep_of_control_true
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderUWord n counterWidth)
      (fun i =>
        coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      x h
  have hscratchAfter :
      (coeffAdderScratchABit n counterWidth).get
          (EncodedBit.Word.adjacentShiftLeftStep
            (coeffAdderUWord n counterWidth)
            (fun i j hij =>
              coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
                hij)
            x) =
        true := by
    rw [adjacentShiftLeftStep_get_observed_of_word_ne
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderUWord n counterWidth)
      (fun i j hij =>
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i))
      x]
    exact h
  calc
    EncodedBit.Word.controlledAdjacentShiftRightStep
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderSCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderUWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
              hij)
          x) =
      EncodedBit.Word.controlledAdjacentShiftRightStep
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderSCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderUWord n counterWidth)
          (fun i j hij =>
            coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
              hij)
          x) := by
        rw [hfirst]
    _ =
      EncodedBit.Word.adjacentShiftRightStep
        (coeffAdderSCoeffValueWord n counterWidth)
        (fun i j hij =>
          coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderUWord n counterWidth)
          (fun i j hij =>
            coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
              hij)
          x) := by
        exact
          controlledAdjacentShiftRightStep_eq_adjacentShiftRightStep_of_control_true
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderSCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            _ hscratchAfter

/-- When the active flag is true, the active-controlled `v/r` shift group acts
as the unconditioned `v / 2`, `r * 2` pair. -/
theorem coeffWorkActiveVDiv2ThenRMul2Step_eq_vDiv2ThenRMul2Step_of_active_true
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderActiveBit n counterWidth).get x = true) :
    coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x =
      coeffWorkVDiv2ThenRMul2Step n counterWidth x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step coeffWorkVDiv2ThenRMul2Step
    coeffWorkActiveVDiv2CyclicShiftStep coeffWorkVDiv2CyclicShiftStep
    coeffWorkActiveRMul2CyclicShiftStep coeffWorkRMul2CyclicShiftStep
  have hfirst :
      EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          x =
        EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderVWord n counterWidth)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          x :=
    controlledAdjacentShiftLeftStep_eq_adjacentShiftLeftStep_of_control_true
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i =>
        coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      x h
  have hactiveAfter :
      (coeffAdderActiveBit n counterWidth).get
          (EncodedBit.Word.adjacentShiftLeftStep
            (coeffAdderVWord n counterWidth)
            (fun i j hij =>
              coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
                hij)
            x) =
        true := by
    rw [adjacentShiftLeftStep_get_observed_of_word_ne
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderVWord n counterWidth)
      (fun i j hij =>
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
      (fun i =>
        Ne.symm
          (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i))
      x]
    exact h
  calc
    EncodedBit.Word.controlledAdjacentShiftRightStep
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderRCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          x) =
      EncodedBit.Word.controlledAdjacentShiftRightStep
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderRCoeffValueWord n counterWidth)
        (fun i =>
          coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i)
        (fun i j hij =>
          coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderVWord n counterWidth)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          x) := by
        rw [hfirst]
    _ =
      EncodedBit.Word.adjacentShiftRightStep
        (coeffAdderRCoeffValueWord n counterWidth)
        (fun i j hij =>
          coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
            counterWidth i j hij)
        (EncodedBit.Word.adjacentShiftLeftStep
          (coeffAdderVWord n counterWidth)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          x) := by
        exact
          controlledAdjacentShiftRightStep_eq_adjacentShiftRightStep_of_control_true
            (coeffAdderActiveBit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            _ hactiveAfter

/-- If the active flag is false, the active-controlled `v / 2`, `r * 2`
shift group is a no-op. -/
theorem coeffWorkActiveVDiv2ThenRMul2Step_eq_self_of_active_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h : (coeffAdderActiveBit n counterWidth).get x = false) :
    coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x = x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step
  have hfirst :
      coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x = x := by
    simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
      controlledAdjacentShiftLeftStep_eq_self_of_control_false
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderVWord n counterWidth)
        (fun i =>
          coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
        (fun i j hij =>
          coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j hij)
        x h
  rw [hfirst]
  exact
    controlledAdjacentShiftRightStep_eq_self_of_control_false
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderRCoeffValueWord n counterWidth)
      (fun i =>
        coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i)
      (fun i j hij =>
        coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
          counterWidth i j hij)
      x h

/-- If branch-code staging leaves both the active flag and scratchA true, the
auxiliary-bit shift dispatch selects the unconditioned `u/s` shift group. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkUDiv2ThenSMul2Step n counterWidth x := by
  have hcontrols :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x := by
    rw [hactive, hscratchA]
  calc
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x :=
        coeffWorkAuxActiveShiftDispatchStep_eq_auxUDiv2ThenSMul2Step_of_active_eq_scratchA
          n counterWidth x hcontrols
    _ = coeffWorkUDiv2ThenSMul2Step n counterWidth x :=
        coeffWorkAuxUDiv2ThenSMul2Step_eq_uDiv2ThenSMul2Step_of_scratchA_true
          n counterWidth x hscratchA

/-- If branch-code staging leaves the active flag true and scratchA false, the
auxiliary-bit shift dispatch selects the unconditioned `v/r` shift group. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkVDiv2ThenRMul2Step n counterWidth x := by
  calc
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
      coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x :=
        coeffWorkAuxActiveShiftDispatchStep_eq_activeVDiv2ThenRMul2Step_of_scratchA_false
          n counterWidth x hscratchA
    _ = coeffWorkVDiv2ThenRMul2Step n counterWidth x :=
        coeffWorkActiveVDiv2ThenRMul2Step_eq_vDiv2ThenRMul2Step_of_active_true
          n counterWidth x hactive

/-- If both branch-dispatch controls are false, the auxiliary-bit shift
dispatch is a no-op. -/
theorem coeffWorkAuxActiveShiftDispatchStep_eq_self_of_active_false_scratchA_false
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x = x := by
  calc
    coeffWorkAuxActiveShiftDispatchStep n counterWidth x =
        coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x :=
      coeffWorkAuxActiveShiftDispatchStep_eq_activeVDiv2ThenRMul2Step_of_scratchA_false
        n counterWidth x hscratchA
    _ = x :=
      coeffWorkActiveVDiv2ThenRMul2Step_eq_self_of_active_false
        n counterWidth x hactive

private theorem coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  calc
    (coeffAdderActiveBit n counterWidth).get
        (EncodedBit.Word.controlledAdjacentShiftRightStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (EncodedBit.Word.controlledAdjacentShiftLeftStep
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            x)) =
      (coeffAdderActiveBit n counterWidth).get
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          x) := by
        exact controlledAdjacentShiftRightStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (fun i => Ne.symm
            (coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i))
          _
    _ = (coeffAdderActiveBit n counterWidth).get x := by
        exact controlledAdjacentShiftLeftStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderActiveBit n counterWidth)
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          (fun i => Ne.symm
            (coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i))
          x

private theorem coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  calc
    (coeffAdderScratchABit n counterWidth).get
        (EncodedBit.Word.controlledAdjacentShiftRightStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (EncodedBit.Word.controlledAdjacentShiftLeftStep
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            x)) =
      (coeffAdderScratchABit n counterWidth).get
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          x) := by
        exact controlledAdjacentShiftRightStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (fun i => Ne.symm
            (coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i))
          _
    _ = (coeffAdderScratchABit n counterWidth).get x := by
        exact controlledAdjacentShiftLeftStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          (fun i => Ne.symm
            (coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i))
          x

/-- The auxiliary-bit shift-dispatch prefix preserves the active flag. -/
theorem coeffWorkAuxActiveShiftDispatchPrefixStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  unfold coeffWorkAuxActiveShiftDispatchPrefixStep
  rw [coeffWorkActiveVDiv2ThenRMul2Step_get_active]
  exact coeffWorkAuxUDiv2ThenSMul2Step_get_active n counterWidth x

/-- The auxiliary-bit shift-dispatch prefix preserves scratchA, the staged
auxiliary branch-code bit. -/
theorem coeffWorkAuxActiveShiftDispatchPrefixStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  unfold coeffWorkAuxActiveShiftDispatchPrefixStep
  rw [coeffWorkActiveVDiv2ThenRMul2Step_get_scratchA]
  exact coeffWorkAuxUDiv2ThenSMul2Step_get_scratchA n counterWidth x

/-- The auxiliary-bit Kaliski shift dispatch preserves the active flag. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  unfold coeffWorkAuxActiveShiftDispatchStep
  rw [coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_active]
  exact coeffWorkAuxActiveShiftDispatchPrefixStep_get_active n counterWidth x

/-- The auxiliary-bit Kaliski shift dispatch preserves scratchA, so the later
branch-code uncompute can still clean the staged auxiliary bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  unfold coeffWorkAuxActiveShiftDispatchStep
  rw [coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_scratchA]
  exact coeffWorkAuxActiveShiftDispatchPrefixStep_get_scratchA n counterWidth x

private theorem coeffWorkActiveVDiv2ThenRMul2Step_get_observed_of_v_r_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hv : ∀ i,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkActiveVDiv2ThenRMul2Step n counterWidth x) =
      observed.get x := by
  unfold coeffWorkActiveVDiv2ThenRMul2Step
  have hrValue :
      ∀ i : Fin (n + 1),
        ((coeffAdderRCoeffValueWord n counterWidth).bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coeffAdderRCoeffValueWord, coeffAdderRCoeffWord,
      liftedRCoeffValueWord, liftedRCoeffWord, RegisterBits.rCoeffValueBit]
      using hr (WireAddress.littleEndianWire i)
  calc
    observed.get
        (coeffWorkActiveRMul2CyclicShiftStep n counterWidth
          (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)) =
      observed.get (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkActiveRMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            observed
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            hrValue
            (coeffWorkActiveVDiv2CyclicShiftStep n counterWidth x)
    _ = observed.get x := by
        simpa [coeffWorkActiveVDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderActiveBit n counterWidth)
            observed
            (coeffAdderVWord n counterWidth)
            (fun i =>
              coeffAdderActiveBit_coeffAdderVWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
                hij)
            hv
            x

private theorem coeffWorkAuxUDiv2ThenSMul2Step_get_observed_of_u_s_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hu : ∀ i,
      ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire)
    (hs : ∀ i,
      ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkAuxUDiv2ThenSMul2Step n counterWidth x) =
      observed.get x := by
  unfold coeffWorkAuxUDiv2ThenSMul2Step
  have hsValue :
      ∀ i : Fin (n + 1),
        ((coeffAdderSCoeffValueWord n counterWidth).bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coeffAdderSCoeffValueWord, coeffAdderSCoeffWord,
      liftedSCoeffValueWord, liftedSCoeffWord, RegisterBits.sCoeffValueBit]
      using hs (WireAddress.littleEndianWire i)
  calc
    observed.get
        (coeffWorkAuxSMul2CyclicShiftStep n counterWidth
          (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)) =
      observed.get (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x) := by
        simpa [coeffWorkAuxSMul2CyclicShiftStep] using
          controlledAdjacentShiftRightStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            observed
            (coeffAdderSCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderSCoeffValueWordBit_coeffAdderSCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            hsValue
            (coeffWorkAuxUDiv2CyclicShiftStep n counterWidth x)
    _ = observed.get x := by
        simpa [coeffWorkAuxUDiv2CyclicShiftStep] using
          controlledAdjacentShiftLeftStep_get_observed_of_word_ne
            (coeffAdderScratchABit n counterWidth)
            observed
            (coeffAdderUWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderUWordBit_wire_ne n counterWidth i)
            (fun i j hij =>
              coeffAdderUWordBit_coeffAdderUWordBit_wire_ne n counterWidth i j
                hij)
            hu
            x

private theorem
    coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_observed_of_v_r_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hv : ∀ i,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get
        (coeffWorkAuxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      observed.get x := by
  unfold coeffWorkAuxVDiv2ThenRMul2InverseShiftStep
  have hrValue :
      ∀ i : Fin (n + 1),
        ((coeffAdderRCoeffValueWord n counterWidth).bit i).wire ≠
          observed.wire := by
    intro i
    simpa [coeffAdderRCoeffValueWord, coeffAdderRCoeffWord,
      liftedRCoeffValueWord, liftedRCoeffWord, RegisterBits.rCoeffValueBit]
      using hr (WireAddress.littleEndianWire i)
  calc
    observed.get
        (EncodedBit.Word.controlledAdjacentShiftRightStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          (EncodedBit.Word.controlledAdjacentShiftLeftStep
            (coeffAdderScratchABit n counterWidth)
            (coeffAdderRCoeffValueWord n counterWidth)
            (fun i =>
              coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i)
            (fun i j hij =>
              coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
                counterWidth i j hij)
            x)) =
      observed.get
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          (coeffAdderScratchABit n counterWidth)
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          x) := by
        exact controlledAdjacentShiftRightStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          observed
          (coeffAdderVWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderVWordBit_wire_ne n counterWidth i)
          (fun i j hij =>
            coeffAdderVWordBit_coeffAdderVWordBit_wire_ne n counterWidth i j
              hij)
          hv
          _
    _ = observed.get x := by
        exact controlledAdjacentShiftLeftStep_get_observed_of_word_ne
          (coeffAdderScratchABit n counterWidth)
          observed
          (coeffAdderRCoeffValueWord n counterWidth)
          (fun i =>
            coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i)
          (fun i j hij =>
            coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne n
              counterWidth i j hij)
          hrValue
          x

private theorem
    coeffWorkAuxActiveShiftDispatchPrefixStep_get_observed_of_words_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hu : ∀ i,
      ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire)
    (hs : ∀ i,
      ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (hv : ∀ i,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x) =
      observed.get x := by
  unfold coeffWorkAuxActiveShiftDispatchPrefixStep
  rw [coeffWorkActiveVDiv2ThenRMul2Step_get_observed_of_v_r_ne
    n counterWidth observed hv hr]
  exact coeffWorkAuxUDiv2ThenSMul2Step_get_observed_of_u_s_ne
    n counterWidth observed hu hs x

private theorem coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithCoeffAdderWorkEncoding n counterWidth))
    (hu : ∀ i,
      ((coeffAdderUWord n counterWidth).bit i).wire ≠ observed.wire)
    (hs : ∀ i,
      ((coeffAdderSCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (hv : ∀ i,
      ((coeffAdderVWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((coeffAdderRCoeffWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    observed.get (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      observed.get x := by
  unfold coeffWorkAuxActiveShiftDispatchStep
  rw [coeffWorkAuxVDiv2ThenRMul2InverseShiftStep_get_observed_of_v_r_ne
    n counterWidth observed hv hr]
  exact
    coeffWorkAuxActiveShiftDispatchPrefixStep_get_observed_of_words_ne
      n counterWidth observed hu hs hv hr x

/-- The auxiliary-bit Kaliski shift dispatch preserves the comparison
ancilla. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (coeffAdderCompareBit n counterWidth)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedUWordBit_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedVWordBit_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedCompareBit n counterWidth)
        (Ne.symm (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth i)))
    x

/-- The auxiliary-bit Kaliski shift dispatch preserves the second scratch
bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (coeffAdderScratchBBit n counterWidth)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedScratchBBit n counterWidth)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_scratchB_wire_ne n counterWidth
                (WireAddress.littleEndianWire i))))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedScratchBBit n counterWidth)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth i)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedScratchBBit n counterWidth)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_scratchB_wire_ne n counterWidth
                (WireAddress.littleEndianWire i))))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedScratchBBit n counterWidth)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth i)))
    x

/-- The auxiliary-bit Kaliski shift dispatch preserves every stored
branch-history bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (coeffAdderHistoryBit n counterWidth historyIndex)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.sCoeff_history_wire_ne n counterWidth i historyIndex)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex)))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedHistoryBit n counterWidth historyIndex)
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.rCoeff_history_wire_ne n counterWidth i historyIndex)))
    x

/-- The auxiliary-shift dispatcher never touches a padding-counter value bit.
This raw physical getter is intentionally independent of source readout. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_counterValueBit
    (n counterWidth : Nat) (counterBit : Fin counterWidth)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCounterValueBit n counterWidth counterBit).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderCounterValueBit n counterWidth counterBit).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (coeffAdderCounterValueBit n counterWidth counterBit)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit)))
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)
                (WireAddress.littleEndianWire counterBit))))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit)))
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.sCoeff_counter_wire_ne n counterWidth i
            (WireAddress.littleEndianWire counterBit))))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit)))
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)
                (WireAddress.littleEndianWire counterBit))))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit)))
        (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.rCoeff_counter_wire_ne n counterWidth i
            (WireAddress.littleEndianWire counterBit))))
    x

/-- The auxiliary-bit Kaliski shift dispatch preserves every comparison-work
carry bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (coeffAdderComparisonCarryBit n counterWidth workBit)
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (liftedComparisonCarryBit n counterWidth workBit)
        (liftedUWordBit_liftedComparisonCarry_wire_ne n counterWidth i
          workBit))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (liftedComparisonCarryBit n counterWidth workBit)
        (liftedSCoeffWordBit_liftedComparisonCarry_wire_ne n counterWidth i
          workBit))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (liftedComparisonCarryBit n counterWidth workBit)
        (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth i
          workBit))
    (fun i =>
      liftComparisonStateBit_liftComparisonStateBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (liftedComparisonCarryBit n counterWidth workBit)
        (liftedRCoeffWordBit_liftedComparisonCarry_wire_ne n counterWidth i
          workBit))
    x

/-- The auxiliary-bit Kaliski shift dispatch preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_carryIn
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (liftedCoeffAdderCarryInBit n counterWidth)
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (coeffAdderCarryInWorkBit n))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (coeffAdderCarryInWorkBit n))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (coeffAdderCarryInWorkBit n))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (coeffAdderCarryInWorkBit n))
    x

/-- The auxiliary-bit Kaliski shift dispatch preserves each coefficient-adder
temporary carry-work bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_get_carryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  exact coeffWorkAuxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit)
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedUWord n counterWidth).bit i)
        (coeffAdderCarryWorkBit n workBit))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedSCoeffWord n counterWidth).bit i)
        (coeffAdderCarryWorkBit n workBit))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedVWord n counterWidth).bit i)
        (coeffAdderCarryWorkBit n workBit))
    (fun i =>
      liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne n counterWidth
        ((liftedRCoeffWord n counterWidth).bit i)
        (coeffAdderCarryWorkBit n workBit))
    x

/-- The auxiliary-bit shift-dispatch prefix preserves equality between the
active flag and the staged auxiliary branch-code bit. -/
theorem coeffWorkAuxActiveShiftDispatchPrefixStep_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchPrefixStep n counterWidth x) := by
  rw [coeffWorkAuxActiveShiftDispatchPrefixStep_get_active,
    coeffWorkAuxActiveShiftDispatchPrefixStep_get_scratchA, h]

/-- The auxiliary-bit Kaliski shift dispatch preserves equality between the
active flag and the staged auxiliary branch-code bit. -/
theorem coeffWorkAuxActiveShiftDispatchStep_active_eq_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (h :
      (coeffAdderActiveBit n counterWidth).get x =
        (coeffAdderScratchABit n counterWidth).get x) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get
        (coeffWorkAuxActiveShiftDispatchStep n counterWidth x) := by
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active,
    coeffWorkAuxActiveShiftDispatchStep_get_scratchA, h]

/-! ## Compact-carrier cyclic shifts -/

namespace Compact

private theorem uValueWord_bit_wire_ne (n counterWidth : Nat)
    (left right : Fin n) (hne : left ≠ right) :
    ((uValueWord n counterWidth).bit left).wire ≠
      ((uValueWord n counterWidth).bit right).wire := by
  apply liftCoreBit_wire_ne
  exact u_u_wire_ne n counterWidth
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne hne)

private theorem vValueWord_bit_wire_ne (n counterWidth : Nat)
    (left right : Fin n) (hne : left ≠ right) :
    ((vValueWord n counterWidth).bit left).wire ≠
      ((vValueWord n counterWidth).bit right).wire := by
  apply liftCoreBit_wire_ne
  exact v_v_wire_ne n counterWidth
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne hne)

private theorem sCoeffValueWord_bit_wire_ne (n counterWidth : Nat)
    (left right : Fin (n + 1)) (hne : left ≠ right) :
    ((sCoeffValueWord n counterWidth).bit left).wire ≠
      ((sCoeffValueWord n counterWidth).bit right).wire := by
  apply liftCoreBit_wire_ne
  exact sCoeff_sCoeff_wire_ne n counterWidth
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne hne)

private theorem rCoeffValueWord_bit_wire_ne (n counterWidth : Nat)
    (left right : Fin (n + 1)) (hne : left ≠ right) :
    ((rCoeffValueWord n counterWidth).bit left).wire ≠
      ((rCoeffValueWord n counterWidth).bit right).wire := by
  apply liftCoreBit_wire_ne
  exact rCoeff_rCoeff_wire_ne n counterWidth
    (WireAddress.littleEndianWire left)
    (WireAddress.littleEndianWire right)
    (littleEndianWire_ne hne)

private theorem adjacentShiftLeftGates_multiplicity_sum
    {Data : Type} {wordWidth : Nat}
    {wordEncoding : BinaryLabelEncoding Data}
    (word : EncodedBit.Word wordEncoding wordWidth)
    (hword : ∀ i j, i ≠ j →
      (word.bit i).wire ≠ (word.bit j).wire)
    (multiplicity : EncodedBit.GateSpec wordEncoding → Nat) (count : Nat)
    (hcount : ∀ i,
      ((EncodedBit.Word.adjacentSwapGates word hword i).map
        multiplicity).sum = count) :
    ((EncodedBit.Word.adjacentShiftLeftGates word hword).map
      multiplicity).sum = count * (wordWidth - 1) := by
  unfold EncodedBit.Word.adjacentShiftLeftGates
  have hsum : ∀ indices : List (Fin (wordWidth - 1)),
      ((indices.flatMap
        (EncodedBit.Word.adjacentSwapGates word hword)).map
          multiplicity).sum = count * indices.length := by
    intro indices
    induction indices with
    | nil => simp
    | cons bit rest ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.length_cons]
        rw [hcount bit, ih]
        simp [Nat.mul_add, Nat.add_comm]
  simpa only [List.length_ofFn] using
    hsum (List.ofFn fun i : Fin (wordWidth - 1) => i)

private theorem adjacentShiftLeftGates_length
    {Data : Type} {wordWidth : Nat}
    {wordEncoding : BinaryLabelEncoding Data}
    (word : EncodedBit.Word wordEncoding wordWidth)
    (hword : ∀ i j, i ≠ j →
      (word.bit i).wire ≠ (word.bit j).wire) :
    (EncodedBit.Word.adjacentShiftLeftGates word hword).length =
      3 * (wordWidth - 1) := by
  simp [EncodedBit.Word.adjacentShiftLeftGates,
    EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates,
    List.length_flatMap, Function.comp_def]
  omega

private theorem adjacentShiftLeftGates_xMultiplicity_sum
    {Data : Type} {wordWidth : Nat}
    {wordEncoding : BinaryLabelEncoding Data}
    (word : EncodedBit.Word wordEncoding wordWidth)
    (hword : ∀ i j, i ≠ j →
      (word.bit i).wire ≠ (word.bit j).wire) :
    ((EncodedBit.Word.adjacentShiftLeftGates word hword).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa using adjacentShiftLeftGates_multiplicity_sum word hword
    EncodedBit.GateSpec.xMultiplicity 0 (by
      intro bit
      simp [EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates])

private theorem adjacentShiftLeftGates_cnotMultiplicity_sum
    {Data : Type} {wordWidth : Nat}
    {wordEncoding : BinaryLabelEncoding Data}
    (word : EncodedBit.Word wordEncoding wordWidth)
    (hword : ∀ i j, i ≠ j →
      (word.bit i).wire ≠ (word.bit j).wire) :
    ((EncodedBit.Word.adjacentShiftLeftGates word hword).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * (wordWidth - 1) := by
  exact adjacentShiftLeftGates_multiplicity_sum word hword
    EncodedBit.GateSpec.cnotMultiplicity 3 (by
      intro bit
      simp [EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates])

private theorem adjacentShiftLeftGates_toffoliMultiplicity_sum
    {Data : Type} {wordWidth : Nat}
    {wordEncoding : BinaryLabelEncoding Data}
    (word : EncodedBit.Word wordEncoding wordWidth)
    (hword : ∀ i j, i ≠ j →
      (word.bit i).wire ≠ (word.bit j).wire) :
    ((EncodedBit.Word.adjacentShiftLeftGates word hword).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simpa using adjacentShiftLeftGates_multiplicity_sum word hword
    EncodedBit.GateSpec.toffoliMultiplicity 0 (by
      intro bit
      simp [EncodedBit.Word.adjacentSwapGates, EncodedBit.swapGates])

/-- Literal adjacent-swap gate list for the compact `u / 2` cyclic shift. -/
def uDiv2CyclicShiftGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.Word.adjacentShiftLeftGates
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)

/-- Literal adjacent-swap gate list for the compact `v / 2` cyclic shift. -/
def vDiv2CyclicShiftGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.Word.adjacentShiftLeftGates
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)

/-- Literal inverse adjacent-swap list for the compact `s * 2` shift. -/
def sMul2CyclicShiftGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.Word.adjacentShiftRightGates
    (sCoeffValueWord n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)

/-- Literal inverse adjacent-swap list for the compact `r * 2` shift. -/
def rMul2CyclicShiftGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.Word.adjacentShiftRightGates
    (rCoeffValueWord n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)

theorem uDiv2CyclicShiftGates_length (n counterWidth : Nat) :
    (uDiv2CyclicShiftGates n counterWidth).length = 3 * (n - 1) :=
  adjacentShiftLeftGates_length
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)

theorem vDiv2CyclicShiftGates_length (n counterWidth : Nat) :
    (vDiv2CyclicShiftGates n counterWidth).length = 3 * (n - 1) :=
  adjacentShiftLeftGates_length
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)

theorem sMul2CyclicShiftGates_length (n counterWidth : Nat) :
    (sMul2CyclicShiftGates n counterWidth).length = 3 * n := by
  simpa only [sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.length_reverse,
    Nat.add_sub_cancel] using
    adjacentShiftLeftGates_length
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth)

theorem rMul2CyclicShiftGates_length (n counterWidth : Nat) :
    (rMul2CyclicShiftGates n counterWidth).length = 3 * n := by
  simpa only [rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.length_reverse,
    Nat.add_sub_cancel] using
    adjacentShiftLeftGates_length
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth)

theorem uDiv2CyclicShiftGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((uDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 :=
  adjacentShiftLeftGates_xMultiplicity_sum
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)

theorem vDiv2CyclicShiftGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((vDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 :=
  adjacentShiftLeftGates_xMultiplicity_sum
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)

theorem sMul2CyclicShiftGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((sMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    adjacentShiftLeftGates_xMultiplicity_sum
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth)

theorem rMul2CyclicShiftGates_xMultiplicity_sum (n counterWidth : Nat) :
    ((rMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    adjacentShiftLeftGates_xMultiplicity_sum
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth)

theorem uDiv2CyclicShiftGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((uDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * (n - 1) :=
  adjacentShiftLeftGates_cnotMultiplicity_sum
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)

theorem vDiv2CyclicShiftGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((vDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * (n - 1) :=
  adjacentShiftLeftGates_cnotMultiplicity_sum
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)

theorem sMul2CyclicShiftGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((sMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * n := by
  simpa only [sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse, Nat.add_sub_cancel] using
    adjacentShiftLeftGates_cnotMultiplicity_sum
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth)

theorem rMul2CyclicShiftGates_cnotMultiplicity_sum (n counterWidth : Nat) :
    ((rMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * n := by
  simpa only [rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse, Nat.add_sub_cancel] using
    adjacentShiftLeftGates_cnotMultiplicity_sum
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth)

theorem uDiv2CyclicShiftGates_toffoliMultiplicity_sum (n counterWidth : Nat) :
    ((uDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 :=
  adjacentShiftLeftGates_toffoliMultiplicity_sum
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)

theorem vDiv2CyclicShiftGates_toffoliMultiplicity_sum (n counterWidth : Nat) :
    ((vDiv2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 :=
  adjacentShiftLeftGates_toffoliMultiplicity_sum
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)

theorem sMul2CyclicShiftGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((sMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simpa only [sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    adjacentShiftLeftGates_toffoliMultiplicity_sum
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth)

theorem rMul2CyclicShiftGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((rMul2CyclicShiftGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simpa only [rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    adjacentShiftLeftGates_toffoliMultiplicity_sum
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth)

/-- Folded compact `u / 2` cyclic-shift action. -/
def uDiv2CyclicShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (uDiv2CyclicShiftGates n counterWidth)

/-- Folded compact `v / 2` cyclic-shift action. -/
def vDiv2CyclicShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (vDiv2CyclicShiftGates n counterWidth)

/-- Folded compact `s * 2` cyclic-shift action. -/
def sMul2CyclicShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (sMul2CyclicShiftGates n counterWidth)

/-- Folded compact `r * 2` cyclic-shift action. -/
def rMul2CyclicShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (rMul2CyclicShiftGates n counterWidth)

/-- Physical compact `u / 2` cyclic-shift program. -/
def uDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uDiv2CyclicShiftGates n counterWidth)

/-- Physical compact `v / 2` cyclic-shift program. -/
def vDiv2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vDiv2CyclicShiftGates n counterWidth)

/-- Physical compact `s * 2` cyclic-shift program. -/
def sMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (sMul2CyclicShiftGates n counterWidth)

/-- Physical compact `r * 2` cyclic-shift program. -/
def rMul2CyclicShiftProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (rMul2CyclicShiftGates n counterWidth)

theorem uDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (uDiv2CyclicShiftProgram n counterWidth)
      (uDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uDiv2CyclicShiftGates n counterWidth)

theorem vDiv2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (vDiv2CyclicShiftProgram n counterWidth)
      (vDiv2CyclicShiftStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vDiv2CyclicShiftGates n counterWidth)

theorem sMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (sMul2CyclicShiftProgram n counterWidth)
      (sMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (sMul2CyclicShiftGates n counterWidth)

theorem rMul2CyclicShift_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (rMul2CyclicShiftProgram n counterWidth)
      (rMul2CyclicShiftStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (rMul2CyclicShiftGates n counterWidth)

/-- The compact `u / 2` atom exposes the exact cyclic source permutation. -/
theorem uDiv2CyclicShiftStep_get_uBit_source
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    ((uValueWord n counterWidth).bit target).get
        (uDiv2CyclicShiftStep n counterWidth x) =
      ((uValueWord n counterWidth).bit
        (EncodedBit.Word.adjacentSwapIndexPerm n
          (List.ofFn fun i : Fin (n - 1) => i) target)).get x := by
  simpa [uDiv2CyclicShiftStep, uDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_indexPerm
      (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)
      target x

/-- The compact `v / 2` atom exposes the exact cyclic source permutation. -/
theorem vDiv2CyclicShiftStep_get_vBit_source
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    ((vValueWord n counterWidth).bit target).get
        (vDiv2CyclicShiftStep n counterWidth x) =
      ((vValueWord n counterWidth).bit
        (EncodedBit.Word.adjacentSwapIndexPerm n
          (List.ofFn fun i : Fin (n - 1) => i) target)).get x := by
  simpa [vDiv2CyclicShiftStep, vDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_indexPerm
      (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)
      target x

/-- The compact `s * 2` atom exposes the exact inverse cyclic permutation. -/
theorem sMul2CyclicShiftStep_get_sCoeffBit_source
    (n counterWidth : Nat) (target : Fin (n + 1))
    (x : Registers n counterWidth) :
    ((sCoeffValueWord n counterWidth).bit target).get
        (sMul2CyclicShiftStep n counterWidth x) =
      ((sCoeffValueWord n counterWidth).bit
        ((EncodedBit.Word.adjacentSwapIndexPerm (n + 1)
          (List.ofFn fun i : Fin ((n + 1) - 1) => i)).symm target)).get x := by
  simpa [sMul2CyclicShiftStep, sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_indexPerm
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth) target x

/-- The compact `r * 2` atom exposes the exact inverse cyclic permutation. -/
theorem rMul2CyclicShiftStep_get_rCoeffBit_source
    (n counterWidth : Nat) (target : Fin (n + 1))
    (x : Registers n counterWidth) :
    ((rCoeffValueWord n counterWidth).bit target).get
        (rMul2CyclicShiftStep n counterWidth x) =
      ((rCoeffValueWord n counterWidth).bit
        ((EncodedBit.Word.adjacentSwapIndexPerm (n + 1)
          (List.ofFn fun i : Fin ((n + 1) - 1) => i)).symm target)).get x := by
  simpa [rMul2CyclicShiftStep, rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_indexPerm
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth) target x

/-- Every non-last compact `u / 2` target bit reads the next source bit. -/
theorem uDiv2CyclicShiftStep_get_uBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : Registers tail.succ counterWidth) :
    ((uValueWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (uDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((uValueWord tail.succ counterWidth).bit target.succ).get x := by
  simpa [uDiv2CyclicShiftStep, uDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_castSucc
      (uValueWord tail.succ counterWidth)
      (uValueWord_bit_wire_ne tail.succ counterWidth) target x

/-- The last compact `u / 2` target bit wraps from source bit zero. -/
theorem uDiv2CyclicShiftStep_get_uBit_wrap
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    ((uValueWord tail.succ counterWidth).bit (Fin.last tail)).get
        (uDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((uValueWord tail.succ counterWidth).bit 0).get x := by
  simpa [uDiv2CyclicShiftStep, uDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_last
      (uValueWord tail.succ counterWidth)
      (uValueWord_bit_wire_ne tail.succ counterWidth) x

/-- Every non-last compact `v / 2` target bit reads the next source bit. -/
theorem vDiv2CyclicShiftStep_get_vBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : Registers tail.succ counterWidth) :
    ((vValueWord tail.succ counterWidth).bit (Fin.castSucc target)).get
        (vDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((vValueWord tail.succ counterWidth).bit target.succ).get x := by
  simpa [vDiv2CyclicShiftStep, vDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_castSucc
      (vValueWord tail.succ counterWidth)
      (vValueWord_bit_wire_ne tail.succ counterWidth) target x

/-- The last compact `v / 2` target bit wraps from source bit zero. -/
theorem vDiv2CyclicShiftStep_get_vBit_wrap
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    ((vValueWord tail.succ counterWidth).bit (Fin.last tail)).get
        (vDiv2CyclicShiftStep tail.succ counterWidth x) =
      ((vValueWord tail.succ counterWidth).bit 0).get x := by
  simpa [vDiv2CyclicShiftStep, vDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep] using
    EncodedBit.Word.adjacentShiftLeftStep_get_last
      (vValueWord tail.succ counterWidth)
      (vValueWord_bit_wire_ne tail.succ counterWidth) x

/-- Compact `s * 2` target bit zero wraps from the top source bit. -/
theorem sMul2CyclicShiftStep_get_sCoeffBit_zero
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    ((sCoeffValueWord n counterWidth).bit 0).get
        (sMul2CyclicShiftStep n counterWidth x) =
      ((sCoeffValueWord n counterWidth).bit (Fin.last n)).get x := by
  simpa [sMul2CyclicShiftStep, sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_zero
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth) x

/-- Each successor compact `s * 2` bit reads the preceding source bit. -/
theorem sMul2CyclicShiftStep_get_sCoeffBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    ((sCoeffValueWord n counterWidth).bit target.succ).get
        (sMul2CyclicShiftStep n counterWidth x) =
      ((sCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get x := by
  simpa [sMul2CyclicShiftStep, sMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_succ
      (sCoeffValueWord n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth) target x

/-- Compact `r * 2` target bit zero wraps from the top source bit. -/
theorem rMul2CyclicShiftStep_get_rCoeffBit_zero
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    ((rCoeffValueWord n counterWidth).bit 0).get
        (rMul2CyclicShiftStep n counterWidth x) =
      ((rCoeffValueWord n counterWidth).bit (Fin.last n)).get x := by
  simpa [rMul2CyclicShiftStep, rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_zero
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth) x

/-- Each successor compact `r * 2` bit reads the preceding source bit. -/
theorem rMul2CyclicShiftStep_get_rCoeffBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    ((rCoeffValueWord n counterWidth).bit target.succ).get
        (rMul2CyclicShiftStep n counterWidth x) =
      ((rCoeffValueWord n counterWidth).bit (Fin.castSucc target)).get x := by
  simpa [rMul2CyclicShiftStep, rMul2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftRightStep] using
    EncodedBit.Word.adjacentShiftRightStep_get_succ
      (rCoeffValueWord n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth) target x

/-- `testBit` form of the compact `u / 2` shift away from the cyclic wrap
position. -/
theorem uDiv2CyclicShiftStep_get_u_testBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : Registers tail.succ counterWidth) :
    (uDiv2CyclicShiftStep tail.succ counterWidth x).core.u.val.testBit
        (Fin.castSucc target).val =
      x.core.u.val.testBit target.succ.val := by
  simpa [uValueWord_get, Fin.val_ofNat] using
    uDiv2CyclicShiftStep_get_uBit_next tail counterWidth target x

/-- `testBit` form of the compact `u / 2` cyclic wrap. -/
theorem uDiv2CyclicShiftStep_get_u_testBit_wrap
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (uDiv2CyclicShiftStep tail.succ counterWidth x).core.u.val.testBit
        (Fin.last tail).val =
      x.core.u.val.testBit (0 : Fin tail.succ).val := by
  simpa only [uValueWord_get] using
    uDiv2CyclicShiftStep_get_uBit_wrap tail counterWidth x

/-- `testBit` form of the compact `v / 2` shift away from the cyclic wrap
position. -/
theorem vDiv2CyclicShiftStep_get_v_testBit_next
    (tail counterWidth : Nat) (target : Fin tail)
    (x : Registers tail.succ counterWidth) :
    (vDiv2CyclicShiftStep tail.succ counterWidth x).core.v.val.testBit
        (Fin.castSucc target).val =
      x.core.v.val.testBit target.succ.val := by
  simpa [vValueWord_get, Fin.val_ofNat] using
    vDiv2CyclicShiftStep_get_vBit_next tail counterWidth target x

/-- `testBit` form of the compact `v / 2` cyclic wrap. -/
theorem vDiv2CyclicShiftStep_get_v_testBit_wrap
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (vDiv2CyclicShiftStep tail.succ counterWidth x).core.v.val.testBit
        (Fin.last tail).val =
      x.core.v.val.testBit (0 : Fin tail.succ).val := by
  simpa only [vValueWord_get] using
    vDiv2CyclicShiftStep_get_vBit_wrap tail counterWidth x

/-- `testBit` form of the compact `s * 2` low cyclic wrap. -/
theorem sMul2CyclicShiftStep_get_sCoeff_testBit_zero
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (sMul2CyclicShiftStep n counterWidth x).core.sCoeff.val.testBit
        (0 : Fin (n + 1)).val =
      x.core.sCoeff.val.testBit (Fin.last n).val := by
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using
    sMul2CyclicShiftStep_get_sCoeffBit_zero n counterWidth x

/-- `testBit` form of each successor compact `s * 2` bit. -/
theorem sMul2CyclicShiftStep_get_sCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    (sMul2CyclicShiftStep n counterWidth x).core.sCoeff.val.testBit
        target.succ.val =
      x.core.sCoeff.val.testBit (Fin.castSucc target).val := by
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using
    sMul2CyclicShiftStep_get_sCoeffBit_succ n counterWidth target x

/-- `testBit` form of the compact `r * 2` low cyclic wrap. -/
theorem rMul2CyclicShiftStep_get_rCoeff_testBit_zero
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (rMul2CyclicShiftStep n counterWidth x).core.rCoeff.val.testBit
        (0 : Fin (n + 1)).val =
      x.core.rCoeff.val.testBit (Fin.last n).val := by
  simpa only [rCoeffValueWord, rCoeffValueBit_get] using
    rMul2CyclicShiftStep_get_rCoeffBit_zero n counterWidth x

/-- `testBit` form of each successor compact `r * 2` bit. -/
theorem rMul2CyclicShiftStep_get_rCoeff_testBit_succ
    (n counterWidth : Nat) (target : Fin n)
    (x : Registers n counterWidth) :
    (rMul2CyclicShiftStep n counterWidth x).core.rCoeff.val.testBit
        target.succ.val =
      x.core.rCoeff.val.testBit (Fin.castSucc target).val := by
  simpa only [rCoeffValueWord, rCoeffValueBit_get] using
    rMul2CyclicShiftStep_get_rCoeffBit_succ n counterWidth target x

/-- On an even compact source word, the cyclic `u` shift is natural
halving. -/
theorem uDiv2CyclicShiftStep_get_u_wordHalf_of_lsb_false
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hlsb : x.core.u.val.testBit (0 : Nat) = false) :
    (uDiv2CyclicShiftStep tail.succ counterWidth x).core.u =
      wordHalf tail.succ x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.lastCases ?last ?cast bit
  · have hwrap :=
      uDiv2CyclicShiftStep_get_u_testBit_wrap tail counterWidth x
    have hhigh :
        x.core.u.val.testBit ((Fin.last tail).val + 1) = false := by
      have hpow : 2 ^ tail.succ <= 2 ^ ((Fin.last tail).val + 1) := by
        simp
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.core.u.isLt hpow)
    rw [wordHalf_val, Nat.testBit_div_two]
    calc
      (uDiv2CyclicShiftStep tail.succ counterWidth x).core.u.val.testBit
          (Fin.last tail).val =
        x.core.u.val.testBit (0 : Fin tail.succ).val := hwrap
      _ = false := by simpa [Fin.val_ofNat] using hlsb
      _ = x.core.u.val.testBit ((Fin.last tail).val + 1) := hhigh.symm
  · intro target
    have hnext :=
      uDiv2CyclicShiftStep_get_u_testBit_next tail counterWidth target x
    rw [wordHalf_val, Nat.testBit_div_two]
    simpa using hnext

/-- On an even compact source word, the cyclic `v` shift is natural
halving. -/
theorem vDiv2CyclicShiftStep_get_v_wordHalf_of_lsb_false
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hlsb : x.core.v.val.testBit (0 : Nat) = false) :
    (vDiv2CyclicShiftStep tail.succ counterWidth x).core.v =
      wordHalf tail.succ x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.lastCases ?last ?cast bit
  · have hwrap :=
      vDiv2CyclicShiftStep_get_v_testBit_wrap tail counterWidth x
    have hhigh :
        x.core.v.val.testBit ((Fin.last tail).val + 1) = false := by
      have hpow : 2 ^ tail.succ <= 2 ^ ((Fin.last tail).val + 1) := by
        simp
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.core.v.isLt hpow)
    rw [wordHalf_val, Nat.testBit_div_two]
    calc
      (vDiv2CyclicShiftStep tail.succ counterWidth x).core.v.val.testBit
          (Fin.last tail).val =
        x.core.v.val.testBit (0 : Fin tail.succ).val := hwrap
      _ = false := by simpa [Fin.val_ofNat] using hlsb
      _ = x.core.v.val.testBit ((Fin.last tail).val + 1) := hhigh.symm
  · intro target
    have hnext :=
      vDiv2CyclicShiftStep_get_v_testBit_next tail counterWidth target x
    rw [wordHalf_val, Nat.testBit_div_two]
    simpa using hnext

/-- When the compact `s` top bit is zero, its cyclic left shift is
width-preserving natural doubling. -/
theorem sMul2CyclicShiftStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hmsb : x.core.sCoeff.val.testBit (Fin.last n).val = false) :
    (sMul2CyclicShiftStep n counterWidth x).core.sCoeff =
      wordDouble (n + 1) x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      sMul2CyclicShiftStep_get_sCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      sMul2CyclicShiftStep_get_sCoeff_testBit_succ n counterWidth target x
    rw [hsucc, wordDouble_testBit]
    simp

/-- When the compact `r` top bit is zero, its cyclic left shift is
width-preserving natural doubling. -/
theorem rMul2CyclicShiftStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hmsb : x.core.rCoeff.val.testBit (Fin.last n).val = false) :
    (rMul2CyclicShiftStep n counterWidth x).core.rCoeff =
      wordDouble (n + 1) x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  refine Fin.cases ?zero ?succ bit
  · have hzero :=
      rMul2CyclicShiftStep_get_rCoeff_testBit_zero n counterWidth x
    rw [hzero, hmsb, wordDouble_testBit]
    simp
  · intro target
    have hsucc :=
      rMul2CyclicShiftStep_get_rCoeff_testBit_succ n counterWidth target x
    rw [hsucc, wordDouble_testBit]
    simp

/-! ### Compact branch-controlled shift dispatch -/

private theorem scratchABit_uValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (scratchABit n counterWidth).wire ≠
      ((uValueWord n counterWidth).bit bit).wire := by
  simpa [scratchABit, uValueWord, RegisterBits.uValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

private theorem scratchABit_vValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (scratchABit n counterWidth).wire ≠
      ((vValueWord n counterWidth).bit bit).wire := by
  simpa [scratchABit, vValueWord, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

private theorem scratchABit_sCoeffValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (scratchABit n counterWidth).wire ≠
      ((sCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [scratchABit, sCoeffValueWord, sCoeffValueBit,
    RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

private theorem scratchABit_rCoeffValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (scratchABit n counterWidth).wire ≠
      ((rCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [scratchABit, rCoeffValueWord, rCoeffValueBit,
    RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)))

private theorem activeBit_vValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (activeBit n counterWidth).wire ≠
      ((vValueWord n counterWidth).bit bit).wire := by
  simpa [activeBit, vValueWord, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))

private theorem activeBit_rCoeffValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (activeBit n counterWidth).wire ≠
      ((rCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [activeBit, rCoeffValueWord, rCoeffValueBit,
    RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))

private theorem activeBit_uValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin n) :
    (activeBit n counterWidth).wire ≠
      ((uValueWord n counterWidth).bit bit).wire := by
  simpa [activeBit, uValueWord, RegisterBits.uValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))

private theorem activeBit_sCoeffValueWord_bit_wire_ne
    (n counterWidth : Nat) (bit : Fin (n + 1)) :
    (activeBit n counterWidth).wire ≠
      ((sCoeffValueWord n counterWidth).bit bit).wire := by
  simpa [activeBit, sCoeffValueWord, sCoeffValueBit,
    RegisterBits.sCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))

/-- Auxiliary-controlled `u/s` shift group. -/
def auxUDiv2ThenSMul2Step (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x =>
    EncodedBit.Word.controlledAdjacentShiftRightStep
      (scratchABit n counterWidth) (sCoeffValueWord n counterWidth)
      (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth)
      (EncodedBit.Word.controlledAdjacentShiftLeftStep
        (scratchABit n counterWidth) (uValueWord n counterWidth)
        (scratchABit_uValueWord_bit_wire_ne n counterWidth)
        (uValueWord_bit_wire_ne n counterWidth) x)

/-- Active-controlled `v/r` shift group. -/
def activeVDiv2ThenRMul2Step (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x =>
    EncodedBit.Word.controlledAdjacentShiftRightStep
      (activeBit n counterWidth) (rCoeffValueWord n counterWidth)
      (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth)
      (EncodedBit.Word.controlledAdjacentShiftLeftStep
        (activeBit n counterWidth) (vValueWord n counterWidth)
        (activeBit_vValueWord_bit_wire_ne n counterWidth)
        (vValueWord_bit_wire_ne n counterWidth) x)

/-- Auxiliary-controlled inverse of the `v/r` shift group. -/
def auxVDiv2ThenRMul2InverseShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x =>
    EncodedBit.Word.controlledAdjacentShiftRightStep
      (scratchABit n counterWidth) (vValueWord n counterWidth)
      (scratchABit_vValueWord_bit_wire_ne n counterWidth)
      (vValueWord_bit_wire_ne n counterWidth)
      (EncodedBit.Word.controlledAdjacentShiftLeftStep
        (scratchABit n counterWidth) (rCoeffValueWord n counterWidth)
        (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
        (rCoeffValueWord_bit_wire_ne n counterWidth) x)

/-- Uncontrolled compact `u/s` shift group. -/
def uDiv2ThenSMul2Step (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x => sMul2CyclicShiftStep n counterWidth
    (uDiv2CyclicShiftStep n counterWidth x)

/-- Uncontrolled compact `v/r` shift group. -/
def vDiv2ThenRMul2Step (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x => rMul2CyclicShiftStep n counterWidth
    (vDiv2CyclicShiftStep n counterWidth x)

/-- Uncontrolled inverse of the compact `v/r` shift group. -/
def vDiv2ThenRMul2InverseShiftStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x =>
    EncodedBit.Word.adjacentShiftRightStep
      (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)
      (EncodedBit.Word.adjacentShiftLeftStep
        (rCoeffValueWord n counterWidth)
        (rCoeffValueWord_bit_wire_ne n counterWidth) x)

/-- The compact `u` source shift leaves the whole `s` coefficient word
unchanged. -/
theorem uDiv2CyclicShiftStep_get_sCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (uDiv2CyclicShiftStep n counterWidth x).core.sCoeff = x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentShiftLeftStep_get_observed_of_word_ne
    ((sCoeffValueWord n counterWidth).bit bit)
    (uValueWord n counterWidth) (uValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [uValueWord, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire bit))) x
  simpa [uDiv2CyclicShiftStep, uDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep, sCoeffValueWord] using h

/-- The compact `v` source shift leaves the whole `r` coefficient word
unchanged. -/
theorem vDiv2CyclicShiftStep_get_rCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (vDiv2CyclicShiftStep n counterWidth x).core.rCoeff = x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentShiftLeftStep_get_observed_of_word_ne
    ((rCoeffValueWord n counterWidth).bit bit)
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [vValueWord, rCoeffValueWord, rCoeffValueBit,
        RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire bit))) x
  simpa [vDiv2CyclicShiftStep, vDiv2CyclicShiftGates,
    EncodedBit.Word.adjacentShiftLeftStep, rCoeffValueWord] using h

/-- Arithmetic endpoint of the compact paired `u / 2`, `s * 2` shift. -/
theorem uDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hlsb : x.core.u.val.testBit (0 : Nat) = false) :
    (uDiv2ThenSMul2Step tail.succ counterWidth x).core.u =
      wordHalf tail.succ x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have hpres := adjacentShiftRightStep_get_observed_of_word_ne
    ((uValueWord tail.succ counterWidth).bit bit)
    (sCoeffValueWord tail.succ counterWidth)
    (sCoeffValueWord_bit_wire_ne tail.succ counterWidth)
    (fun coeffBit => by
      simpa [uValueWord, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne tail.succ counterWidth
          (RegisterBits.u_sCoeff_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire coeffBit))).symm)
    (uDiv2CyclicShiftStep tail.succ counterWidth x)
  have hhalf := congrArg (fun word => word.val.testBit bit.val)
    (uDiv2CyclicShiftStep_get_u_wordHalf_of_lsb_false
      tail counterWidth x hlsb)
  rw [uDiv2ThenSMul2Step]
  calc
    (sMul2CyclicShiftStep tail.succ counterWidth
        (uDiv2CyclicShiftStep tail.succ counterWidth x)).core.u.val.testBit
        bit.val =
      (uDiv2CyclicShiftStep tail.succ counterWidth x).core.u.val.testBit
        bit.val := by
          simpa [sMul2CyclicShiftStep, sMul2CyclicShiftGates,
            EncodedBit.Word.adjacentShiftRightStep, uValueWord_get] using hpres
    _ = (wordHalf tail.succ x.core.u).val.testBit bit.val := hhalf

/-- Arithmetic endpoint of the compact paired `v / 2`, `r * 2` shift. -/
theorem vDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hlsb : x.core.v.val.testBit (0 : Nat) = false) :
    (vDiv2ThenRMul2Step tail.succ counterWidth x).core.v =
      wordHalf tail.succ x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have hpres := adjacentShiftRightStep_get_observed_of_word_ne
    ((vValueWord tail.succ counterWidth).bit bit)
    (rCoeffValueWord tail.succ counterWidth)
    (rCoeffValueWord_bit_wire_ne tail.succ counterWidth)
    (fun coeffBit => by
      simpa [vValueWord, rCoeffValueWord, rCoeffValueBit,
        RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne tail.succ counterWidth
          (RegisterBits.v_rCoeff_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire coeffBit))).symm)
    (vDiv2CyclicShiftStep tail.succ counterWidth x)
  have hhalf := congrArg (fun word => word.val.testBit bit.val)
    (vDiv2CyclicShiftStep_get_v_wordHalf_of_lsb_false
      tail counterWidth x hlsb)
  rw [vDiv2ThenRMul2Step]
  calc
    (rMul2CyclicShiftStep tail.succ counterWidth
        (vDiv2CyclicShiftStep tail.succ counterWidth x)).core.v.val.testBit
        bit.val =
      (vDiv2CyclicShiftStep tail.succ counterWidth x).core.v.val.testBit
        bit.val := by
          simpa [rMul2CyclicShiftStep, rMul2CyclicShiftGates,
            EncodedBit.Word.adjacentShiftRightStep, vValueWord_get] using hpres
    _ = (wordHalf tail.succ x.core.v).val.testBit bit.val := hhalf

/-- Arithmetic coefficient endpoint of the compact paired `u/s` shift. -/
theorem uDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hmsb : x.core.sCoeff.val.testBit (Fin.last n).val = false) :
    (uDiv2ThenSMul2Step n counterWidth x).core.sCoeff =
      wordDouble (n + 1) x.core.sCoeff := by
  let shifted := uDiv2CyclicShiftStep n counterWidth x
  have hs : shifted.core.sCoeff = x.core.sCoeff := by
    exact uDiv2CyclicShiftStep_get_sCoeff n counterWidth x
  have hshiftedMsb :
      shifted.core.sCoeff.val.testBit (Fin.last n).val = false := by
    rw [hs]
    exact hmsb
  change (sMul2CyclicShiftStep n counterWidth shifted).core.sCoeff = _
  rw [sMul2CyclicShiftStep_get_sCoeff_wordDouble_of_msb_false
    n counterWidth shifted hshiftedMsb, hs]

/-- Arithmetic coefficient endpoint of the compact paired `v/r` shift. -/
theorem vDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hmsb : x.core.rCoeff.val.testBit (Fin.last n).val = false) :
    (vDiv2ThenRMul2Step n counterWidth x).core.rCoeff =
      wordDouble (n + 1) x.core.rCoeff := by
  let shifted := vDiv2CyclicShiftStep n counterWidth x
  have hr : shifted.core.rCoeff = x.core.rCoeff := by
    exact vDiv2CyclicShiftStep_get_rCoeff n counterWidth x
  have hshiftedMsb :
      shifted.core.rCoeff.val.testBit (Fin.last n).val = false := by
    rw [hr]
    exact hmsb
  change (rMul2CyclicShiftStep n counterWidth shifted).core.rCoeff = _
  rw [rMul2CyclicShiftStep_get_rCoeff_wordDouble_of_msb_false
    n counterWidth shifted hshiftedMsb, hr]

private theorem adjacentLeftThenRightStep_get_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {leftWidth rightWidth : Nat}
    (observed : EncodedBit encoding)
    (left : EncodedBit.Word encoding leftWidth)
    (right : EncodedBit.Word encoding rightWidth)
    (hleft : ∀ i j, i ≠ j → (left.bit i).wire ≠ (left.bit j).wire)
    (hright : ∀ i j, i ≠ j → (right.bit i).wire ≠ (right.bit j).wire)
    (hleftObserved : ∀ i, (left.bit i).wire ≠ observed.wire)
    (hrightObserved : ∀ i, (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.adjacentShiftRightStep right hright
          (EncodedBit.Word.adjacentShiftLeftStep left hleft x)) =
      observed.get x := by
  rw [adjacentShiftRightStep_get_observed_of_word_ne
    observed right hright hrightObserved]
  exact adjacentShiftLeftStep_get_observed_of_word_ne
    observed left hleft hleftObserved x

/-- The compact paired `u/s` shift preserves the untouched `v` word. -/
theorem uDiv2ThenSMul2Step_core_v
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (uDiv2ThenSMul2Step n counterWidth x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentLeftThenRightStep_get_observed
    ((vValueWord n counterWidth).bit bit)
    (uValueWord n counterWidth) (sCoeffValueWord n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [uValueWord, vValueWord, RegisterBits.uValueBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire bit)))
    (fun coeffBit => by
      simpa [sCoeffValueWord, sCoeffValueBit, vValueWord,
        RegisterBits.sCoeffValueBit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire coeffBit))).symm) x
  simpa [uDiv2ThenSMul2Step, uDiv2CyclicShiftStep,
    uDiv2CyclicShiftGates, sMul2CyclicShiftStep,
    sMul2CyclicShiftGates, EncodedBit.Word.adjacentShiftLeftStep,
    EncodedBit.Word.adjacentShiftRightStep] using h

/-- The compact paired `u/s` shift preserves the untouched `r` coefficient. -/
theorem uDiv2ThenSMul2Step_core_rCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (uDiv2ThenSMul2Step n counterWidth x).core.rCoeff = x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentLeftThenRightStep_get_observed
    ((rCoeffValueWord n counterWidth).bit bit)
    (uValueWord n counterWidth) (sCoeffValueWord n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [uValueWord, rCoeffValueWord, rCoeffValueBit,
        RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire bit)))
    (fun coeffBit => by
      simpa [sCoeffValueWord, sCoeffValueBit, rCoeffValueWord,
        rCoeffValueBit, RegisterBits.sCoeffValueBit,
        RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire coeffBit)
            (WireAddress.littleEndianWire bit))) x
  simpa [uDiv2ThenSMul2Step, uDiv2CyclicShiftStep,
    uDiv2CyclicShiftGates, sMul2CyclicShiftStep,
    sMul2CyclicShiftGates, EncodedBit.Word.adjacentShiftLeftStep,
    EncodedBit.Word.adjacentShiftRightStep, rCoeffValueWord,
    rCoeffValueBit_get] using h

/-- The compact paired `v/r` shift preserves the untouched `u` word. -/
theorem vDiv2ThenRMul2Step_core_u
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (vDiv2ThenRMul2Step n counterWidth x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentLeftThenRightStep_get_observed
    ((uValueWord n counterWidth).bit bit)
    (vValueWord n counterWidth) (rCoeffValueWord n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [uValueWord, vValueWord, RegisterBits.uValueBit,
        RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire sourceBit))).symm)
    (fun coeffBit => by
      simpa [rCoeffValueWord, rCoeffValueBit, uValueWord,
        RegisterBits.rCoeffValueBit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire coeffBit))).symm) x
  simpa [vDiv2ThenRMul2Step, vDiv2CyclicShiftStep,
    vDiv2CyclicShiftGates, rMul2CyclicShiftStep,
    rMul2CyclicShiftGates, EncodedBit.Word.adjacentShiftLeftStep,
    EncodedBit.Word.adjacentShiftRightStep] using h

/-- The compact paired `v/r` shift preserves the untouched `s` coefficient. -/
theorem vDiv2ThenRMul2Step_core_sCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (vDiv2ThenRMul2Step n counterWidth x).core.sCoeff = x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := adjacentLeftThenRightStep_get_observed
    ((sCoeffValueWord n counterWidth).bit bit)
    (vValueWord n counterWidth) (rCoeffValueWord n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (fun sourceBit => by
      simpa [vValueWord, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire sourceBit)
            (WireAddress.littleEndianWire bit)))
    (fun coeffBit => by
      simpa [rCoeffValueWord, rCoeffValueBit, sCoeffValueWord,
        sCoeffValueBit, RegisterBits.rCoeffValueBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire coeffBit))).symm) x
  simpa [vDiv2ThenRMul2Step, vDiv2CyclicShiftStep,
    vDiv2CyclicShiftGates, rMul2CyclicShiftStep,
    rMul2CyclicShiftGates, EncodedBit.Word.adjacentShiftLeftStep,
    EncodedBit.Word.adjacentShiftRightStep, sCoeffValueWord,
    sCoeffValueBit_get] using h

/-- The compact `u/s` shift group leaves every `r` coefficient bit
unchanged. -/
theorem uDiv2ThenSMul2Step_get_rCoeffValueBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth bit).get
        (uDiv2ThenSMul2Step n counterWidth x) =
      (rCoeffValueBit n counterWidth bit).get x := by
  unfold uDiv2ThenSMul2Step sMul2CyclicShiftStep sMul2CyclicShiftGates
    uDiv2CyclicShiftStep uDiv2CyclicShiftGates
  change (rCoeffValueBit n counterWidth bit).get
      (EncodedBit.Word.adjacentShiftRightStep
        (sCoeffValueWord n counterWidth)
        (sCoeffValueWord_bit_wire_ne n counterWidth)
        (EncodedBit.Word.adjacentShiftLeftStep
          (uValueWord n counterWidth)
          (uValueWord_bit_wire_ne n counterWidth) x)) = _
  rw [adjacentShiftRightStep_get_observed_of_word_ne
    (rCoeffValueBit n counterWidth bit) (sCoeffValueWord n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)]
  · exact adjacentShiftLeftStep_get_observed_of_word_ne
      (rCoeffValueBit n counterWidth bit) (uValueWord n counterWidth)
      (uValueWord_bit_wire_ne n counterWidth)
      (fun i => by
        simpa [uValueWord, rCoeffValueBit, rCoeffValueWord,
          RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
          liftCoreBit_wire_ne n counterWidth
            (RegisterBits.u_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire i)
              (WireAddress.littleEndianWire bit))) x
  · intro i
    simpa [sCoeffValueWord, sCoeffValueBit, rCoeffValueBit,
      RegisterBits.sCoeffValueBit, RegisterBits.rCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.sCoeff_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)
          (WireAddress.littleEndianWire bit))

/-- The compact `v/r` shift exposes the old coefficient top bit at the new
low `r` bit. -/
theorem vDiv2ThenRMul2Step_get_rCoeffValueBit_zero
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth 0).get
        (vDiv2ThenRMul2Step n counterWidth x) =
      (rCoeffValueBit n counterWidth (Fin.last n)).get x := by
  unfold vDiv2ThenRMul2Step
  rw [show rCoeffValueBit n counterWidth 0 =
      (rCoeffValueWord n counterWidth).bit 0 by rfl,
    rMul2CyclicShiftStep_get_rCoeffBit_zero]
  unfold vDiv2CyclicShiftStep vDiv2CyclicShiftGates
  change (rCoeffValueBit n counterWidth (Fin.last n)).get
      (EncodedBit.Word.adjacentShiftLeftStep
        (vValueWord n counterWidth)
        (vValueWord_bit_wire_ne n counterWidth) x) = _
  exact adjacentShiftLeftStep_get_observed_of_word_ne
    (rCoeffValueBit n counterWidth (Fin.last n))
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)
    (fun i => by
      simpa [vValueWord, rCoeffValueBit, RegisterBits.vValueBit,
        RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire i)
            (WireAddress.littleEndianWire (Fin.last n)))) x

private theorem controlledLeftThenRightStep_get_observed
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {leftWidth rightWidth : Nat}
    (control observed : EncodedBit encoding)
    (left : EncodedBit.Word encoding leftWidth)
    (right : EncodedBit.Word encoding rightWidth)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleft : ∀ i j, i ≠ j → (left.bit i).wire ≠ (left.bit j).wire)
    (hright : ∀ i j, i ≠ j → (right.bit i).wire ≠ (right.bit j).wire)
    (hleftObserved : ∀ i, (left.bit i).wire ≠ observed.wire)
    (hrightObserved : ∀ i, (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (EncodedBit.Word.controlledAdjacentShiftRightStep
          control right hcontrolRight hright
          (EncodedBit.Word.controlledAdjacentShiftLeftStep
            control left hcontrolLeft hleft x)) =
      observed.get x := by
  rw [controlledAdjacentShiftRightStep_get_observed_of_word_ne
    control observed right hcontrolRight hright hrightObserved]
  exact controlledAdjacentShiftLeftStep_get_observed_of_word_ne
    control observed left hcontrolLeft hleft hleftObserved x

private theorem controlledLeftThenRightStep_eq_uncontrolled_of_true
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {leftWidth rightWidth : Nat}
    (control : EncodedBit encoding)
    (left : EncodedBit.Word encoding leftWidth)
    (right : EncodedBit.Word encoding rightWidth)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleft : ∀ i j, i ≠ j → (left.bit i).wire ≠ (left.bit j).wire)
    (hright : ∀ i j, i ≠ j → (right.bit i).wire ≠ (right.bit j).wire)
    (x : Data) (hcontrol : control.get x = true) :
    EncodedBit.Word.controlledAdjacentShiftRightStep
        control right hcontrolRight hright
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          control left hcontrolLeft hleft x) =
      EncodedBit.Word.adjacentShiftRightStep right hright
        (EncodedBit.Word.adjacentShiftLeftStep left hleft x) := by
  have hafter :
      control.get
          (EncodedBit.Word.controlledAdjacentShiftLeftStep
            control left hcontrolLeft hleft x) = true := by
    rw [controlledAdjacentShiftLeftStep_get_observed_of_word_ne
      control control left hcontrolLeft hleft
      (fun i => Ne.symm (hcontrolLeft i))]
    exact hcontrol
  rw [controlledAdjacentShiftRightStep_eq_adjacentShiftRightStep_of_control_true
    control right hcontrolRight hright _ hafter]
  rw [controlledAdjacentShiftLeftStep_eq_adjacentShiftLeftStep_of_control_true
    control left hcontrolLeft hleft x hcontrol]

private theorem controlledLeftThenRightStep_eq_self_of_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {leftWidth rightWidth : Nat}
    (control : EncodedBit encoding)
    (left : EncodedBit.Word encoding leftWidth)
    (right : EncodedBit.Word encoding rightWidth)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleft : ∀ i j, i ≠ j → (left.bit i).wire ≠ (left.bit j).wire)
    (hright : ∀ i j, i ≠ j → (right.bit i).wire ≠ (right.bit j).wire)
    (x : Data) (hcontrol : control.get x = false) :
    EncodedBit.Word.controlledAdjacentShiftRightStep
        control right hcontrolRight hright
        (EncodedBit.Word.controlledAdjacentShiftLeftStep
          control left hcontrolLeft hleft x) = x := by
  rw [controlledAdjacentShiftLeftStep_eq_self_of_control_false
    control left hcontrolLeft hleft x hcontrol]
  exact controlledAdjacentShiftRightStep_eq_self_of_control_false
    control right hcontrolRight hright x hcontrol

theorem auxUDiv2ThenSMul2Step_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (auxUDiv2ThenSMul2Step n counterWidth x) =
      (activeBit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (scratchABit n counterWidth) (activeBit n counterWidth)
    (uValueWord n counterWidth) (sCoeffValueWord n counterWidth)
    (scratchABit_uValueWord_bit_wire_ne n counterWidth)
    (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm (activeBit_uValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (activeBit_sCoeffValueWord_bit_wire_ne n counterWidth i)) x

theorem auxUDiv2ThenSMul2Step_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (auxUDiv2ThenSMul2Step n counterWidth x) =
      (scratchABit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (scratchABit n counterWidth) (scratchABit n counterWidth)
    (uValueWord n counterWidth) (sCoeffValueWord n counterWidth)
    (scratchABit_uValueWord_bit_wire_ne n counterWidth)
    (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm (scratchABit_uValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth i)) x

theorem activeVDiv2ThenRMul2Step_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (activeVDiv2ThenRMul2Step n counterWidth x) =
      (activeBit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (activeBit n counterWidth) (activeBit n counterWidth)
    (vValueWord n counterWidth) (rCoeffValueWord n counterWidth)
    (activeBit_vValueWord_bit_wire_ne n counterWidth)
    (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm (activeBit_vValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth i)) x

theorem activeVDiv2ThenRMul2Step_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (activeVDiv2ThenRMul2Step n counterWidth x) =
      (scratchABit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (activeBit n counterWidth) (scratchABit n counterWidth)
    (vValueWord n counterWidth) (rCoeffValueWord n counterWidth)
    (activeBit_vValueWord_bit_wire_ne n counterWidth)
    (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm (scratchABit_vValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth i)) x

theorem auxVDiv2ThenRMul2InverseShiftStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (auxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      (scratchABit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (scratchABit n counterWidth) (scratchABit n counterWidth)
    (rCoeffValueWord n counterWidth) (vValueWord n counterWidth)
    (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (scratchABit_vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (scratchABit_vValueWord_bit_wire_ne n counterWidth i)) x

theorem auxUDiv2ThenSMul2Step_eq_uDiv2ThenSMul2Step_of_scratchA_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (scratchABit n counterWidth).get x = true) :
    auxUDiv2ThenSMul2Step n counterWidth x =
      uDiv2ThenSMul2Step n counterWidth x := by
  exact controlledLeftThenRightStep_eq_uncontrolled_of_true
    (scratchABit n counterWidth) (uValueWord n counterWidth)
    (sCoeffValueWord n counterWidth)
    (scratchABit_uValueWord_bit_wire_ne n counterWidth)
    (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem auxUDiv2ThenSMul2Step_eq_self_of_scratchA_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (scratchABit n counterWidth).get x = false) :
    auxUDiv2ThenSMul2Step n counterWidth x = x := by
  exact controlledLeftThenRightStep_eq_self_of_false
    (scratchABit n counterWidth) (uValueWord n counterWidth)
    (sCoeffValueWord n counterWidth)
    (scratchABit_uValueWord_bit_wire_ne n counterWidth)
    (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
    (uValueWord_bit_wire_ne n counterWidth)
    (sCoeffValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem activeVDiv2ThenRMul2Step_eq_vDiv2ThenRMul2Step_of_active_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (activeBit n counterWidth).get x = true) :
    activeVDiv2ThenRMul2Step n counterWidth x =
      vDiv2ThenRMul2Step n counterWidth x := by
  exact controlledLeftThenRightStep_eq_uncontrolled_of_true
    (activeBit n counterWidth) (vValueWord n counterWidth)
    (rCoeffValueWord n counterWidth)
    (activeBit_vValueWord_bit_wire_ne n counterWidth)
    (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem activeVDiv2ThenRMul2Step_eq_self_of_active_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (activeBit n counterWidth).get x = false) :
    activeVDiv2ThenRMul2Step n counterWidth x = x := by
  exact controlledLeftThenRightStep_eq_self_of_false
    (activeBit n counterWidth) (vValueWord n counterWidth)
    (rCoeffValueWord n counterWidth)
    (activeBit_vValueWord_bit_wire_ne n counterWidth)
    (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem auxVDiv2ThenRMul2InverseShiftStep_eq_inverse_of_scratchA_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (scratchABit n counterWidth).get x = true) :
    auxVDiv2ThenRMul2InverseShiftStep n counterWidth x =
      vDiv2ThenRMul2InverseShiftStep n counterWidth x := by
  exact controlledLeftThenRightStep_eq_uncontrolled_of_true
    (scratchABit n counterWidth) (rCoeffValueWord n counterWidth)
    (vValueWord n counterWidth)
    (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (scratchABit_vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem auxVDiv2ThenRMul2InverseShiftStep_eq_self_of_scratchA_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (scratchABit n counterWidth).get x = false) :
    auxVDiv2ThenRMul2InverseShiftStep n counterWidth x = x := by
  exact controlledLeftThenRightStep_eq_self_of_false
    (scratchABit n counterWidth) (rCoeffValueWord n counterWidth)
    (vValueWord n counterWidth)
    (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (scratchABit_vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth) x hcontrol

theorem vDiv2ThenRMul2InverseShiftStep_comp_forward
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    vDiv2ThenRMul2InverseShiftStep n counterWidth
        (vDiv2ThenRMul2Step n counterWidth x) = x := by
  change
    EncodedBit.Word.adjacentShiftRightStep
        (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth)
        (EncodedBit.Word.adjacentShiftLeftStep
          (rCoeffValueWord n counterWidth)
          (rCoeffValueWord_bit_wire_ne n counterWidth)
          (EncodedBit.Word.adjacentShiftRightStep
            (rCoeffValueWord n counterWidth)
            (rCoeffValueWord_bit_wire_ne n counterWidth)
            (EncodedBit.Word.adjacentShiftLeftStep
              (vValueWord n counterWidth)
              (vValueWord_bit_wire_ne n counterWidth) x))) = x
  rw [EncodedBit.Word.adjacentShiftLeftStep_adjacentShiftRightStep]
  exact EncodedBit.Word.adjacentShiftRightStep_adjacentShiftLeftStep
    (vValueWord n counterWidth) (vValueWord_bit_wire_ne n counterWidth) x

/-- Literal compact dispatch: auxiliary-controlled `u/s`, active-controlled
`v/r`, then auxiliary-controlled inverse `v/r`. -/
def auxActiveShiftDispatchGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.Word.controlledAdjacentShiftLeftGates
      (scratchABit n counterWidth) (uValueWord n counterWidth)
      (scratchABit_uValueWord_bit_wire_ne n counterWidth)
      (uValueWord_bit_wire_ne n counterWidth) ++
    EncodedBit.Word.controlledAdjacentShiftRightGates
      (scratchABit n counterWidth) (sCoeffValueWord n counterWidth)
      (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
      (sCoeffValueWord_bit_wire_ne n counterWidth) ++
    EncodedBit.Word.controlledAdjacentShiftLeftGates
      (activeBit n counterWidth) (vValueWord n counterWidth)
      (activeBit_vValueWord_bit_wire_ne n counterWidth)
      (vValueWord_bit_wire_ne n counterWidth) ++
    EncodedBit.Word.controlledAdjacentShiftRightGates
      (activeBit n counterWidth) (rCoeffValueWord n counterWidth)
      (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth) ++
    EncodedBit.Word.controlledAdjacentShiftLeftGates
      (scratchABit n counterWidth) (rCoeffValueWord n counterWidth)
      (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
      (rCoeffValueWord_bit_wire_ne n counterWidth) ++
    EncodedBit.Word.controlledAdjacentShiftRightGates
      (scratchABit n counterWidth) (vValueWord n counterWidth)
      (scratchABit_vValueWord_bit_wire_ne n counterWidth)
      (vValueWord_bit_wire_ne n counterWidth)

/-- The paired compact shift dispatcher stays within core/shared work and is
disjoint from every public target bit. -/
theorem auxActiveShiftDispatchGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ auxActiveShiftDispatchGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  rw [auxActiveShiftDispatchGates] at hgate
  rcases List.mem_append.mp hgate with hgate | hvInv
  · rcases List.mem_append.mp hgate with hgate | hrInv
    · rcases List.mem_append.mp hgate with hgate | hr
      · rcases List.mem_append.mp hgate with hgate | hv
        · rcases List.mem_append.mp hgate with hu | hs
          · exact
              EncodedBit.Word.controlledAdjacentShiftLeftGates_bitDisjoint
                (scratchABit n counterWidth) (uValueWord n counterWidth)
                (scratchABit_uValueWord_bit_wire_ne n counterWidth)
                (uValueWord_bit_wire_ne n counterWidth)
                (targetValueBit n counterWidth targetIndex)
                (liftCoreBit_targetValueBit_wire_ne n counterWidth
                  (RegisterBits.scratchABit n counterWidth) targetIndex)
                (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
                  (RegisterBits.uValueBit n counterWidth i) targetIndex)
                gate hu
          · exact
              EncodedBit.Word.controlledAdjacentShiftRightGates_bitDisjoint
                (scratchABit n counterWidth) (sCoeffValueWord n counterWidth)
                (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
                (sCoeffValueWord_bit_wire_ne n counterWidth)
                (targetValueBit n counterWidth targetIndex)
                (liftCoreBit_targetValueBit_wire_ne n counterWidth
                  (RegisterBits.scratchABit n counterWidth) targetIndex)
                (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
                  (RegisterBits.sCoeffValueBit n counterWidth i) targetIndex)
                gate hs
        · exact
            EncodedBit.Word.controlledAdjacentShiftLeftGates_bitDisjoint
              (activeBit n counterWidth) (vValueWord n counterWidth)
              (activeBit_vValueWord_bit_wire_ne n counterWidth)
              (vValueWord_bit_wire_ne n counterWidth)
              (targetValueBit n counterWidth targetIndex)
              (liftCoreBit_targetValueBit_wire_ne n counterWidth
                (RegisterBits.activeBit n counterWidth) targetIndex)
              (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
                (RegisterBits.vValueBit n counterWidth i) targetIndex)
              gate hv
      · exact
          EncodedBit.Word.controlledAdjacentShiftRightGates_bitDisjoint
            (activeBit n counterWidth) (rCoeffValueWord n counterWidth)
            (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
            (rCoeffValueWord_bit_wire_ne n counterWidth)
            (targetValueBit n counterWidth targetIndex)
            (liftCoreBit_targetValueBit_wire_ne n counterWidth
              (RegisterBits.activeBit n counterWidth) targetIndex)
            (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
              (RegisterBits.rCoeffValueBit n counterWidth i) targetIndex)
            gate hr
    · exact
        EncodedBit.Word.controlledAdjacentShiftLeftGates_bitDisjoint
          (scratchABit n counterWidth) (rCoeffValueWord n counterWidth)
          (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
          (rCoeffValueWord_bit_wire_ne n counterWidth)
          (targetValueBit n counterWidth targetIndex)
          (liftCoreBit_targetValueBit_wire_ne n counterWidth
            (RegisterBits.scratchABit n counterWidth) targetIndex)
          (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
            (RegisterBits.rCoeffValueBit n counterWidth i) targetIndex)
          gate hrInv
  · exact EncodedBit.Word.controlledAdjacentShiftRightGates_bitDisjoint
      (scratchABit n counterWidth) (vValueWord n counterWidth)
      (scratchABit_vValueWord_bit_wire_ne n counterWidth)
      (vValueWord_bit_wire_ne n counterWidth)
      (targetValueBit n counterWidth targetIndex)
      (liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex)
      (fun i => liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth i) targetIndex) gate hvInv

def auxActiveShiftDispatchStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x =>
    auxVDiv2ThenRMul2InverseShiftStep n counterWidth
      (activeVDiv2ThenRMul2Step n counterWidth
        (auxUDiv2ThenSMul2Step n counterWidth x))

def auxActiveShiftDispatchProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (auxActiveShiftDispatchGates n counterWidth)

theorem auxActiveShiftDispatchStep_eq_gateList
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (auxActiveShiftDispatchGates n counterWidth) x =
      auxActiveShiftDispatchStep n counterWidth x := by
  unfold auxActiveShiftDispatchGates auxActiveShiftDispatchStep
    auxUDiv2ThenSMul2Step activeVDiv2ThenRMul2Step
    auxVDiv2ThenRMul2InverseShiftStep
  repeat rw [EncodedBit.GateSpec.stepList_append]
  rfl

theorem auxActiveShiftDispatch_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (auxActiveShiftDispatchProgram n counterWidth)
      (auxActiveShiftDispatchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (auxActiveShiftDispatchGates n counterWidth)
    (auxActiveShiftDispatchStep_eq_gateList n counterWidth)

theorem auxActiveShiftDispatchGates_length (n counterWidth : Nat) :
    (auxActiveShiftDispatchGates n counterWidth).length =
      9 * (n - 1) + 9 * n := by
  simp only [auxActiveShiftDispatchGates, List.length_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_length,
    EncodedBit.Word.controlledAdjacentShiftRightGates_length]
  omega

theorem auxActiveShiftDispatchGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((auxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp only [auxActiveShiftDispatchGates, List.map_append, List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_xMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_xMultiplicity_sum,
    Nat.zero_add]

theorem auxActiveShiftDispatchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((auxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [auxActiveShiftDispatchGates, List.map_append, List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_cnotMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_cnotMultiplicity_sum,
    Nat.zero_add]

theorem auxActiveShiftDispatchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((auxActiveShiftDispatchGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      9 * (n - 1) + 9 * n := by
  simp only [auxActiveShiftDispatchGates, List.map_append, List.sum_append,
    EncodedBit.Word.controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum,
    EncodedBit.Word.controlledAdjacentShiftRightGates_toffoliMultiplicity_sum]
  omega

theorem auxVDiv2ThenRMul2InverseShiftStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (auxVDiv2ThenRMul2InverseShiftStep n counterWidth x) =
      (activeBit n counterWidth).get x := by
  exact controlledLeftThenRightStep_get_observed
    (scratchABit n counterWidth) (activeBit n counterWidth)
    (rCoeffValueWord n counterWidth) (vValueWord n counterWidth)
    (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
    (scratchABit_vValueWord_bit_wire_ne n counterWidth)
    (rCoeffValueWord_bit_wire_ne n counterWidth)
    (vValueWord_bit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth i))
    (fun i => Ne.symm
      (activeBit_vValueWord_bit_wire_ne n counterWidth i)) x

/-- The compact shift dispatcher preserves the active-round flag. -/
theorem auxActiveShiftDispatchStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (activeBit n counterWidth).get x := by
  unfold auxActiveShiftDispatchStep
  rw [auxVDiv2ThenRMul2InverseShiftStep_get_active,
    activeVDiv2ThenRMul2Step_get_active,
    auxUDiv2ThenSMul2Step_get_active]

/-- The compact shift dispatcher preserves the staged auxiliary branch bit. -/
theorem auxActiveShiftDispatchStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (scratchABit n counterWidth).get x := by
  unfold auxActiveShiftDispatchStep
  rw [auxVDiv2ThenRMul2InverseShiftStep_get_scratchA,
    activeVDiv2ThenRMul2Step_get_scratchA,
    auxUDiv2ThenSMul2Step_get_scratchA]

/-- Any bit outside the four shifted words is preserved by the complete
compact dispatcher. -/
theorem auxActiveShiftDispatchStep_get_observed_of_words_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hu : ∀ i, ((uValueWord n counterWidth).bit i).wire ≠ observed.wire)
    (hs : ∀ i,
      ((sCoeffValueWord n counterWidth).bit i).wire ≠ observed.wire)
    (hv : ∀ i, ((vValueWord n counterWidth).bit i).wire ≠ observed.wire)
    (hr : ∀ i,
      ((rCoeffValueWord n counterWidth).bit i).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (auxActiveShiftDispatchStep n counterWidth x) =
      observed.get x := by
  unfold auxActiveShiftDispatchStep
  calc
    observed.get
        (auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth
            (auxUDiv2ThenSMul2Step n counterWidth x))) =
      observed.get
        (activeVDiv2ThenRMul2Step n counterWidth
          (auxUDiv2ThenSMul2Step n counterWidth x)) := by
        exact controlledLeftThenRightStep_get_observed
          (scratchABit n counterWidth) observed
          (rCoeffValueWord n counterWidth) (vValueWord n counterWidth)
          (scratchABit_rCoeffValueWord_bit_wire_ne n counterWidth)
          (scratchABit_vValueWord_bit_wire_ne n counterWidth)
          (rCoeffValueWord_bit_wire_ne n counterWidth)
          (vValueWord_bit_wire_ne n counterWidth) hr hv _
    _ = observed.get (auxUDiv2ThenSMul2Step n counterWidth x) := by
        exact controlledLeftThenRightStep_get_observed
          (activeBit n counterWidth) observed
          (vValueWord n counterWidth) (rCoeffValueWord n counterWidth)
          (activeBit_vValueWord_bit_wire_ne n counterWidth)
          (activeBit_rCoeffValueWord_bit_wire_ne n counterWidth)
          (vValueWord_bit_wire_ne n counterWidth)
          (rCoeffValueWord_bit_wire_ne n counterWidth) hv hr _
    _ = observed.get x := by
        exact controlledLeftThenRightStep_get_observed
          (scratchABit n counterWidth) observed
          (uValueWord n counterWidth) (sCoeffValueWord n counterWidth)
          (scratchABit_uValueWord_bit_wire_ne n counterWidth)
          (scratchABit_sCoeffValueWord_bit_wire_ne n counterWidth)
          (uValueWord_bit_wire_ne n counterWidth)
          (sCoeffValueWord_bit_wire_ne n counterWidth) hu hs x

theorem auxActiveShiftDispatchStep_get_scratchB
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (scratchBBit n counterWidth).get x := by
  apply auxActiveShiftDispatchStep_get_observed_of_words_ne
  · intro i
    simpa [uValueWord, scratchBBit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  · intro i
    simpa [sCoeffValueWord, sCoeffValueBit, scratchBBit,
      RegisterBits.sCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  · intro i
    simpa [vValueWord, scratchBBit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  · intro i
    simpa [rCoeffValueWord, rCoeffValueBit, scratchBBit,
      RegisterBits.rCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))

theorem auxActiveShiftDispatchStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  apply auxActiveShiftDispatchStep_get_observed_of_words_ne
  · intro i
    simpa [uValueWord, compareBit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  · intro i
    simpa [sCoeffValueWord, sCoeffValueBit, compareBit,
      RegisterBits.sCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (Ne.symm (RegisterBits.compare_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)))
  · intro i
    simpa [vValueWord, compareBit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire i))
  · intro i
    simpa [rCoeffValueWord, rCoeffValueBit, compareBit,
      RegisterBits.rCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (Ne.symm (RegisterBits.compare_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire i)))

theorem auxActiveShiftDispatchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (historyBit n counterWidth historyIndex).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (historyBit n counterWidth historyIndex).get x := by
  apply auxActiveShiftDispatchStep_get_observed_of_words_ne
  · intro i
    simpa [uValueWord, historyBit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.u_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire i) historyIndex)
  · intro i
    simpa [sCoeffValueWord, sCoeffValueBit, historyBit,
      RegisterBits.sCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.sCoeff_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire i) historyIndex)
  · intro i
    simpa [vValueWord, historyBit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire i) historyIndex)
  · intro i
    simpa [rCoeffValueWord, rCoeffValueBit, historyBit,
      RegisterBits.rCoeffValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.rCoeff_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire i) historyIndex)

theorem auxActiveShiftDispatchStep_get_coefficientCarryWorkBit
    (n counterWidth : Nat) (workIndex : Fin n)
    (x : Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth workIndex).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (coefficientCarryWorkBit n counterWidth workIndex).get x := by
  apply auxActiveShiftDispatchStep_get_observed_of_words_ne
  · intro i
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i) workIndex
  · intro i
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth i) workIndex
  · intro i
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i) workIndex
  · intro i
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth i) workIndex

theorem auxActiveShiftDispatchStep_get_coefficientCarryInBit
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (auxActiveShiftDispatchStep n counterWidth x) =
      (coefficientCarryInBit n counterWidth).get x := by
  apply auxActiveShiftDispatchStep_get_observed_of_words_ne
  · intro i
    exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
  · intro i
    exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth i)
  · intro i
    exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
  · intro i
    exact liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth i)

/-- If both branch controls are true, the active `v/r` shift and its
auxiliary inverse cancel, leaving exactly the `u/s` shift group. -/
theorem auxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (haux : (scratchABit n counterWidth).get x = true) :
    auxActiveShiftDispatchStep n counterWidth x =
      uDiv2ThenSMul2Step n counterWidth x := by
  have hauxStep :=
    auxUDiv2ThenSMul2Step_eq_uDiv2ThenSMul2Step_of_scratchA_true
      n counterWidth x haux
  have hactiveAfterU :
      (activeBit n counterWidth).get
          (uDiv2ThenSMul2Step n counterWidth x) = true := by
    rw [← hauxStep, auxUDiv2ThenSMul2Step_get_active, hactive]
  have hauxAfterU :
      (scratchABit n counterWidth).get
          (uDiv2ThenSMul2Step n counterWidth x) = true := by
    rw [← hauxStep, auxUDiv2ThenSMul2Step_get_scratchA, haux]
  have hactiveStep :=
    activeVDiv2ThenRMul2Step_eq_vDiv2ThenRMul2Step_of_active_true
      n counterWidth (uDiv2ThenSMul2Step n counterWidth x) hactiveAfterU
  have hauxAfterV :
      (scratchABit n counterWidth).get
          (vDiv2ThenRMul2Step n counterWidth
            (uDiv2ThenSMul2Step n counterWidth x)) = true := by
    rw [← hactiveStep, activeVDiv2ThenRMul2Step_get_scratchA, hauxAfterU]
  calc
    auxActiveShiftDispatchStep n counterWidth x =
        auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth
            (auxUDiv2ThenSMul2Step n counterWidth x)) := rfl
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth
            (uDiv2ThenSMul2Step n counterWidth x)) := by rw [hauxStep]
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (vDiv2ThenRMul2Step n counterWidth
            (uDiv2ThenSMul2Step n counterWidth x)) := by rw [hactiveStep]
    _ = vDiv2ThenRMul2InverseShiftStep n counterWidth
          (vDiv2ThenRMul2Step n counterWidth
            (uDiv2ThenSMul2Step n counterWidth x)) := by
          rw [auxVDiv2ThenRMul2InverseShiftStep_eq_inverse_of_scratchA_true
            n counterWidth _ hauxAfterV]
    _ = uDiv2ThenSMul2Step n counterWidth x :=
      vDiv2ThenRMul2InverseShiftStep_comp_forward n counterWidth _

/-- With active true and auxiliary false, only the `v/r` shift group runs. -/
theorem auxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (haux : (scratchABit n counterWidth).get x = false) :
    auxActiveShiftDispatchStep n counterWidth x =
      vDiv2ThenRMul2Step n counterWidth x := by
  have hauxStep :=
    auxUDiv2ThenSMul2Step_eq_self_of_scratchA_false
      n counterWidth x haux
  have hactiveStep :=
    activeVDiv2ThenRMul2Step_eq_vDiv2ThenRMul2Step_of_active_true
      n counterWidth x hactive
  have hauxAfterV :
      (scratchABit n counterWidth).get
          (vDiv2ThenRMul2Step n counterWidth x) = false := by
    rw [← hactiveStep, activeVDiv2ThenRMul2Step_get_scratchA, haux]
  calc
    auxActiveShiftDispatchStep n counterWidth x =
        auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth
            (auxUDiv2ThenSMul2Step n counterWidth x)) := rfl
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth x) := by rw [hauxStep]
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (vDiv2ThenRMul2Step n counterWidth x) := by rw [hactiveStep]
    _ = vDiv2ThenRMul2Step n counterWidth x :=
      auxVDiv2ThenRMul2InverseShiftStep_eq_self_of_scratchA_false
        n counterWidth _ hauxAfterV

/-- In inactive mode with clean auxiliary code, the dispatcher is a no-op. -/
theorem auxActiveShiftDispatchStep_eq_self_of_active_false_scratchA_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false)
    (haux : (scratchABit n counterWidth).get x = false) :
    auxActiveShiftDispatchStep n counterWidth x = x := by
  have hauxStep :=
    auxUDiv2ThenSMul2Step_eq_self_of_scratchA_false
      n counterWidth x haux
  have hactiveStep :=
    activeVDiv2ThenRMul2Step_eq_self_of_active_false
      n counterWidth x hactive
  calc
    auxActiveShiftDispatchStep n counterWidth x =
        auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth
            (auxUDiv2ThenSMul2Step n counterWidth x)) := rfl
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth
          (activeVDiv2ThenRMul2Step n counterWidth x) := by rw [hauxStep]
    _ = auxVDiv2ThenRMul2InverseShiftStep n counterWidth x := by rw [hactiveStep]
    _ = x := auxVDiv2ThenRMul2InverseShiftStep_eq_self_of_scratchA_false
      n counterWidth x haux

/-- Reversing the literal compact `u / 2` gate list restores every carrier. -/
theorem uDiv2CyclicShift_reverse_step
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList (uDiv2CyclicShiftGates n counterWidth).reverse
        (uDiv2CyclicShiftStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (uDiv2CyclicShiftGates n counterWidth) x

/-- Reversing the literal compact `v / 2` gate list restores every carrier. -/
theorem vDiv2CyclicShift_reverse_step
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList (vDiv2CyclicShiftGates n counterWidth).reverse
        (vDiv2CyclicShiftStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (vDiv2CyclicShiftGates n counterWidth) x

/-- Reversing the literal compact `s * 2` gate list restores every carrier. -/
theorem sMul2CyclicShift_reverse_step
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList (sMul2CyclicShiftGates n counterWidth).reverse
        (sMul2CyclicShiftStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (sMul2CyclicShiftGates n counterWidth) x

/-- Reversing the literal compact `r * 2` gate list restores every carrier. -/
theorem rMul2CyclicShift_reverse_step
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList (rMul2CyclicShiftGates n counterWidth).reverse
        (rMul2CyclicShiftStep n counterWidth x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (rMul2CyclicShiftGates n counterWidth) x

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Mathematics

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Resources

/-!
# Residue semantics of the compact in-place point schedule

This module exposes the field interpretation of the two arithmetic words used
by the seventeen-stage schedule.  It keeps the Montgomery scale explicit: a
product consumes one inverse radix, while inversion returns the squared-radix
scaled inverse supplied by the literal compact Montgomery--Kaliski circuit.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace Semantics

noncomputable section

open Nat.FixedWidth
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- The Montgomery radix `2^fieldWidth` as a unit modulo an odd modulus. -/
def radixUnit (p fieldWidth : Nat) (hpOdd : Odd p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (2 ^ fieldWidth)
    (Nat.Coprime.pow_left fieldWidth hpOdd.coprime_two_left)

@[simp] lemma radixUnit_coe (p fieldWidth : Nat) (hpOdd : Odd p) :
    (radixUnit p fieldWidth hpOdd : ZMod p) = 2 ^ fieldWidth := by
  simp [radixUnit, ZMod.coe_unitOfCoprime]

/-- Canonical fixed-width word for a Montgomery-encoded residue. -/
def montgomeryWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (value : ZMod p) : Word fieldTail.succ := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  exact
    ⟨(2 ^ fieldTail.succ * value.val) % p,
      (Nat.mod_lt _ hpPos).trans hp⟩

lemma montgomeryWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (value : ZMod p) :
    ((montgomeryWord fieldTail p hpPos hp value).val : ZMod p) =
      (2 : ZMod p) ^ fieldTail.succ * value := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  change
    ((((2 ^ fieldTail.succ * value.val) % p : Nat) : ZMod p)) = _
  rw [ZMod.natCast_mod]
  push_cast
  simp

lemma montgomeryWord_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (value : ZMod p) :
    (montgomeryWord fieldTail p hpPos hp value).val < p := by
  exact Nat.mod_lt _ hpPos

/-- The inverse-radix fold is the multiplicative inverse of `2^rounds`. -/
lemma inverseRadixUnit_mul_pow
    (p : Nat) (hpOdd : Odd p) :
    ∀ rounds : Nat,
      (MontgomeryMultiplication.inverseRadixUnit p hpOdd rounds : ZMod p) *
          (2 : ZMod p) ^ rounds = 1 := by
  intro rounds
  induction rounds with
  | zero => simp [MontgomeryMultiplication.inverseRadixUnit]
  | succ rounds induction =>
      simp only [MontgomeryMultiplication.inverseRadixUnit, Units.val_mul,
        pow_succ]
      have htwo :
          (MontgomeryMultiplication.twoUnit p hpOdd : ZMod p) = 2 := by
        simp [MontgomeryMultiplication.twoUnit, ZMod.coe_unitOfCoprime]
      calc
        _ =
            (((MontgomeryMultiplication.twoUnit p hpOdd)⁻¹ : (ZMod p)ˣ) :
                ZMod p) *
              ((MontgomeryMultiplication.inverseRadixUnit p hpOdd rounds :
                  ZMod p) * (2 : ZMod p) ^ rounds) * 2 := by ring
        _ =
            (((MontgomeryMultiplication.twoUnit p hpOdd)⁻¹ : (ZMod p)ˣ) :
                ZMod p) * 1 * 2 := by rw [induction]
        _ =
            (((MontgomeryMultiplication.twoUnit p hpOdd)⁻¹ : (ZMod p)ˣ) :
                ZMod p) * 1 *
              (MontgomeryMultiplication.twoUnit p hpOdd : ZMod p) := by
                rw [htwo]
        _ = 1 := by simp

/-- The schedule's closed product word denotes one Montgomery product. -/
lemma productWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (multiplier coefficient : Word fieldTail.succ)
    (hcoefficient : coefficient.val < p) :
    ((Schedule.productWord fieldTail p hpPos hp multiplier coefficient).val :
        ZMod p) =
      (multiplier.val : ZMod p) *
        (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
          ZMod p) *
        (coefficient.val : ZMod p) := by
  let coefficientWide :=
    CompactCorrection.widenFixedWord fieldTail.succ coefficient
  let initial : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficientWide
      target := 0 }
  have hwide : coefficientWide.val < p := by
    simpa [coefficientWide] using hcoefficient
  have hscaled : initial.coefficient.val < p := by
    exact MontgomeryMultiplication.inverseScaleWord_lt fieldTail p hpPos hp
      hpOdd fieldTail.succ coefficientWide hwide
  have htarget : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have semantic :=
    MontgomeryMultiplication.residueRounds_finRange_target_cast fieldTail p
      hpPos hp multiplier initial hscaled htarget
  have scale := MontgomeryMultiplication.inverseScaleWord_cast fieldTail p
    hpPos hp hpOdd fieldTail.succ coefficientWide hwide
  change
    ((MontgomeryMultiplication.residueRounds fieldTail p hpPos hp multiplier
        (List.finRange fieldTail.succ) initial).target.val : ZMod p) = _
  rw [semantic]
  dsimp only [initial]
  rw [Fin.val_zero, Nat.cast_zero, zero_add, scale]
  simp only [coefficientWide, CompactCorrection.widenFixedWord_val]
  ring

/-- The compact inversion word is the literal squared-radix scaled inverse.
The full-width hypothesis is the range condition used by its correction
schedule. -/
lemma inversionOutput_cast
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    (input : Word fieldTail.succ)
    (hinput : 0 < input.val) (hcoprime : Nat.Coprime p input.val)
    (u : (ZMod p)ˣ) (hinputUnit : (input.val : ZMod p) = (u : ZMod p)) :
    ((Schedule.inversionOutput fieldTail counterTail p hpPos hp hfit input
        0).val : ZMod p) =
      scaledInverseResidue ((2 : ZMod p) ^ (2 * fieldTail.succ)) u := by
  have endpoint :=
    CompactInversion.compactInversionStep_cleanMontgomeryUnitEndpoint
      fieldTail counterTail hfit hcapacity hwidth hcounterWidth
      (⟨p, hp⟩ : Word fieldTail.succ) input 0
      (Nat.odd_iff.mp hpOdd) hinput hcoprime hfull (by simpa using hpPos)
      u hinputUnit
  dsimp only at endpoint
  simpa [Schedule.inversionOutput] using endpoint.2

/-- A compact inversion fed a Montgomery word returns the Montgomery word of
the field inverse. -/
lemma inversionOutput_montgomery_cast
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (value : ZMod p) (hvalue : value ≠ 0) :
    ((Schedule.inversionOutput fieldTail counterTail p hpPos hp hfit
        (montgomeryWord fieldTail p hpPos hp value) 0).val : ZMod p) =
      (2 : ZMod p) ^ fieldTail.succ * value⁻¹ := by
  let input := montgomeryWord fieldTail p hpPos hp value
  have inputCast : (input.val : ZMod p) =
      (2 : ZMod p) ^ fieldTail.succ * value := by
    simpa only [input] using montgomeryWord_cast fieldTail p hpPos hp value
  have radixNe : (2 : ZMod p) ^ fieldTail.succ ≠ 0 := by
    rw [← radixUnit_coe p fieldTail.succ hpOdd]
    exact Units.ne_zero _
  have inputCastNe : (input.val : ZMod p) ≠ 0 := by
    rw [inputCast]
    exact mul_ne_zero radixNe hvalue
  have inputPos : 0 < input.val := by
    by_contra notPositive
    have inputZero : input.val = 0 := Nat.eq_zero_of_not_pos notPositive
    exact inputCastNe (by simp [inputZero])
  have inputIsUnit : IsUnit (input.val : ZMod p) :=
    (isUnit_iff_ne_zero).2 inputCastNe
  have inputCoprime : Nat.Coprime p input.val := by
    exact (ZMod.isUnit_iff_coprime input.val p).mp inputIsUnit |>.symm
  let inputUnit : (ZMod p)ˣ :=
    ZMod.unitOfCoprime input.val inputCoprime.symm
  have inputUnitCoe : (inputUnit : ZMod p) = (input.val : ZMod p) := by
    simp [inputUnit, ZMod.coe_unitOfCoprime]
  have raw := inversionOutput_cast fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull input inputPos inputCoprime
    inputUnit inputUnitCoe.symm
  calc
    ((Schedule.inversionOutput fieldTail counterTail p hpPos hp hfit input
        0).val : ZMod p) =
        scaledInverseResidue ((2 : ZMod p) ^ (2 * fieldTail.succ))
          inputUnit := raw
    _ = (2 : ZMod p) ^ (2 * fieldTail.succ) *
        ((inputUnit : ZMod p)⁻¹) := by
      change
        (2 : ZMod p) ^ (2 * fieldTail.succ) *
            (((inputUnit⁻¹ : (ZMod p)ˣ) : ZMod p)) = _
      rw [Units.val_inv_eq_inv_val]
    _ = (2 : ZMod p) ^ (2 * fieldTail.succ) *
        (((2 : ZMod p) ^ fieldTail.succ * value)⁻¹) := by
      rw [inputUnitCoe, inputCast]
    _ = (2 : ZMod p) ^ fieldTail.succ * value⁻¹ := by
      rw [two_mul, pow_add]
      field_simp [radixNe, hvalue]

/-- Multiplying two Montgomery words emits the Montgomery encoding of their
field product. -/
lemma productWord_montgomery_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (left right : ZMod p) :
    ((Schedule.productWord fieldTail p hpPos hp
        (montgomeryWord fieldTail p hpPos hp left)
        (montgomeryWord fieldTail p hpPos hp right)).val : ZMod p) =
      (2 : ZMod p) ^ fieldTail.succ * (left * right) := by
  have product := productWord_cast fieldTail p hpPos hp hpOdd
    (montgomeryWord fieldTail p hpPos hp left)
    (montgomeryWord fieldTail p hpPos hp right)
    (montgomeryWord_lt fieldTail p hpPos hp right)
  rw [montgomeryWord_cast, montgomeryWord_cast] at product
  rw [product]
  have inverseLaw := inverseRadixUnit_mul_pow p hpOdd fieldTail.succ
  calc
    ((2 : ZMod p) ^ fieldTail.succ * left) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) *
        ((2 : ZMod p) ^ fieldTail.succ * right) =
        (2 : ZMod p) ^ fieldTail.succ *
          ((MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
              ZMod p) *
            (2 : ZMod p) ^ fieldTail.succ) * (left * right) := by ring
    _ = (2 : ZMod p) ^ fieldTail.succ * (left * right) := by
      rw [inverseLaw]
      ring

/-- Two canonical field words are equal when their residue-field casts agree.
-/
lemma word_eq_of_cast_eq
    {fieldWidth p : Nat}
    (left right : Word fieldWidth)
    (hleft : left.val < p) (hright : right.val < p)
    (equality : (left.val : ZMod p) = (right.val : ZMod p)) :
    left = right := by
  apply Fin.ext
  have values := congrArg ZMod.val equality
  simpa [ZMod.val_natCast_of_lt hleft, ZMod.val_natCast_of_lt hright] using
    values

/-- Modular subtraction preserves Montgomery encoding. -/
lemma modularDifferenceWord_montgomery
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (left right : ZMod p) :
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
        (montgomeryWord fieldTail p hpPos hp left)
        (montgomeryWord fieldTail p hpPos hp right) =
      montgomeryWord fieldTail p hpPos hp (left - right) := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  apply word_eq_of_cast_eq (p := p)
  · exact Nat.mod_lt _ hpPos
  · exact montgomeryWord_lt fieldTail p hpPos hp (left - right)
  rw [CompactCorrection.modularDifferenceWord_cast]
  · rw [montgomeryWord_cast, montgomeryWord_cast, montgomeryWord_cast]
    ring
  · exact montgomeryWord_lt fieldTail p hpPos hp right

/-- Modular addition preserves Montgomery encoding. -/
lemma modularSumFixedWord_montgomery
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (left right : ZMod p) :
    CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
        (montgomeryWord fieldTail p hpPos hp left)
        (montgomeryWord fieldTail p hpPos hp right) =
      montgomeryWord fieldTail p hpPos hp (left + right) := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  apply word_eq_of_cast_eq (p := p)
  · exact Nat.mod_lt _ hpPos
  · exact montgomeryWord_lt fieldTail p hpPos hp (left + right)
  rw [MontgomeryMultiplication.modularSumFixedWord_cast]
  rw [montgomeryWord_cast, montgomeryWord_cast, montgomeryWord_cast]
  ring

/-- The closed schedule product preserves Montgomery encoding. -/
lemma productWord_montgomery
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (left right : ZMod p) :
    Schedule.productWord fieldTail p hpPos hp
        (montgomeryWord fieldTail p hpPos hp left)
        (montgomeryWord fieldTail p hpPos hp right) =
      montgomeryWord fieldTail p hpPos hp (left * right) := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  apply word_eq_of_cast_eq (p := p)
  · exact Schedule.productWord_lt fieldTail p hpPos hp hpOdd _ _
      (montgomeryWord_lt fieldTail p hpPos hp right)
  · exact montgomeryWord_lt fieldTail p hpPos hp (left * right)
  exact (productWord_montgomery_cast fieldTail p hpPos hp hpOdd left right).trans
    (montgomeryWord_cast fieldTail p hpPos hp (left * right)).symm

/-- The closed schedule inversion preserves Montgomery encoding on nonzero
field inputs. -/
lemma inversionOutput_montgomery
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (value : ZMod p) (hvalue : value ≠ 0) :
    Schedule.inversionOutput fieldTail counterTail p hpPos hp hfit
        (montgomeryWord fieldTail p hpPos hp value) 0 =
      montgomeryWord fieldTail p hpPos hp value⁻¹ := by
  apply word_eq_of_cast_eq (p := p)
  · exact Schedule.inversionOutput_lt fieldTail counterTail p hpPos hp hfit _ _
  · exact montgomeryWord_lt fieldTail p hpPos hp value⁻¹
  exact (inversionOutput_montgomery_cast fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull value hvalue).trans
    (montgomeryWord_cast fieldTail p hpPos hp value⁻¹).symm

@[simp] lemma montgomeryWord_zero
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) :
    montgomeryWord fieldTail p hpPos hp 0 = 0 := by
  apply Fin.ext
  simp [montgomeryWord]

/-- A nonzero residue has a positive canonical Montgomery word. -/
lemma montgomeryWord_positive
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    [Fact p.Prime] (value : ZMod p) (hvalue : value ≠ 0) :
    0 < (montgomeryWord fieldTail p hpPos hp value).val := by
  have radixNe : (2 : ZMod p) ^ fieldTail.succ ≠ 0 := by
    rw [← radixUnit_coe p fieldTail.succ hpOdd]
    exact Units.ne_zero _
  have castNe :
      ((montgomeryWord fieldTail p hpPos hp value).val : ZMod p) ≠ 0 := by
    rw [montgomeryWord_cast]
    exact mul_ne_zero radixNe hvalue
  by_contra notPositive
  have wordZero : (montgomeryWord fieldTail p hpPos hp value).val = 0 :=
    Nat.eq_zero_of_not_pos notPositive
  exact castNe (by simp [wordZero])

/-- A nonzero residue has a Montgomery word coprime to the prime modulus. -/
lemma montgomeryWord_coprime
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    [Fact p.Prime] (value : ZMod p) (hvalue : value ≠ 0) :
    Nat.Coprime p (montgomeryWord fieldTail p hpPos hp value).val := by
  have radixNe : (2 : ZMod p) ^ fieldTail.succ ≠ 0 := by
    rw [← radixUnit_coe p fieldTail.succ hpOdd]
    exact Units.ne_zero _
  have castNe :
      ((montgomeryWord fieldTail p hpPos hp value).val : ZMod p) ≠ 0 := by
    rw [montgomeryWord_cast]
    exact mul_ne_zero radixNe hvalue
  exact
    ((ZMod.isUnit_iff_coprime
      (montgomeryWord fieldTail p hpPos hp value).val p).mp
      ((isUnit_iff_ne_zero).2 castNe)).symm

/-- The four public words of one compact point-addition call. -/
def montgomeryInput
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) : Schedule.Input fieldTail where
  control := control
  x1 := montgomeryWord fieldTail p hpPos hp x1
  y1 := montgomeryWord fieldTail p hpPos hp y1
  x2 := montgomeryWord fieldTail p hpPos hp x2
  y2 := montgomeryWord fieldTail p hpPos hp y2

@[simp] lemma montgomeryInput_control
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).control =
      control := rfl

@[simp] lemma montgomeryInput_x2
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).x2 =
      montgomeryWord fieldTail p hpPos hp x2 := rfl

@[simp] lemma montgomeryInput_y2
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).y2 =
      montgomeryWord fieldTail p hpPos hp y2 := rfl

lemma montgomeryInput_xAfterSubtract
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).xAfterSubtract
        p hpPos hp = montgomeryWord fieldTail p hpPos hp (x1 - x2) := by
  exact modularDifferenceWord_montgomery fieldTail p hpPos hp x1 x2

lemma montgomeryInput_yAfterSelectedSubtract
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (control : Bool)
    (x1 y1 x2 y2 : ZMod p) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).yAfterSelectedSubtract
        p hpPos hp =
      montgomeryWord fieldTail p hpPos hp
        (selectedNumerator control y1 y2) := by
  cases control <;>
    simp [montgomeryInput, Schedule.Input.yAfterSelectedSubtract,
      selectedNumerator, modularDifferenceWord_montgomery]

lemma montgomeryInput_firstInverse
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (control : Bool) (x1 y1 x2 y2 : ZMod p)
    (hfirst : x1 - x2 ≠ 0) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).firstInverse
        counterTail p hpPos hp hfit =
      montgomeryWord fieldTail p hpPos hp (x1 - x2)⁻¹ := by
  rw [Schedule.Input.firstInverse, montgomeryInput_xAfterSubtract]
  exact inversionOutput_montgomery fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull (x1 - x2) hfirst

lemma montgomeryInput_slope
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (control : Bool) (x1 y1 x2 y2 : ZMod p)
    (hfirst : x1 - x2 ≠ 0) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).slope
        counterTail p hpPos hp hfit =
      montgomeryWord fieldTail p hpPos hp
        (selectedSlope control x1 y1 x2 y2) := by
  rw [Schedule.Input.slope, montgomeryInput_yAfterSelectedSubtract,
    montgomeryInput_firstInverse fieldTail counterTail p hpPos hp hfit
      hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst,
    productWord_montgomery fieldTail p hpPos hp hpOdd]
  rfl

lemma tripleConstant_montgomery
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (x : ZMod p) :
    Schedule.tripleConstant fieldTail p hpPos hp
        (montgomeryWord fieldTail p hpPos hp x) =
      montgomeryWord fieldTail p hpPos hp (3 * x) := by
  rw [Schedule.tripleConstant, modularSumFixedWord_montgomery,
    modularSumFixedWord_montgomery]
  congr 1
  ring

lemma montgomeryInput_secondDenominator
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (control : Bool) (x1 y1 x2 y2 : ZMod p)
    (hfirst : x1 - x2 ≠ 0) :
    (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).xBeforeNegation
        counterTail p hpPos hp hfit =
      montgomeryWord fieldTail p hpPos hp
        (secondDenominator control x1 y1 x2 y2) := by
  have hslope := montgomeryInput_slope fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst
  have hsquare :
      (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).slopeSquare
          counterTail p hpPos hp hfit =
        montgomeryWord fieldTail p hpPos hp
          (selectedSlope control x1 y1 x2 y2 ^ 2) := by
    rw [Schedule.Input.slopeSquare, hslope,
      productWord_montgomery fieldTail p hpPos hp hpOdd]
    ring_nf
  cases control with
  | false =>
      simpa only [Schedule.Input.xBeforeNegation,
        Schedule.Input.xAfterSelectedSquareSubtract, montgomeryInput_control,
        Bool.false_eq_true, if_false, secondDenominator] using
        (montgomeryInput_xAfterSubtract fieldTail p hpPos hp false
          x1 y1 x2 y2)
  | true =>
      rw [Schedule.Input.xBeforeNegation,
        Schedule.Input.xAfterSelectedSquareSubtract]
      simp only [montgomeryInput_control, ↓reduceIte,
        montgomeryInput_x2]
      rw [montgomeryInput_xAfterSubtract, hsquare,
        modularDifferenceWord_montgomery, tripleConstant_montgomery,
        modularSumFixedWord_montgomery]
      rfl

lemma montgomeryInput_cleanCertificate
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (control : Bool) (x1 y1 x2 y2 : ZMod p)
    (hfirst : x1 - x2 ≠ 0)
    (hsecond : secondDenominator control x1 y1 x2 y2 ≠ 0) :
    Schedule.CleanCertificate fieldTail counterTail p hpPos hp hfit
      (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2) := by
  let data := montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2
  have hxA := montgomeryInput_xAfterSubtract fieldTail p hpPos hp control
    x1 y1 x2 y2
  have hyA := montgomeryInput_yAfterSelectedSubtract fieldTail p hpPos hp
    control x1 y1 x2 y2
  have hslope := montgomeryInput_slope fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst
  have hxC := montgomeryInput_secondDenominator fieldTail counterTail p hpPos hp
    hfit hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst
  refine
    { hpOdd := hpOdd
      hx1 := montgomeryWord_lt fieldTail p hpPos hp x1
      hy1 := montgomeryWord_lt fieldTail p hpPos hp y1
      hx2 := montgomeryWord_lt fieldTail p hpPos hp x2
      hy2 := montgomeryWord_lt fieldTail p hpPos hp y2
      firstInputPositive := ?_
      firstInputCoprime := ?_
      secondInputPositive := ?_
      secondInputCoprime := ?_
      firstProductClears := ?_
      secondProductClears := ?_ }
  · rw [hxA]
    exact montgomeryWord_positive fieldTail p hpPos hp hpOdd _ hfirst
  · rw [hxA]
    exact montgomeryWord_coprime fieldTail p hpPos hp hpOdd _ hfirst
  · rw [hxC]
    exact montgomeryWord_positive fieldTail p hpPos hp hpOdd _ hsecond
  · rw [hxC]
    exact montgomeryWord_coprime fieldTail p hpPos hp hpOdd _ hsecond
  · rw [hslope, hxA, hyA,
      productWord_montgomery fieldTail p hpPos hp hpOdd]
    congr 1
    simp [selectedSlope, hfirst]
  · have hyB :
        data.yBeforeFinalSubtract counterTail p hpPos hp hfit =
          montgomeryWord fieldTail p hpPos hp
            (selectedSlope control x1 y1 x2 y2 *
              secondDenominator control x1 y1 x2 y2) := by
      rw [Schedule.Input.yBeforeFinalSubtract, hslope, hxC,
        productWord_montgomery fieldTail p hpPos hp hpOdd]
    have hinv2 :
        data.secondInverse counterTail p hpPos hp hfit =
          montgomeryWord fieldTail p hpPos hp
            (secondDenominator control x1 y1 x2 y2)⁻¹ := by
      rw [Schedule.Input.secondInverse, hxC]
      exact inversionOutput_montgomery fieldTail counterTail p hpPos hp hfit
        hcapacity hwidth hcounterWidth hpOdd hfull _ hsecond
    rw [hyB, hinv2, hslope,
      productWord_montgomery fieldTail p hpPos hp hpOdd]
    congr 1
    simp [hsecond]

/-- Both public output words carry the field values selected by the control
bit, while every auxiliary register is covered by the clean certificate. -/
lemma montgomeryInput_outputs
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    [Fact p.Prime] (control : Bool) (x1 y1 x2 y2 : ZMod p)
    (hfirst : x1 - x2 ≠ 0) :
    let data := montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2
    data.outputX counterTail p hpPos hp hfit =
        montgomeryWord fieldTail p hpPos hp
          (selectedOutputX control x1 y1 x2 y2) ∧
      data.outputY counterTail p hpPos hp hfit =
        montgomeryWord fieldTail p hpPos hp
          (selectedOutputY control x1 y1 x2 y2) := by
  dsimp only
  have hslope := montgomeryInput_slope fieldTail counterTail p hpPos hp hfit
    hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst
  have hxC := montgomeryInput_secondDenominator fieldTail counterTail p hpPos hp
    hfit hcapacity hwidth hcounterWidth hpOdd hfull control x1 y1 x2 y2 hfirst
  have hyB :
      (montgomeryInput fieldTail p hpPos hp control x1 y1 x2 y2).yBeforeFinalSubtract
          counterTail p hpPos hp hfit =
        montgomeryWord fieldTail p hpPos hp
          (selectedSlope control x1 y1 x2 y2 *
            secondDenominator control x1 y1 x2 y2) := by
    rw [Schedule.Input.yBeforeFinalSubtract, hslope, hxC,
      productWord_montgomery fieldTail p hpPos hp hpOdd]
  constructor
  · cases control with
    | false =>
        rw [Schedule.Input.outputX, Schedule.Input.xAfterNegation]
        simp only [montgomeryInput_control, Bool.false_eq_true, if_false,
          selectedOutputX, montgomeryInput_x2]
        rw [hxC, modularSumFixedWord_montgomery]
    | true =>
        rw [Schedule.Input.outputX, Schedule.Input.xAfterNegation]
        simp only [montgomeryInput_control, ↓reduceIte,
          selectedOutputX, montgomeryInput_x2]
        rw [hxC, ← montgomeryWord_zero fieldTail p hpPos hp,
          modularDifferenceWord_montgomery]
        rw [modularSumFixedWord_montgomery]
        congr 1
        ring
  · cases control with
    | false =>
        rw [Schedule.Input.outputY]
        simp only [montgomeryInput_control, Bool.false_eq_true, if_false,
          selectedOutputY]
        exact hyB
    | true =>
        rw [Schedule.Input.outputY]
        simp only [montgomeryInput_control, ↓reduceIte,
          selectedOutputY, montgomeryInput_y2]
        rw [hyB]
        exact modularDifferenceWord_montgomery fieldTail p hpPos hp _ _

end
end Semantics
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end

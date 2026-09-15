/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Checked.SignedReduction.Model

/-!
# Original pure checked-inverse engine interpretation

The original widened XGCD input, unit decision, canonical coefficient and
checked-inverse acceptance proofs retain their exact names and bodies. This
model has no retired machine interpreter dependency. Its modulus may equal
the full operand capacity, and failure covers every nonunit denominator.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Engine

open ClassicalAlgorithms
open ClassicalAlgorithms.NumberTheory
open ClassicalAlgorithms.Modular
open SignedReduction

/-- The semantic XGCD input used for every checked denominator. -/
def xgcdInput {width : Nat} (spec : ModulusSpec width)
    (denominator : Residue spec) : XGCD.PureXGCD.Input (xgcdWidth width) where
  left := wordOfNat (xgcdWidth width) spec.modulus
  right := wordOfNat (xgcdWidth width) denominator.val

/-- The deterministic right Bezout coefficient selected by widened XGCD,
canonically reduced into the endpoint modulus. -/
def inverseCoefficient {width : Nat} (spec : ModulusSpec width)
    (denominator : Residue spec) : Residue spec :=
  residueOfInt spec
    (XGCD.PureXGCD.eval
      (xgcdInput spec denominator)).rightCoefficient.toInt

/-- Runtime-success meaning shared by every checked endpoint. -/
def unitDecision {width : Nat} (spec : ModulusSpec width)
    (denominator : Residue spec) : Bool :=
  decide (Nat.Coprime denominator.val spec.modulus)

/-- Pure optional result exposed by the shared engine before any endpoint-
specific multiplication or nominal packing. -/
def checkedInverse {width : Nat} (spec : ModulusSpec width)
    (denominator : Residue spec) : Option (Residue spec) :=
  if _coprime : Nat.Coprime denominator.val spec.modulus then
    some (inverseCoefficient spec denominator)
  else
    none

/-- A raw-engine coefficient satisfying XGCD's decoder contract reduces to
the Engine's unique pure inverse coefficient. -/
theorem reduceRawCoefficient_eq_inverseCoefficient {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (raw : CShape.Word (signedWidth width))
    (decoded : XGCD.decodeRawSignedWord (width := xgcdWidth width) raw =
      (XGCD.PureXGCD.eval
        (xgcdInput spec denominator)).rightCoefficient.toInt) :
    reduceRawCoefficient spec raw = inverseCoefficient spec denominator := by
  unfold reduceRawCoefficient inverseCoefficient
  rw [decoded]

/-- The explicit signed-reduction target agrees with the shared inverse
coefficient whenever the reusable XGCD engine supplies its decoder contract. -/
theorem rawCanonicalResidue_eq_inverseCoefficient {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (raw : CShape.Word (signedWidth width))
    (decoded : XGCD.decodeRawSignedWord (width := xgcdWidth width) raw =
      (XGCD.PureXGCD.eval
        (xgcdInput spec denominator)).rightCoefficient.toInt) :
    rawCanonicalResidue spec raw = inverseCoefficient spec denominator := by
  rw [rawCanonicalResidue_eq_reduceRawCoefficient]
  exact reduceRawCoefficient_eq_inverseCoefficient
    spec denominator raw decoded

@[simp] theorem xgcdInput_left_val {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    (xgcdInput spec denominator).left.val = spec.modulus := by
  unfold xgcdInput xgcdWidth
  rw [fixedWidthWordOfNat_val, Nat.mod_eq_of_lt]
  exact modulusSpec_modulus_lt_extended spec

@[simp] theorem xgcdInput_right_val {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    (xgcdInput spec denominator).right.val = denominator.val := by
  unfold xgcdInput xgcdWidth
  rw [fixedWidthWordOfNat_val, Nat.mod_eq_of_lt]
  exact denominator.isLt.trans (modulusSpec_modulus_lt_extended spec)

/-- Comparing widened XGCD's raw gcd with one is exactly the endpoint unit
decision; no separate primality or ring-inverse test is involved. -/
theorem checkedEngine_xgcdGcdOne_iff {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    (XGCD.PureXGCD.eval
      (xgcdInput spec denominator)).gcd.val = 1 ↔
        Nat.Coprime denominator.val spec.modulus := by
  rw [ClassicalAlgorithms.NumberTheory.XGCD.xgcdEval_gcd_val,
    xgcdInput_left_val, xgcdInput_right_val]
  simp [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]

/-- On a unit denominator, the shared coefficient reduction is a genuine
canonical inverse. -/
theorem inverseCoefficient_mul_mod {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (coprime : Nat.Coprime denominator.val spec.modulus) :
    denominator.val * (inverseCoefficient spec denominator).val %
        spec.modulus = 1 := by
  let _ : NeZero spec.modulus :=
    ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have xgcdAccepts :=
    XGCD.PureXGCD.xgcdEval_accepts (xgcdInput spec denominator)
  have gcdOne :
      Nat.gcd (xgcdInput spec denominator).left.val
          (xgcdInput spec denominator).right.val = 1 := by
    rw [xgcdInput_left_val, xgcdInput_right_val]
    exact coprime.symm.gcd_eq_one
  have outputGcdOne :
      (XGCD.PureXGCD.eval
        (xgcdInput spec denominator)).gcd.val = 1 :=
    xgcdAccepts.1.trans gcdOne
  have bezout :
      (1 : Int) =
        (spec.modulus : Int) *
            (XGCD.PureXGCD.eval
              (xgcdInput spec denominator)).leftCoefficient.toInt +
          (denominator.val : Int) *
            (XGCD.PureXGCD.eval
              (xgcdInput spec denominator)).rightCoefficient.toInt := by
    calc
      (1 : Int) =
          ((XGCD.PureXGCD.eval
            (xgcdInput spec denominator)).gcd.val : Int) := by
        exact congrArg (fun value : Nat => (value : Int)) outputGcdOne.symm
      _ =
          ((xgcdInput spec denominator).left.val : Int) *
              (XGCD.PureXGCD.eval
                (xgcdInput spec denominator)).leftCoefficient.toInt +
            ((xgcdInput spec denominator).right.val : Int) *
              (XGCD.PureXGCD.eval
                (xgcdInput spec denominator)).rightCoefficient.toInt :=
        xgcdAccepts.2.1
      _ = _ := by rw [xgcdInput_left_val, xgcdInput_right_val]
  have castBezout :=
    congrArg (fun value : Int => (value : ZMod spec.modulus)) bezout
  have coefficientProduct :
      (denominator.val : ZMod spec.modulus) *
          ((XGCD.PureXGCD.eval
            (xgcdInput spec denominator)).rightCoefficient.toInt :
              ZMod spec.modulus) = 1 := by
    simpa only [Int.cast_one, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add] using
        castBezout.symm
  have canonicalProduct :
      (denominator.val : ZMod spec.modulus) *
          ((inverseCoefficient spec denominator).val :
            ZMod spec.modulus) = 1 := by
    rw [inverseCoefficient, residueOfInt_cast]
    exact coefficientProduct
  have naturalCast :
      ((denominator.val * (inverseCoefficient spec denominator).val : Nat) :
          ZMod spec.modulus) = ((1 : Nat) : ZMod spec.modulus) := by
    simpa only [Nat.cast_mul, Nat.cast_one] using canonicalProduct
  have modularEquality :=
    (ZMod.natCast_eq_natCast_iff'
      (denominator.val * (inverseCoefficient spec denominator).val)
      1 spec.modulus).1 naturalCast
  simpa [Nat.mod_eq_of_lt (modulusSpec_one_lt spec)] using modularEquality

/-- The shared coefficient agrees with the pure endpoint's selected canonical
inverse whenever the denominator is a unit. -/
theorem inverseCoefficient_eq_candidate {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (coprime : Nat.Coprime denominator.val spec.modulus) :
    inverseCoefficient spec denominator =
      ClassicalAlgorithms.NumberTheory.inverseCandidate
        spec denominator := by
  exact inverse_eq_candidate_of_mul_mod spec denominator
    (inverseCoefficient spec denominator) coprime
    (inverseCoefficient_mul_mod spec denominator coprime)

@[simp] theorem checkedEngine_unitDecision_true_iff {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    unitDecision spec denominator = true ↔
      Nat.Coprime denominator.val spec.modulus := by
  simp [unitDecision]

@[simp] theorem checkedEngine_unitDecision_false_iff {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    unitDecision spec denominator = false ↔
      ¬ Nat.Coprime denominator.val spec.modulus := by
  simp [unitDecision]

/-- The raw gcd value supplied by `RawEngineRelation` selects the same success
bit as the shared pure unit decision. -/
theorem checkedEngine_rawGcdOne_iff_unitDecision {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (rawGcd : CShape.Word (xgcdWidth width))
    (rawValue : rawGcd.toNat =
      (XGCD.PureXGCD.eval
        (xgcdInput spec denominator)).gcd.val) :
    rawGcd.toNat = 1 ↔ unitDecision spec denominator = true := by
  calc
    rawGcd.toNat = 1 ↔
        (XGCD.PureXGCD.eval
          (xgcdInput spec denominator)).gcd.val = 1 := by rw [rawValue]
    _ ↔ Nat.Coprime denominator.val spec.modulus :=
      checkedEngine_xgcdGcdOne_iff spec denominator
    _ ↔ unitDecision spec denominator = true :=
      (checkedEngine_unitDecision_true_iff spec denominator).symm

theorem checkedEngine_checkedInverse_of_unitDecision_true {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (success : unitDecision spec denominator = true) :
    checkedInverse spec denominator =
      some (inverseCoefficient spec denominator) := by
  have coprime :=
    (checkedEngine_unitDecision_true_iff spec denominator).1 success
  simp [checkedInverse, coprime]

theorem checkedEngine_checkedInverse_of_unitDecision_false {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec)
    (failure : unitDecision spec denominator = false) :
    checkedInverse spec denominator = none := by
  have nonunit :=
    (checkedEngine_unitDecision_false_iff spec denominator).1 failure
  simp [checkedInverse, nonunit]

/-- The Engine-level pure result is definitionally the same checked operation
as the public pure model, with the XGCD coefficient bridge discharging the
successful branch. -/
theorem checkedEngine_checkedInverse_eq_tryInvEval {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    checkedInverse spec denominator =
      ClassicalAlgorithms.NumberTheory.TryInv.eval
        spec denominator := by
  by_cases coprime : Nat.Coprime denominator.val spec.modulus
  · simp [checkedInverse,
      ClassicalAlgorithms.NumberTheory.TryInv.eval,
      inverseCoefficient_eq_candidate spec denominator coprime]
  · simp [checkedInverse,
      ClassicalAlgorithms.NumberTheory.TryInv.eval, coprime]

/-- The shared pure result satisfies the normalization-independent checked-
inverse acceptance relation used by public endpoints. -/
theorem checkedEngine_checkedInverse_accepts {width : Nat}
    (spec : ModulusSpec width) (denominator : Residue spec) :
    ClassicalAlgorithms.NumberTheory.TryInv.accepts denominator
      (checkedInverse spec denominator) := by
  rw [checkedEngine_checkedInverse_eq_tryInvEval]
  exact
    ClassicalAlgorithms.NumberTheory.TryInv.tryInv_eval_accepts
      spec denominator

end QuantumAlg.ClassicalRoutines.NumberTheory.Checked.Engine

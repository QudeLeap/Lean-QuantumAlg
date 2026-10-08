/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters

/-!
# Pure half-power factor selection and bounded output encoding

These original source functions depend only on natural arithmetic and the
public modulus width. Actual classical recovery proves equality to them
without importing the order-finding quantum execution implementation.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery

noncomputable section

/-- Select the first nontrivial half-order GCD from one already-computed
power value.  Keeping this reduction separate from exponentiation is the
bridge between the pure boundary and the fixed-width modular-power seam. -/
def factorFromHalfPowerValue (modulus halfPower : Nat) : Option Nat :=
  let left := Nat.gcd (halfPower - 1) modulus
  if 1 < left ∧ left < modulus then
    some left
  else
    let right := Nat.gcd (halfPower + 1) modulus
    if 1 < right ∧ right < modulus then some right else none

/-- Encode the pure optional result in the bounded public output shape. -/
def encodeOutput {N : Nat} (value : Option Nat) :
    CShape.Value (.option (.unsignedWord (modulusBits N))) :=
  match value with
  | none => .optionNone
  | some factor =>
      .optionSome (CShape.wordOfNat (modulusBits N) factor)

/-- The standard public half-order gcd reduction, with the left branch taking
precedence when both branches are nontrivial. -/
def factorFromOrderValue (modulus base order : Nat) : Option Nat :=
  if 2 < modulus ∧ Even modulus then
    some 2
  else if 0 < order ∧ Even order then
    factorFromHalfPowerValue modulus (base ^ (order / 2))
  else
    none

/-- The same factor selector stated with the canonical residue physically
returned by the fixed-width modular-power seam. -/
def factorFromOrderResidueValue (modulus base order : Nat) : Option Nat :=
  if 2 < modulus ∧ Even modulus then
    some 2
  else if 0 < order ∧ Even order then
    factorFromHalfPowerValue modulus (base ^ (order / 2) % modulus)
  else
    none

/-- Every successful pure half-order branch is a nontrivial divisor. -/
theorem factorFromOrderValue_some_sound
    {modulus base order candidate : Nat}
    (result : factorFromOrderValue modulus base order = some candidate) :
    candidate ∣ modulus ∧ 1 < candidate ∧ candidate < modulus := by
  unfold factorFromOrderValue factorFromHalfPowerValue at result
  dsimp only at result
  split at result
  next evenModulus =>
    injection result with candidateEq
    subst candidate
    exact ⟨even_iff_two_dvd.mp evenModulus.2, by norm_num,
      evenModulus.1⟩
  next _oddModulus =>
    split at result
    next _validOrder =>
      split at result
      next leftValid =>
        injection result with candidateEq
        subst candidate
        exact ⟨Nat.gcd_dvd_right _ _, leftValid.1, leftValid.2⟩
      next _leftInvalid =>
        split at result
        next rightValid =>
          injection result with candidateEq
          subst candidate
          exact ⟨Nat.gcd_dvd_right _ _, rightValid.1, rightValid.2⟩
        next _rightInvalid => simp at result
    next _invalidOrder => simp at result

/-- Reducing the already-computed half power modulo the public modulus does
not change the selected nontrivial GCD.  The zero-residue case is handled
separately: its left raw GCD is one whereas the fixed-width representative
has left GCD equal to the modulus, but neither value is a valid factor. -/
theorem factorFromHalfPowerValue_mod_eq (modulus halfPower : Nat) :
    factorFromHalfPowerValue modulus (halfPower % modulus) =
      factorFromHalfPowerValue modulus halfPower := by
  by_cases halfPowerZero : halfPower = 0
  · subst halfPower
    simp [factorFromHalfPowerValue]
  by_cases remainderZero : halfPower % modulus = 0
  · let q := halfPower / modulus
    have decomposition : halfPower = modulus * q := by
      calc
        halfPower = halfPower % modulus + modulus * (halfPower / modulus) :=
          (Nat.mod_add_div halfPower modulus).symm
        _ = modulus * q := by simp [remainderZero, q]
    have productPositive : 1 ≤ modulus * q := by
      rw [← decomposition]
      exact Nat.one_le_iff_ne_zero.mpr halfPowerZero
    have leftRaw : Nat.gcd (halfPower - 1) modulus = 1 := by
      calc
        Nat.gcd (halfPower - 1) modulus =
            Nat.gcd (modulus * q - 1) modulus :=
          congrArg (fun value => Nat.gcd (value - 1) modulus) decomposition
        _ = Nat.gcd 1 modulus :=
          Nat.gcd_mul_left_sub_left productPositive
        _ = 1 := Nat.gcd_one_left _
    have rightRaw : Nat.gcd (halfPower + 1) modulus = 1 := by
      calc
        Nat.gcd (halfPower + 1) modulus =
            Nat.gcd (modulus * q + 1) modulus :=
          congrArg (fun value => Nat.gcd (value + 1) modulus) decomposition
        _ = Nat.gcd 1 modulus :=
          Nat.gcd_mul_left_add_left modulus 1 q
        _ = 1 := Nat.gcd_one_left _
    simp [factorFromHalfPowerValue, remainderZero, leftRaw, rightRaw]
  · let q := halfPower / modulus
    let r := halfPower % modulus
    have decomposition : halfPower = r + modulus * q := by
      exact (Nat.mod_add_div halfPower modulus).symm
    have remainderPositive : 0 < r :=
      Nat.pos_of_ne_zero remainderZero
    have subtractDecomposition : halfPower - 1 =
        modulus * q + (r - 1) := by
      calc
        halfPower - 1 = (r + modulus * q) - 1 :=
          congrArg (fun value => value - 1) decomposition
        _ = (modulus * q + r) - 1 := by rw [Nat.add_comm r]
        _ = modulus * q + (r - 1) :=
          Nat.add_sub_assoc (Nat.succ_le_of_lt remainderPositive) _
    have addDecomposition : halfPower + 1 =
        modulus * q + (r + 1) := by
      calc
        halfPower + 1 = (r + modulus * q) + 1 :=
          congrArg (fun value => value + 1) decomposition
        _ = modulus * q + (r + 1) := by omega
    have leftEq : Nat.gcd (halfPower - 1) modulus =
        Nat.gcd (r - 1) modulus := by
      calc
        Nat.gcd (halfPower - 1) modulus =
            Nat.gcd (modulus * q + (r - 1)) modulus :=
          congrArg (fun value => Nat.gcd value modulus) subtractDecomposition
        _ = Nat.gcd (r - 1) modulus :=
          Nat.gcd_mul_left_add_left modulus (r - 1) q
    have rightEq : Nat.gcd (halfPower + 1) modulus =
        Nat.gcd (r + 1) modulus := by
      calc
        Nat.gcd (halfPower + 1) modulus =
            Nat.gcd (modulus * q + (r + 1)) modulus :=
          congrArg (fun value => Nat.gcd value modulus) addDecomposition
        _ = Nat.gcd (r + 1) modulus :=
          Nat.gcd_mul_left_add_left modulus (r + 1) q
    unfold factorFromHalfPowerValue
    change
      (let left := Nat.gcd (r - 1) modulus
       if 1 < left ∧ left < modulus then some left
       else
         let right := Nat.gcd (r + 1) modulus
         if 1 < right ∧ right < modulus then some right else none) = _
    rw [leftEq, rightEq]

/-- The canonical residue returned by fixed-width modular powering has the
same selected GCD branch as the corresponding raw natural power. -/
theorem factorFromHalfPowerValue_pow_mod_eq
    (modulus base exponent : Nat) :
    factorFromHalfPowerValue modulus (base ^ exponent % modulus) =
      factorFromHalfPowerValue modulus (base ^ exponent) :=
  factorFromHalfPowerValue_mod_eq modulus (base ^ exponent)

/-- The fixed-width modular-power seam stores the canonical power residue,
which has the same factor-selection meaning as the raw natural power used by
the pure `outputOf` boundary. -/
theorem factorFromHalfPowerValue_modularPow_eq
    (modulus base exponent : Nat) :
    factorFromHalfPowerValue modulus ((base % modulus) ^ exponent % modulus) =
      factorFromHalfPowerValue modulus (base ^ exponent) := by
  rw [← Nat.pow_mod]
  exact factorFromHalfPowerValue_mod_eq modulus (base ^ exponent)

/-- The raw pure selector and the residue-facing selector agree exactly. -/
theorem factorFromOrderResidueValue_eq_factorFromOrderValue
    (modulus base order : Nat) :
    factorFromOrderResidueValue modulus base order =
      factorFromOrderValue modulus base order := by
  simp [factorFromOrderResidueValue, factorFromOrderValue,
    factorFromHalfPowerValue_pow_mod_eq]

/-- Machine-facing factor choice.  The shaped sampler parameter carries its
unit word and an optional early Euclidean factor; the order latch determines
whether the candidate word may enter the half-order reduction. -/
def outputOf {N : Nat} (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1)) :
    Option Nat :=
  if 2 < N ∧ Even N then
    some 2
  else if parameter.second.first.toBool = true then
    some parameter.second.second.toNat
  else if orderAccepted = true then
    factorFromOrderValue N parameter.first.toNat order.val
  else
    none

/-- Machine-facing output selection stated with the actual modular-power
residue consumed by the real GCD suffix. -/
def outputOfResidue {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1)) :
    Option Nat :=
  if 2 < N ∧ Even N then
    some 2
  else if parameter.second.first.toBool = true then
    some parameter.second.second.toNat
  else if orderAccepted = true then
    factorFromOrderResidueValue N parameter.first.toNat order.val
  else
    none

/-- The residue-facing selector is definitionally equivalent to the public
raw-power selector. -/
theorem outputOfResidue_eq_outputOf {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (orderAccepted : Bool)
    (order : ClassicalAlgorithms.Word (phaseBits N + 1)) :
    outputOfResidue parameter orderAccepted order = outputOf parameter orderAccepted order := by
  simp [outputOfResidue, outputOf,
    factorFromOrderResidueValue_eq_factorFromOrderValue]

/-- The pure factor choice consumes the optional order word.  An early
factor remains available even when terminal recovery rejects every candidate. -/
def outputOfRecovered {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (recovered :
      ClassicalAlgorithms.OrderRecovery.Output (modulusBits N) (phaseBits N)) :
    Option Nat :=
  match recovered with
  | none => outputOf parameter false
      (ClassicalAlgorithms.OrderRecovery.candidateWord (phaseBits N) 0)
  | some order => outputOf parameter true order

/-- Residue-facing form of the optional order selector.  This is the direct
semantic target of the actual `Pow.intoWord` plus GCD suffix. -/
def outputOfRecoveredResidue {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (recovered :
      ClassicalAlgorithms.OrderRecovery.Output (modulusBits N) (phaseBits N)) :
    Option Nat :=
  match recovered with
  | none => outputOfResidue parameter false
      (ClassicalAlgorithms.OrderRecovery.candidateWord (phaseBits N) 0)
  | some order => outputOfResidue parameter true order

/-- The exact result represented by the real modular-power suffix is the
public optional factor result. -/
theorem outputOfRecoveredResidue_eq_outputOfRecovered {N : Nat}
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (recovered :
      ClassicalAlgorithms.OrderRecovery.Output (modulusBits N) (phaseBits N)) :
    outputOfRecoveredResidue parameter recovered = outputOfRecovered parameter recovered := by
  cases recovered <;> simp [outputOfRecoveredResidue, outputOfRecovered,
    outputOfResidue_eq_outputOf]

/-- A selected pure result fits the public modulus-width word. -/
theorem factorFromOrderValue_some_lt_capacity
    {N base order candidate : Nat} (input : Input N)
    (result : factorFromOrderValue N base order = some candidate) :
    candidate < 2 ^ modulusBits N :=
  (factorFromOrderValue_some_sound result).2.2.trans_le input.register_fits

/-- The payload word used by a successful encoding does not truncate. -/
theorem encodeOutput_some_payload_toNat {N factor : Nat} (input : Input N)
    (fits : factor < N) :
    (CShape.wordOfNat (modulusBits N) factor).toNat = factor := by
  have capacity : factor < CShape.wordModulus (modulusBits N) :=
    fits.trans_le input.register_fits
  simp [CShape.wordOfNat_val, Nat.mod_eq_of_lt capacity]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery

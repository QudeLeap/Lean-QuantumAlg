/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.BitComplexity
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Finite continued fractions of nonnegative rationals

This module computes the finite list of distinct convergents of an exact
nonnegative rational by Euclidean recursion.  It also supplies a bit-length
bound and the dyadic specialization used by measured phase registers.
-/

section

namespace QuantumAlg
namespace RationalContinuedFraction

/-- The finite list of distinct convergents of `numerator / denominator`.
The recursive call is the continued fraction of the reciprocal fractional
part.  Once the remainder is zero the infinite mathematical sequence is
constant, so the list stops at its final distinct value. -/
def convergents (numerator denominator : Nat) : List ℚ :=
  if hdenominator : denominator = 0 then
    [0]
  else
    let integerPart : ℚ := (numerator / denominator : Nat)
    let remainder := numerator % denominator
    if hremainder : remainder = 0 then
      [integerPart]
    else
      integerPart ::
        (convergents denominator remainder).map
          (fun tail => integerPart + tail⁻¹)
termination_by denominator
decreasing_by
  exact Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)

/-- The zero-denominator convention agrees with field division by zero. -/
@[simp] lemma convergents_zero (numerator : Nat) :
    convergents numerator 0 = [0] := by
  rw [convergents]
  simp

/-- A zero remainder terminates the finite continued fraction. -/
lemma convergents_eq_singleton_of_mod_eq_zero
    {numerator denominator : Nat} (hdenominator : denominator ≠ 0)
    (hremainder : numerator % denominator = 0) :
    convergents numerator denominator =
      [((numerator / denominator : Nat) : ℚ)] := by
  rw [convergents]
  simp [hdenominator, hremainder]

/-- A nonzero remainder exposes one convergent and recurses on the reciprocal
fractional part. -/
lemma convergents_eq_cons_of_mod_ne_zero
    {numerator denominator : Nat} (hdenominator : denominator ≠ 0)
    (hremainder : numerator % denominator ≠ 0) :
    convergents numerator denominator =
      ((numerator / denominator : Nat) : ℚ) ::
        (convergents denominator (numerator % denominator)).map
          (fun tail => ((numerator / denominator : Nat) : ℚ) + tail⁻¹) := by
  rw [convergents]
  simp [hdenominator, hremainder]

/-- Two nonterminal Euclidean remainder steps reduce the first operand by
more than a factor of two. -/
private lemma secondRemainder_double_lt
    (denominator numerator : Nat) (hdenominator : 0 < denominator)
    (hremainder : 0 < numerator % denominator) :
    2 * (denominator % (numerator % denominator)) < denominator := by
  have hremainderLt : numerator % denominator < denominator :=
    Nat.mod_lt _ hdenominator
  by_cases hsmall : 2 * (numerator % denominator) ≤ denominator
  · have hnext := Nat.mod_lt denominator hremainder
    omega
  · have hremainderLe : numerator % denominator ≤ denominator :=
      Nat.le_of_lt hremainderLt
    have hsub :
        denominator - (numerator % denominator) <
          numerator % denominator := by
      omega
    rw [Nat.mod_eq_sub_mod hremainderLe, Nat.mod_eq_of_lt hsub]
    omega

/-- The binary width of the denominator drops after two nonterminal
Euclidean steps. -/
private lemma secondRemainder_size_succ_le
    (denominator numerator : Nat) (hdenominator : 0 < denominator)
    (hremainder : 0 < numerator % denominator) :
    Nat.size (denominator % (numerator % denominator)) + 1 ≤
      Nat.size denominator := by
  let next := denominator % (numerator % denominator)
  change Nat.size next + 1 ≤ Nat.size denominator
  have hdouble : 2 * next < denominator := by
    simpa [next] using
      secondRemainder_double_lt denominator numerator hdenominator hremainder
  by_cases hnext : next = 0
  · have hsizePos : 0 < Nat.size denominator :=
      Nat.size_pos.2 hdenominator
    rw [hnext, Nat.size_zero]
    omega
  · have hshift : 2 * next = next <<< 1 := by
      simp [Nat.shiftLeft_eq_mul_pow, Nat.mul_comm]
    have hdoubleSize : Nat.size (2 * next) = Nat.size next + 1 := by
      rw [hshift, Nat.size_shiftLeft hnext]
    have hmono := Nat.size_le_size (Nat.le_of_lt hdouble)
    rw [hdoubleSize] at hmono
    exact hmono

/-- Euclidean continued fractions have at most twice the denominator bit
length many distinct convergents. -/
lemma convergents_length_le (numerator denominator : Nat)
    (hdenominator : 0 < denominator) :
    (convergents numerator denominator).length ≤
      2 * Nat.size denominator := by
  induction denominator using Nat.strong_induction_on generalizing numerator with
  | h denominator ih =>
      let remainder := numerator % denominator
      by_cases hremainderZero : remainder = 0
      · rw [convergents_eq_singleton_of_mod_eq_zero
          hdenominator.ne' (by simpa [remainder] using hremainderZero)]
        simp
        have hsizePos : 0 < Nat.size denominator :=
          Nat.size_pos.2 hdenominator
        omega
      · have hremainder : 0 < remainder :=
          Nat.pos_of_ne_zero hremainderZero
        have hremainderLt : remainder < denominator := by
          simpa [remainder] using Nat.mod_lt numerator hdenominator
        rw [convergents_eq_cons_of_mod_ne_zero
          hdenominator.ne' (by simpa [remainder] using hremainderZero)]
        simp only [List.length_cons, List.length_map]
        let next := denominator % remainder
        by_cases hnextZero : next = 0
        · rw [convergents_eq_singleton_of_mod_eq_zero
            hremainder.ne' (by simpa [next] using hnextZero)]
          simp
          have hsizePos : 0 < Nat.size denominator :=
            Nat.size_pos.2 hdenominator
          omega
        · have hnext : 0 < next := Nat.pos_of_ne_zero hnextZero
          have hnextLtRemainder : next < remainder := by
            simpa [next] using Nat.mod_lt denominator hremainder
          have hnextLt : next < denominator :=
            hnextLtRemainder.trans hremainderLt
          rw [convergents_eq_cons_of_mod_ne_zero
            hremainder.ne' (by simpa [next] using hnextZero)]
          simp only [List.length_cons, List.length_map]
          have htail := ih next hnextLt remainder hnext
          have htail' :
              (convergents remainder
                (denominator % remainder)).length ≤
                  2 * Nat.size next := by
            simpa [next] using htail
          have hsize :
              Nat.size next + 1 ≤ Nat.size denominator := by
            simpa [next, remainder] using
              secondRemainder_size_succ_le
                denominator numerator hdenominator (by
                  simpa [remainder] using hremainder)
          omega

/-- Every mathematical convergent of a nonnegative rational occurs in the
finite Euclidean list.  Indices beyond termination repeat the final entry. -/
lemma real_convergent_mem (numerator denominator index : Nat) :
    (((numerator : ℝ) / (denominator : ℝ)).convergent index) ∈
      convergents numerator denominator := by
  induction denominator using Nat.strong_induction_on
      generalizing numerator index with
  | h denominator ih =>
      by_cases hdenominator : denominator = 0
      · subst denominator
        simp
      · let integerPart : ℚ := (numerator / denominator : Nat)
        let remainder := numerator % denominator
        by_cases hremainderZero : remainder = 0
        · have hnum :
              numerator = denominator * (numerator / denominator) := by
            have hdivision := Nat.mod_add_div numerator denominator
            omega
          have hratio :
              (numerator : ℝ) / (denominator : ℝ) =
                (numerator / denominator : Nat) := by
            have hcast :
                (numerator : ℝ) =
                  (denominator : ℝ) *
                    (numerator / denominator : Nat) := by
              exact_mod_cast hnum
            rw [hcast]
            field_simp
          rw [convergents_eq_singleton_of_mod_eq_zero
            hdenominator (by simpa [remainder] using hremainderZero), hratio]
          rw [List.mem_singleton]
          have hfloor :
              ⌊((numerator / denominator : Nat) : ℝ)⌋ =
                (numerator / denominator : Nat) :=
            Int.floor_natCast _
          induction index with
          | zero =>
              rw [Real.convergent_zero, hfloor]
              rfl
          | succ index _ =>
              rw [Real.convergent_succ, hfloor]
              simp only [Int.fract_natCast, inv_zero,
                Real.convergent_of_zero, add_zero]
              congr 1
        · rw [convergents_eq_cons_of_mod_ne_zero
            hdenominator (by simpa [remainder] using hremainderZero)]
          cases index with
          | zero =>
              simp only [Real.convergent_zero, List.mem_cons]
              left
              congr 1
              rw [Int.floor_div_natCast, Int.floor_natCast,
                Int.ofNat_ediv_ofNat]
          | succ index =>
              have hremainder : 0 < remainder :=
                Nat.pos_of_ne_zero hremainderZero
              have hremainderLt : remainder < denominator := by
                simpa [remainder] using
                  Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
              have hmem :=
                ih remainder hremainderLt denominator index
              have hfract :
                  Int.fract
                      ((numerator : ℝ) / (denominator : ℝ)) =
                    (remainder : ℝ) / (denominator : ℝ) := by
                simpa [remainder] using
                  (Int.fract_div_natCast_eq_div_natCast_mod
                    (k := ℝ) (m := numerator) (n := denominator))
              have hinverse :
                  ((remainder : ℝ) / (denominator : ℝ))⁻¹ =
                    (denominator : ℝ) / (remainder : ℝ) := by
                field_simp
              have hfloor :
                  ⌊(numerator : ℝ) / (denominator : ℝ)⌋ =
                    (numerator / denominator : Nat) := by
                simp [Int.floor_div_natCast]
              rw [Real.convergent_succ, hfract, hinverse, hfloor]
              exact List.mem_cons_of_mem _
                (List.mem_map_of_mem hmem)

/-- A nonnegative rational represented by a positive, reduced natural pair.
This is the executable representation used by the traced Euclidean
enumerator; its denominator therefore needs no later normalization. -/
structure ReducedRational where
  /-- Reduced nonnegative numerator. -/
  numerator : Nat
  /-- Reduced positive denominator. -/
  denominator : Nat
  /-- The stored denominator is positive. -/
  denominator_pos : 0 < denominator
  /-- The stored pair is already reduced. -/
  reduced : Nat.Coprime numerator denominator

namespace ReducedRational

/-- Rational value represented by a reduced natural pair. -/
def value (fraction : ReducedRational) : ℚ :=
  (fraction.numerator : ℚ) / fraction.denominator

/-- The denominator projection of the represented rational is exactly the
stored denominator. -/
@[simp] lemma value_den (fraction : ReducedRational) :
    fraction.value.den = fraction.denominator := by
  change
    (((fraction.numerator : Int) : ℚ) /
      ((fraction.denominator : Int) : ℚ)).den =
        fraction.denominator
  have hpositive :
      (0 : Int) < (fraction.denominator : Int) := by
    exact_mod_cast fraction.denominator_pos
  have hcoprime :
      Nat.Coprime
        (fraction.numerator : Int).natAbs
        (fraction.denominator : Int).natAbs := by
    simpa using fraction.reduced
  have hden :=
    Rat.den_div_eq_of_coprime hpositive hcoprime
  exact_mod_cast hden

/-- Reduced representation of a natural number. -/
def ofNat (value : Nat) : ReducedRational where
  numerator := value
  denominator := 1
  denominator_pos := by decide
  reduced := Nat.coprime_one_right value

@[simp] lemma ofNat_value (value : Nat) :
    (ofNat value).value = value := by
  simp [ofNat, ReducedRational.value]

end ReducedRational

/-- A positive reduced rational.  Reciprocal continued-fraction tails have
this stronger invariant, which makes the lifted denominator executable without
a proof-erasing fallback branch. -/
private structure PositiveReducedRational extends ReducedRational where
  numerator_pos : 0 < numerator

namespace PositiveReducedRational

/-- Positive reduced representation of a positive natural number. -/
private def ofNat (value : Nat) (hvalue : 0 < value) :
    PositiveReducedRational where
  numerator := value
  denominator := 1
  denominator_pos := by decide
  reduced := Nat.coprime_one_right value
  numerator_pos := hvalue

@[simp] private lemma ofNat_value (value : Nat) (hvalue : 0 < value) :
    (ofNat value hvalue).toReducedRational.value = value := by
  simp [ofNat, ReducedRational.value]

/-- Lift a positive tail value `p / d` through `q + (p / d)⁻¹`.
The new pair is reduced because `q*p+d` is coprime to `p`. -/
private def lift (integerPart : Nat)
    (tail : PositiveReducedRational) : PositiveReducedRational where
  numerator := integerPart * tail.numerator + tail.denominator
  denominator := tail.numerator
  denominator_pos := tail.numerator_pos
  reduced := by
    exact
      (Nat.coprime_mul_right_add_left
        tail.denominator tail.numerator integerPart).2
          tail.reduced.symm
  numerator_pos :=
    Nat.add_pos_right _ tail.denominator_pos

/-- The lifted pair implements the reciprocal continued-fraction step. -/
private lemma lift_value (integerPart : Nat)
    (tail : PositiveReducedRational) :
    (lift integerPart tail).toReducedRational.value =
      (integerPart : ℚ) + tail.toReducedRational.value⁻¹ := by
  have hnum : (tail.numerator : ℚ) ≠ 0 := by
    exact_mod_cast tail.numerator_pos.ne'
  have hden : (tail.denominator : ℚ) ≠ 0 := by
    exact_mod_cast tail.denominator_pos.ne'
  simp only [lift, ReducedRational.value, Nat.cast_add, Nat.cast_mul]
  field_simp

end PositiveReducedRational

/-- Result of one finite Euclidean continued-fraction execution.  The private
constructor binds its reduced values to the quotient/remainder and continuant
arithmetic emitted by the same recursion. -/
structure FiniteContinuedFractionTrace (numerator denominator : Nat) where
  private mk ::
  /-- Distinct reduced convergents, in mathematical order. -/
  fractions : List ReducedRational
  /-- Exact natural arithmetic evaluated by the Euclidean recursion and its
  reduced-pair lifts. -/
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Positive-tail variant used internally after a nonzero Euclidean
remainder. -/
private structure PositiveFiniteContinuedFractionTrace
    (numerator denominator : Nat) where
  fractions : List PositiveReducedRational
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Arithmetic used to lift every already-computed tail convergent through one
integer part. -/
private def liftArithmetic (integerPart : Nat)
    (tail : PositiveReducedRational) : List NumberTheory.ArithmeticEvent :=
  [ .natMul integerPart tail.numerator
  , .natAdd (integerPart * tail.numerator) tail.denominator ]

/-- All natural operands carried by one continued-fraction arithmetic event
are bounded by the same natural number.  This internal predicate is kept local
to the Euclidean trace because that trace emits only the five constructors
listed here. -/
private def naturalOperandsLe (bound : Nat) :
    NumberTheory.ArithmeticEvent → Prop
  | .natAdd left right | .natMul left right | .natEq left right |
      .natMod left right | .natDiv left right =>
      left ≤ bound ∧ right ≤ bound
  | _ => False

/-- Increasing a common natural-operand bound preserves the trace invariant. -/
private lemma naturalOperandsLe_mono
    {event : NumberTheory.ArithmeticEvent} {left right : Nat}
    (h : naturalOperandsLe left event) (hle : left ≤ right) :
    naturalOperandsLe right event := by
  cases event <;> simp only [naturalOperandsLe] at h ⊢
  all_goals
    first
    | contradiction
    | exact ⟨h.1.trans hle, h.2.trans hle⟩

/-- A common natural-operand bound controls the event's binary width. -/
private lemma operandWidth_le_size_of_naturalOperandsLe
    {event : NumberTheory.ArithmeticEvent} {bound : Nat}
    (h : naturalOperandsLe bound event) :
    event.operandWidth ≤ Nat.size bound := by
  cases event <;> simp only [naturalOperandsLe] at h
  all_goals
    first
    | contradiction
    | exact
        max_le (Nat.size_le_size h.1) (Nat.size_le_size h.2)

/-- Execute the positive reciprocal tail.  The proof arguments only establish
the invariant needed by the private reduced representation; they do not affect
the computed values or trace. -/
private def positiveFiniteContinuedFractionTrace
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    PositiveFiniteContinuedFractionTrace numerator denominator :=
  let integerPart := numerator / denominator
  let remainder := numerator % denominator
  let eventPrefix : List NumberTheory.ArithmeticEvent :=
    [ .natDiv numerator denominator
    , .natMod numerator denominator
    , .natEq remainder 0 ]
  if hremainder : remainder = 0 then
    .mk [PositiveReducedRational.ofNat integerPart
      (Nat.div_pos hle hdenominator)]
      eventPrefix
  else
    let tail :=
      positiveFiniteContinuedFractionTrace denominator remainder
        (Nat.pos_of_ne_zero hremainder)
        (Nat.le_of_lt (Nat.mod_lt numerator hdenominator))
    .mk
      (PositiveReducedRational.ofNat integerPart
          (Nat.div_pos hle hdenominator) ::
        tail.fractions.map
          (PositiveReducedRational.lift integerPart))
      (eventPrefix ++ tail.arithmetic ++
        tail.fractions.flatMap (liftArithmetic integerPart))
termination_by denominator
decreasing_by
  exact Nat.mod_lt numerator hdenominator

/-- Execute the finite Euclidean continued-fraction enumeration. -/
def finiteContinuedFractionTrace (numerator denominator : Nat) :
    FiniteContinuedFractionTrace numerator denominator :=
  if hdenominator : denominator = 0 then
    .mk [ReducedRational.ofNat 0] [.natEq denominator 0]
  else
    let integerPart := numerator / denominator
    let remainder := numerator % denominator
    let eventPrefix : List NumberTheory.ArithmeticEvent :=
      [ .natEq denominator 0
      , .natDiv numerator denominator
      , .natMod numerator denominator
      , .natEq remainder 0 ]
    if hremainder : remainder = 0 then
      .mk [ReducedRational.ofNat integerPart] eventPrefix
    else
      let tail :=
        positiveFiniteContinuedFractionTrace denominator remainder
          (Nat.pos_of_ne_zero hremainder)
          (Nat.le_of_lt
            (Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)))
      .mk
        (ReducedRational.ofNat integerPart ::
          (tail.fractions.map
            (PositiveReducedRational.lift integerPart)).map
              PositiveReducedRational.toReducedRational)
        (eventPrefix ++ tail.arithmetic ++
          tail.fractions.flatMap (liftArithmetic integerPart))

/-- Every reduced numerator and denominator constructed by a positive
Euclidean tail stays within the corresponding input numerator and denominator.
In particular, the continuant lift does not manufacture a denominator larger
than the preceding Euclidean numerator. -/
private lemma positiveFiniteContinuedFractionTrace_fractions_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    ∀ fraction ∈
        (positiveFiniteContinuedFractionTrace
          numerator denominator hdenominator hle).fractions,
      fraction.numerator ≤ numerator ∧
        fraction.denominator ≤ denominator := by
  induction denominator using Nat.strong_induction_on
      generalizing numerator with
  | h denominator ih =>
      rw [positiveFiniteContinuedFractionTrace]
      let integerPart := numerator / denominator
      let remainder := numerator % denominator
      by_cases hremainder : remainder = 0
      · change numerator % denominator = 0 at hremainder
        simp only [hremainder, ↓reduceDIte, List.mem_singleton]
        intro fraction hfraction
        subst fraction
        exact
          ⟨Nat.div_le_self numerator denominator,
            hdenominator⟩
      · change numerator % denominator ≠ 0 at hremainder
        have hremainderPos : 0 < remainder :=
          Nat.pos_of_ne_zero hremainder
        have hremainderLt : remainder < denominator := by
          simpa [remainder] using Nat.mod_lt numerator hdenominator
        let tail :=
          positiveFiniteContinuedFractionTrace denominator remainder
            hremainderPos (Nat.le_of_lt hremainderLt)
        have htail :
            ∀ fraction ∈ tail.fractions,
              fraction.numerator ≤ denominator ∧
                fraction.denominator ≤ remainder := by
          simpa [tail, remainder] using
            ih remainder hremainderLt denominator
              hremainderPos (Nat.le_of_lt hremainderLt)
        simp only [hremainder, ↓reduceDIte, List.mem_cons, List.mem_map]
        intro fraction hfraction
        rcases hfraction with rfl | ⟨tailFraction, htailFraction, rfl⟩
        · exact
            ⟨Nat.div_le_self numerator denominator,
              hdenominator⟩
        · have htailBounds := htail tailFraction htailFraction
          have hliftNumerator :
              integerPart * tailFraction.numerator +
                  tailFraction.denominator ≤ numerator := by
            calc
              integerPart * tailFraction.numerator +
                    tailFraction.denominator ≤
                  integerPart * denominator + remainder :=
                Nat.add_le_add
                  (Nat.mul_le_mul_left integerPart htailBounds.1)
                  htailBounds.2
              _ = numerator := by
                simpa [integerPart, remainder, Nat.mul_comm] using
                  Nat.div_add_mod numerator denominator
          exact
            ⟨hliftNumerator, htailBounds.1⟩

/-- Every arithmetic operand evaluated by a positive Euclidean tail is at most
that tail's input numerator. -/
private lemma positiveFiniteContinuedFractionTrace_naturalOperandsLe
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    ∀ event ∈
        (positiveFiniteContinuedFractionTrace
          numerator denominator hdenominator hle).arithmetic,
      naturalOperandsLe numerator event := by
  induction denominator using Nat.strong_induction_on
      generalizing numerator with
  | h denominator ih =>
      rw [positiveFiniteContinuedFractionTrace]
      let integerPart := numerator / denominator
      let remainder := numerator % denominator
      let eventPrefix : List NumberTheory.ArithmeticEvent :=
        [ .natDiv numerator denominator
        , .natMod numerator denominator
        , .natEq remainder 0 ]
      by_cases hremainder : remainder = 0
      · change numerator % denominator = 0 at hremainder
        simp only [hremainder, ↓reduceDIte]
        intro event hevent
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hevent
        rcases hevent with rfl | rfl | rfl
        · exact ⟨Nat.le_refl numerator, hle⟩
        · exact ⟨Nat.le_refl numerator, hle⟩
        · exact ⟨Nat.zero_le numerator, Nat.zero_le numerator⟩
      · change numerator % denominator ≠ 0 at hremainder
        have hremainderPos : 0 < remainder :=
          Nat.pos_of_ne_zero hremainder
        have hremainderLt : remainder < denominator := by
          simpa [remainder] using Nat.mod_lt numerator hdenominator
        let tail :=
          positiveFiniteContinuedFractionTrace denominator remainder
            hremainderPos (Nat.le_of_lt hremainderLt)
        have htail :
            ∀ event ∈ tail.arithmetic,
              naturalOperandsLe numerator event := by
          intro event hevent
          exact naturalOperandsLe_mono
            (by
              simpa [tail, remainder] using
                ih remainder hremainderLt denominator
                  hremainderPos (Nat.le_of_lt hremainderLt)
                    event hevent)
            hle
        have hfractions :
            ∀ fraction ∈ tail.fractions,
              fraction.numerator ≤ denominator ∧
                fraction.denominator ≤ remainder := by
          simpa [tail, remainder] using
            positiveFiniteContinuedFractionTrace_fractions_le
              denominator remainder hremainderPos
                (Nat.le_of_lt hremainderLt)
        simp only [hremainder, ↓reduceDIte, List.mem_append,
          List.mem_flatMap]
        intro event hevent
        rcases hevent with (hprefix | htailEvent) | hliftEvent
        · simp only [List.mem_cons, List.not_mem_nil,
            or_false] at hprefix
          rcases hprefix with rfl | rfl | rfl
          · exact ⟨Nat.le_refl numerator, hle⟩
          · exact ⟨Nat.le_refl numerator, hle⟩
          · exact ⟨Nat.mod_le numerator denominator, Nat.zero_le numerator⟩
        · exact htail event htailEvent
        · rcases hliftEvent with
            ⟨tailFraction, htailFraction, hevent⟩
          have htailBounds :=
            hfractions tailFraction htailFraction
          have hintegerPart : integerPart ≤ numerator :=
            Nat.div_le_self numerator denominator
          have htailNumerator :
              tailFraction.numerator ≤ numerator :=
            htailBounds.1.trans hle
          have hliftProduct :
              integerPart * tailFraction.numerator ≤ numerator := by
            exact
              (Nat.mul_le_mul_left integerPart htailBounds.1).trans
                (by
                  simpa [integerPart] using
                    Nat.div_mul_le_self numerator denominator)
          have htailDenominator :
              tailFraction.denominator ≤ numerator :=
            htailBounds.2.trans
              ((Nat.le_of_lt hremainderLt).trans hle)
          simp only [liftArithmetic, List.mem_cons,
            List.not_mem_nil, or_false] at hevent
          rcases hevent with rfl | rfl
          · exact ⟨hintegerPart, htailNumerator⟩
          · exact ⟨hliftProduct, htailDenominator⟩

/-- With a positive denominator that already bounds the numerator, every
reduced denominator constructed by the complete Euclidean trace stays within
that input denominator. -/
private lemma finiteContinuedFractionTrace_denominator_le_of_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (_hle : numerator ≤ denominator) :
    ∀ fraction ∈
        (finiteContinuedFractionTrace numerator denominator).fractions,
      fraction.denominator ≤ denominator := by
  rw [finiteContinuedFractionTrace]
  have hdenominatorNe : denominator ≠ 0 := hdenominator.ne'
  let integerPart := numerator / denominator
  let remainder := numerator % denominator
  by_cases hremainder : remainder = 0
  · change numerator % denominator = 0 at hremainder
    simp only [hdenominatorNe, hremainder, ↓reduceDIte,
      List.mem_singleton]
    intro fraction hfraction
    subst fraction
    exact hdenominator
  · change numerator % denominator ≠ 0 at hremainder
    have hremainderPos : 0 < remainder :=
      Nat.pos_of_ne_zero hremainder
    have hremainderLt : remainder < denominator := by
      simpa [remainder] using Nat.mod_lt numerator hdenominator
    let tail :=
      positiveFiniteContinuedFractionTrace denominator remainder
        hremainderPos (Nat.le_of_lt hremainderLt)
    have htail :
        ∀ fraction ∈ tail.fractions,
          fraction.numerator ≤ denominator ∧
            fraction.denominator ≤ remainder := by
      simpa [tail, remainder] using
        positiveFiniteContinuedFractionTrace_fractions_le
          denominator remainder hremainderPos
            (Nat.le_of_lt hremainderLt)
    simp only [hdenominatorNe, hremainder, ↓reduceDIte,
      List.mem_cons, List.mem_map]
    intro fraction hfraction
    rcases hfraction with rfl |
        ⟨lifted, hlifted, rfl⟩
    · exact hdenominator
    · rcases hlifted with ⟨tailFraction, htailFraction, rfl⟩
      exact (htail tailFraction htailFraction).1

/-- With a positive denominator that bounds the numerator, every arithmetic
operand of the complete Euclidean trace is bounded by that denominator. -/
private lemma finiteContinuedFractionTrace_naturalOperandsLe_of_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : numerator ≤ denominator) :
    ∀ event ∈
        (finiteContinuedFractionTrace numerator denominator).arithmetic,
      naturalOperandsLe denominator event := by
  rw [finiteContinuedFractionTrace]
  have hdenominatorNe : denominator ≠ 0 := hdenominator.ne'
  let integerPart := numerator / denominator
  let remainder := numerator % denominator
  let eventPrefix : List NumberTheory.ArithmeticEvent :=
    [ .natEq denominator 0
    , .natDiv numerator denominator
    , .natMod numerator denominator
    , .natEq remainder 0 ]
  by_cases hremainder : remainder = 0
  · change numerator % denominator = 0 at hremainder
    simp only [hdenominatorNe, hremainder, ↓reduceDIte]
    intro event hevent
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hevent
    rcases hevent with rfl | rfl | rfl | rfl
    · exact ⟨Nat.le_refl denominator, Nat.zero_le denominator⟩
    · exact ⟨hle, Nat.le_refl denominator⟩
    · exact ⟨hle, Nat.le_refl denominator⟩
    · exact ⟨Nat.zero_le denominator, Nat.zero_le denominator⟩
  · change numerator % denominator ≠ 0 at hremainder
    have hremainderPos : 0 < remainder :=
      Nat.pos_of_ne_zero hremainder
    have hremainderLt : remainder < denominator := by
      simpa [remainder] using Nat.mod_lt numerator hdenominator
    let tail :=
      positiveFiniteContinuedFractionTrace denominator remainder
        hremainderPos (Nat.le_of_lt hremainderLt)
    have htail :
        ∀ event ∈ tail.arithmetic,
          naturalOperandsLe denominator event := by
      simpa [tail, remainder] using
        positiveFiniteContinuedFractionTrace_naturalOperandsLe
          denominator remainder hremainderPos
            (Nat.le_of_lt hremainderLt)
    have hfractions :
        ∀ fraction ∈ tail.fractions,
          fraction.numerator ≤ denominator ∧
            fraction.denominator ≤ remainder := by
      simpa [tail, remainder] using
        positiveFiniteContinuedFractionTrace_fractions_le
          denominator remainder hremainderPos
            (Nat.le_of_lt hremainderLt)
    simp only [hdenominatorNe, hremainder, ↓reduceDIte,
      List.mem_append, List.mem_flatMap]
    intro event hevent
    rcases hevent with (hprefix | htailEvent) | hliftEvent
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at hprefix
      rcases hprefix with rfl | rfl | rfl | rfl
      · exact ⟨Nat.le_refl denominator, Nat.zero_le denominator⟩
      · exact ⟨hle, Nat.le_refl denominator⟩
      · exact ⟨hle, Nat.le_refl denominator⟩
      · exact
          ⟨Nat.le_of_lt
              (Nat.mod_lt numerator hdenominator),
            Nat.zero_le denominator⟩
    · exact htail event htailEvent
    · rcases hliftEvent with
        ⟨tailFraction, htailFraction, hevent⟩
      have htailBounds :=
        hfractions tailFraction htailFraction
      have hintegerPart : integerPart ≤ denominator :=
        (Nat.div_le_self numerator denominator).trans hle
      have hliftProduct :
          integerPart * tailFraction.numerator ≤ denominator := by
        calc
          integerPart * tailFraction.numerator ≤
              integerPart * denominator :=
            Nat.mul_le_mul_left integerPart htailBounds.1
          _ ≤ numerator := by
            simpa [integerPart] using
              Nat.div_mul_le_self numerator denominator
          _ ≤ denominator := hle
      have htailDenominator :
          tailFraction.denominator ≤ denominator :=
        htailBounds.2.trans (Nat.le_of_lt hremainderLt)
      simp only [liftArithmetic, List.mem_cons,
        List.not_mem_nil, or_false] at hevent
      rcases hevent with rfl | rfl
      · exact ⟨hintegerPart, htailBounds.1⟩
      · exact ⟨hliftProduct, htailDenominator⟩

/-- The positive trace values agree with the mathematical recursive
convergents. -/
private lemma positiveFiniteContinuedFractionTrace_values
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    ((positiveFiniteContinuedFractionTrace
      numerator denominator hdenominator hle).fractions.map
        (fun fraction => fraction.toReducedRational.value)) =
      convergents numerator denominator := by
  induction denominator using Nat.strong_induction_on
      generalizing numerator with
  | h denominator ih =>
      rw [positiveFiniteContinuedFractionTrace]
      let integerPart := numerator / denominator
      let remainder := numerator % denominator
      by_cases hremainder : remainder = 0
      · change numerator % denominator = 0 at hremainder
        simp [hremainder,
          PositiveReducedRational.ofNat_value,
          convergents_eq_singleton_of_mod_eq_zero hdenominator.ne'
            hremainder]
      · change numerator % denominator ≠ 0 at hremainder
        have hremainderPos : 0 < remainder :=
          Nat.pos_of_ne_zero hremainder
        have hremainderLt : remainder < denominator := by
          simpa [remainder] using Nat.mod_lt numerator hdenominator
        have htail :=
          ih remainder hremainderLt denominator
            hremainderPos (Nat.le_of_lt hremainderLt)
        rw [convergents_eq_cons_of_mod_ne_zero hdenominator.ne'
          hremainder]
        simp only [hremainder, ↓reduceDIte, List.map_cons, List.map_map]
        congr 1
        · simp [PositiveReducedRational.ofNat,
            ReducedRational.value]
        · rw [← htail, List.map_map]
          apply List.map_congr_left
          intro fraction hfraction
          simpa [Function.comp_apply] using
            PositiveReducedRational.lift_value integerPart fraction

/-- The executable reduced values agree exactly with the mathematical
continued-fraction specification. -/
lemma finiteContinuedFractionTrace_values
    (numerator denominator : Nat) :
    ((finiteContinuedFractionTrace numerator denominator).fractions.map
      ReducedRational.value) =
        convergents numerator denominator := by
  rw [finiteContinuedFractionTrace]
  by_cases hdenominator : denominator = 0
  · simp [hdenominator]
  · let integerPart := numerator / denominator
    let remainder := numerator % denominator
    by_cases hremainder : remainder = 0
    · change numerator % denominator = 0 at hremainder
      simp [hdenominator, hremainder,
        convergents_eq_singleton_of_mod_eq_zero hdenominator hremainder]
    · change numerator % denominator ≠ 0 at hremainder
      have hremainderPos : 0 < remainder :=
        Nat.pos_of_ne_zero hremainder
      have hremainderLt : remainder < denominator := by
        simpa [remainder] using
          Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
      have htail :=
        positiveFiniteContinuedFractionTrace_values
          denominator remainder hremainderPos
            (Nat.le_of_lt hremainderLt)
      rw [convergents_eq_cons_of_mod_ne_zero hdenominator
        hremainder]
      simp only [hdenominator, hremainder, ↓reduceDIte, List.map_cons,
        List.map_map]
      congr 1
      · simp [ReducedRational.ofNat_value]
      · rw [← htail, List.map_map]
        apply List.map_congr_left
        intro fraction hfraction
        simpa [Function.comp_apply] using
          PositiveReducedRational.lift_value integerPart fraction

/-- Lifting every already-computed tail convergent emits exactly one
multiplication and one addition per fraction. -/
private lemma liftArithmetic_flatMap_length
    (integerPart : Nat) (fractions : List PositiveReducedRational) :
    (fractions.flatMap (liftArithmetic integerPart)).length =
      2 * fractions.length := by
  induction fractions with
  | nil => rfl
  | cons fraction fractions ih =>
      simp [liftArithmetic, ih]
      omega

/-- The backward Euclidean execution emits at most quadratically many events
in the number of positive-tail convergents it actually constructs. -/
private lemma positiveFiniteContinuedFractionTrace_arithmetic_length_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    (positiveFiniteContinuedFractionTrace
        numerator denominator hdenominator hle).arithmetic.length ≤
      3 *
        (positiveFiniteContinuedFractionTrace
          numerator denominator hdenominator hle).fractions.length ^ 2 := by
  induction denominator using Nat.strong_induction_on
      generalizing numerator with
  | h denominator ih =>
      rw [positiveFiniteContinuedFractionTrace]
      let remainder := numerator % denominator
      by_cases hremainder : remainder = 0
      · change numerator % denominator = 0 at hremainder
        simp [hremainder]
      · change numerator % denominator ≠ 0 at hremainder
        have hremainderLt : numerator % denominator < denominator :=
          Nat.mod_lt numerator hdenominator
        have htail :
            (positiveFiniteContinuedFractionTrace denominator
                (numerator % denominator)
                (Nat.pos_of_ne_zero hremainder)
                (Nat.le_of_lt hremainderLt)).arithmetic.length ≤
              3 *
                (positiveFiniteContinuedFractionTrace denominator
                  (numerator % denominator)
                  (Nat.pos_of_ne_zero hremainder)
                  (Nat.le_of_lt hremainderLt)).fractions.length ^ 2 := by
          exact ih (numerator % denominator) hremainderLt denominator
            (Nat.pos_of_ne_zero hremainder)
            (Nat.le_of_lt hremainderLt)
        simp only [hremainder, ↓reduceDIte, List.length_cons,
          List.length_nil, List.length_map, List.length_append,
          Nat.zero_add,
          liftArithmetic_flatMap_length]
        nlinarith

/-- The complete Euclidean execution emits at most quadratically many events
in the number of reduced convergents it actually constructs. -/
lemma finiteContinuedFractionTrace_arithmetic_length_le
    (numerator denominator : Nat) :
    (finiteContinuedFractionTrace numerator denominator).arithmetic.length ≤
      4 *
        (finiteContinuedFractionTrace
          numerator denominator).fractions.length ^ 2 := by
  rw [finiteContinuedFractionTrace]
  by_cases hdenominator : denominator = 0
  · simp [hdenominator]
  · let remainder := numerator % denominator
    by_cases hremainder : remainder = 0
    · change numerator % denominator = 0 at hremainder
      simp [hdenominator, hremainder]
    · change numerator % denominator ≠ 0 at hremainder
      have hremainderLt : numerator % denominator < denominator :=
        Nat.mod_lt numerator (Nat.pos_of_ne_zero hdenominator)
      have htail :
          (positiveFiniteContinuedFractionTrace denominator
              (numerator % denominator)
              (Nat.pos_of_ne_zero hremainder)
              (Nat.le_of_lt hremainderLt)).arithmetic.length ≤
            3 *
              (positiveFiniteContinuedFractionTrace denominator
                (numerator % denominator)
                (Nat.pos_of_ne_zero hremainder)
                (Nat.le_of_lt hremainderLt)).fractions.length ^ 2 :=
        positiveFiniteContinuedFractionTrace_arithmetic_length_le
          denominator (numerator % denominator)
            (Nat.pos_of_ne_zero hremainder)
            (Nat.le_of_lt hremainderLt)
      simp only [hdenominator, hremainder, ↓reduceDIte,
        List.length_cons, List.length_nil, List.length_map,
        List.length_append, Nat.zero_add,
        liftArithmetic_flatMap_length]
      nlinarith

/-- Number of fixed Euclidean slots used for a `phaseBits`-bit dyadic
measurement. -/
def dyadicFuel (phaseBits : Nat) : Nat :=
  2 * phaseBits + 2

/-- The public fixed schedule fits in one additional binary digit beyond the
phase register. -/
private lemma dyadicFuel_le_two_pow_succ (phaseBits : Nat) :
    dyadicFuel phaseBits ≤ 2 ^ (phaseBits + 1) := by
  induction phaseBits with
  | zero => simp [dyadicFuel]
  | succ phaseBits ih =>
      have htwo : 2 ≤ 2 ^ (phaseBits + 1) := by
        simpa using
          Nat.pow_le_pow_right (by decide : 0 < 2)
            (Nat.succ_le_succ (Nat.zero_le phaseBits))
      rw [show Nat.succ phaseBits + 1 = (phaseBits + 1) + 1 by omega,
        pow_succ]
      simp only [dyadicFuel] at ih ⊢
      omega

/-- A fixed-fuel dyadic execution.  Padding repeats the last already-computed
reduced convergent; the trace records the subtraction that determines the
padding length. -/
structure DyadicContinuedFractionTrace
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) where
  private mk ::
  /-- Fixed-length reduced convergent schedule. -/
  fractions : List ReducedRational
  /-- Exact arithmetic of the finite Euclidean enumeration and the
  fixed-schedule padding-length subtraction. -/
  arithmetic : List NumberTheory.ArithmeticEvent

/-- Execute and pad the exact dyadic continued-fraction enumeration. -/
def dyadicContinuedFractionTrace {phaseBits : Nat}
    (numerator : Fin (2 ^ phaseBits)) :
    DyadicContinuedFractionTrace numerator :=
  let finite := finiteContinuedFractionTrace numerator.val (2 ^ phaseBits)
  let padding :=
    List.replicate (dyadicFuel phaseBits - finite.fractions.length)
      (finite.fractions.getLastD (ReducedRational.ofNat 0))
  .mk (finite.fractions ++ padding)
    (finite.arithmetic ++
      [.natSub (dyadicFuel phaseBits) finite.fractions.length])

/-- Candidate denominators are direct projections of the sealed reduced
execution, not a separately normalized rational list. -/
def DyadicContinuedFractionTrace.denominators
    {phaseBits : Nat} {numerator : Fin (2 ^ phaseBits)}
    (trace : DyadicContinuedFractionTrace numerator) : List Nat :=
  trace.fractions.map ReducedRational.denominator

/-- The fixed dyadic trace contains exactly `2t+2` denominator slots. -/
lemma dyadicContinuedFractionTrace_fractions_length
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) :
    (dyadicContinuedFractionTrace numerator).fractions.length =
      dyadicFuel phaseBits := by
  have hbound :
      (finiteContinuedFractionTrace
        numerator.val (2 ^ phaseBits)).fractions.length ≤
        dyadicFuel phaseBits := by
    rw [← List.length_map,
      finiteContinuedFractionTrace_values]
    simpa [dyadicFuel, Nat.size_pow, Nat.mul_add] using
      convergents_length_le numerator.val (2 ^ phaseBits) (by positivity)
  simp only [dyadicContinuedFractionTrace, List.length_append,
    List.length_replicate]
  omega

/-- The denominator projection preserves the fixed slot count. -/
lemma dyadicContinuedFractionTrace_denominators_length
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) :
    (dyadicContinuedFractionTrace numerator).denominators.length =
      dyadicFuel phaseBits := by
  simp [DyadicContinuedFractionTrace.denominators,
    dyadicContinuedFractionTrace_fractions_length]

/-- Every reduced denominator in the padded dyadic execution is at most the
phase-register cardinality.  Padding repeats an already-computed fraction and
therefore preserves the same mathematical bound. -/
lemma dyadicContinuedFractionTrace_fraction_denominator_le
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits))
    {fraction : ReducedRational}
    (hfraction :
      fraction ∈ (dyadicContinuedFractionTrace numerator).fractions) :
    fraction.denominator ≤ 2 ^ phaseBits := by
  let finite :=
    finiteContinuedFractionTrace numerator.val (2 ^ phaseBits)
  let fallback := ReducedRational.ofNat 0
  have hfinite :
      ∀ candidate ∈ finite.fractions,
        candidate.denominator ≤ 2 ^ phaseBits := by
    simpa [finite] using
      finiteContinuedFractionTrace_denominator_le_of_le
        numerator.val (2 ^ phaseBits) (by positivity)
          (Nat.le_of_lt numerator.isLt)
  have hlast :
      (finite.fractions.getLastD fallback).denominator ≤
        2 ^ phaseBits := by
    cases hfractions : finite.fractions with
    | nil =>
        simp only [List.getLastD_eq_getLast?, List.getLast?_nil,
          Option.getD_none]
        exact Nat.one_le_two_pow
    | cons head tail =>
        have hbound :=
          hfinite (tail.getLastD head) (by
            rw [hfractions]
            exact List.getLastD_mem_cons)
        rw [List.getLastD_cons]
        exact hbound
  change
    fraction ∈
      finite.fractions ++
        List.replicate
          (dyadicFuel phaseBits - finite.fractions.length)
          (finite.fractions.getLastD fallback) at hfraction
  rcases List.mem_append.mp hfraction with hcomputed | hpadded
  · exact hfinite fraction hcomputed
  · have heq :
        fraction = finite.fractions.getLastD fallback :=
      List.eq_of_mem_replicate hpadded
    simpa [heq] using hlast

/-- Every projected denominator slot in the fixed dyadic schedule is at most
the phase-register cardinality. -/
lemma dyadicContinuedFractionTrace_denominator_le
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits))
    {denominator : Nat}
    (hdenominator :
      denominator ∈
        (dyadicContinuedFractionTrace numerator).denominators) :
    denominator ≤ 2 ^ phaseBits := by
  unfold DyadicContinuedFractionTrace.denominators at hdenominator
  rcases List.mem_map.mp hdenominator with
    ⟨fraction, hfraction, rfl⟩
  exact
    dyadicContinuedFractionTrace_fraction_denominator_le
      numerator hfraction

/-- Every operand actually evaluated by the exact dyadic Euclidean trace and
its fixed-schedule padding computation fits in at most `phaseBits + 2` binary
digits. -/
lemma dyadicContinuedFractionTrace_maxOperandWidth_le
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) :
    NumberTheory.arithmeticEventListMaxOperandWidth
        (dyadicContinuedFractionTrace numerator).arithmetic ≤
      phaseBits + 2 := by
  let finite :=
    finiteContinuedFractionTrace numerator.val (2 ^ phaseBits)
  have hfiniteLength :
      finite.fractions.length ≤ dyadicFuel phaseBits := by
    rw [← List.length_map, finiteContinuedFractionTrace_values]
    simpa [finite, dyadicFuel, Nat.size_pow, Nat.mul_add] using
      convergents_length_le numerator.val (2 ^ phaseBits) (by positivity)
  apply NumberTheory.arithmeticEventListMaxOperandWidth_le
  intro event hevent
  change event ∈
    finite.arithmetic ++
      [.natSub (dyadicFuel phaseBits) finite.fractions.length] at hevent
  rcases List.mem_append.mp hevent with hfiniteEvent | hpadding
  · have hoperands :
        naturalOperandsLe (2 ^ phaseBits) event :=
      finiteContinuedFractionTrace_naturalOperandsLe_of_le
        numerator.val (2 ^ phaseBits) (by positivity)
          (Nat.le_of_lt numerator.isLt) event hfiniteEvent
    exact
      (operandWidth_le_size_of_naturalOperandsLe hoperands).trans
        (by simp [Nat.size_pow])
  · have hevent :
        event =
          .natSub (dyadicFuel phaseBits) finite.fractions.length :=
      List.eq_of_mem_singleton hpadding
    subst event
    simp only [NumberTheory.ArithmeticEvent.operandWidth]
    apply max_le
    · exact
        (Nat.size_le_size (dyadicFuel_le_two_pow_succ phaseBits)).trans
          (by simp [Nat.size_pow])
    · exact
        (Nat.size_le_size
          (hfiniteLength.trans
            (dyadicFuel_le_two_pow_succ phaseBits))).trans
          (by simp [Nat.size_pow])

/-- The exact dyadic Euclidean and continuant trace has quadratic event count
in the public phase-register width. -/
lemma dyadicContinuedFractionTrace_arithmetic_length_le
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) :
    (dyadicContinuedFractionTrace numerator).arithmetic.length ≤
      17 * (phaseBits + 1) ^ 2 := by
  let finite :=
    finiteContinuedFractionTrace numerator.val (2 ^ phaseBits)
  have htrace :=
    finiteContinuedFractionTrace_arithmetic_length_le
      numerator.val (2 ^ phaseBits)
  have hfractions :
      finite.fractions.length ≤ 2 * (phaseBits + 1) := by
    rw [← List.length_map, finiteContinuedFractionTrace_values]
    simpa [finite, Nat.size_pow] using
      convergents_length_le numerator.val (2 ^ phaseBits) (by positivity)
  change
    (finite.arithmetic ++
      [NumberTheory.ArithmeticEvent.natSub
        (dyadicFuel phaseBits) finite.fractions.length]).length ≤
        17 * (phaseBits + 1) ^ 2
  simp only [List.length_append, List.length_singleton]
  calc
    finite.arithmetic.length + 1 ≤
        4 * finite.fractions.length ^ 2 + 1 :=
      Nat.add_le_add_right htrace 1
    _ ≤ 4 * (2 * (phaseBits + 1)) ^ 2 + 1 :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hfractions 2)) 1
    _ ≤ 17 * (phaseBits + 1) ^ 2 := by
      have hpositive : 1 ≤ phaseBits + 1 := by omega
      nlinarith

/-- Every mathematical convergent denominator occurs in the actual fixed
dyadic execution. -/
lemma real_convergent_den_mem_dyadicTrace
    {phaseBits : Nat} (numerator : Fin (2 ^ phaseBits)) (index : Nat) :
    ((((numerator.val : ℝ) / (2 : ℝ) ^ phaseBits).convergent index).den) ∈
      (dyadicContinuedFractionTrace numerator).denominators := by
  have hmem :=
    real_convergent_mem numerator.val (2 ^ phaseBits) index
  have hfinite :
      (((numerator.val : ℝ) / (2 : ℝ) ^ phaseBits).convergent index) ∈
        (finiteContinuedFractionTrace
          numerator.val (2 ^ phaseBits)).fractions.map
            ReducedRational.value := by
    rw [finiteContinuedFractionTrace_values]
    simpa using hmem
  rcases List.mem_map.mp hfinite with
    ⟨fraction, hfraction, hvalue⟩
  unfold DyadicContinuedFractionTrace.denominators
  apply List.mem_map.mpr
  refine ⟨fraction, ?_, ?_⟩
  · simpa [dyadicContinuedFractionTrace] using
      (List.mem_append_left
        (List.replicate
          (dyadicFuel phaseBits -
            (finiteContinuedFractionTrace
              numerator.val (2 ^ phaseBits)).fractions.length)
          ((finiteContinuedFractionTrace
            numerator.val (2 ^ phaseBits)).fractions.getLastD
              (ReducedRational.ofNat 0)))
        hfraction)
  · rw [← ReducedRational.value_den, hvalue]

/-- Executable dyadic regression for the phase numerator `5/64`.  The true
order four is not present in this observation's fixed convergent schedule. -/
lemma dyadicContinuedFractionTrace_five_of_six_denominators :
    (dyadicContinuedFractionTrace
      (⟨5, by norm_num⟩ : Fin (2 ^ 6))).denominators =
      [1, 12, 13, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64] := by
  have hconvergents :
      convergents 5 64 =
        [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13, (5 : ℚ) / 64] := by
    rw [convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [convergents_eq_singleton_of_mod_eq_zero
      (by norm_num) (by norm_num)]
    norm_num
  have hvalues :
      (finiteContinuedFractionTrace 5 64).fractions.map
          ReducedRational.value =
        [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13, (5 : ℚ) / 64] := by
    rw [finiteContinuedFractionTrace_values, hconvergents]
  have hdenominators :
      (finiteContinuedFractionTrace 5 64).fractions.map
          ReducedRational.denominator =
        [1, 12, 13, 64] := by
    have hfive : (((5 : ℚ) / 64).den) = 64 := by
      change ((((5 : Int) : ℚ) / ((64 : Int) : ℚ)).den) = 64
      have hfiveInt :=
        Rat.den_div_eq_of_coprime
          (a := 5) (b := 64) (by norm_num)
            (by decide : Nat.Coprime (5 : Int).natAbs (64 : Int).natAbs)
      exact_mod_cast hfiveInt
    calc
      (finiteContinuedFractionTrace 5 64).fractions.map
          ReducedRational.denominator =
          ((finiteContinuedFractionTrace 5 64).fractions.map
            ReducedRational.value).map (fun value : ℚ => value.den) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro fraction _hmem
            exact (ReducedRational.value_den fraction).symm
      _ = [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13,
          (5 : ℚ) / 64].map (fun value : ℚ => value.den) := by
            rw [hvalues]
      _ = [1, 12, 13, 64] := by
            simp [hfive]
  have hlength :
      (finiteContinuedFractionTrace 5 64).fractions.length = 4 := by
    have hlength' := congrArg List.length hdenominators
    simpa using hlength'
  have hmapLast :
      ((finiteContinuedFractionTrace 5 64).fractions.map
          ReducedRational.denominator).getLastD 1 =
        ((finiteContinuedFractionTrace 5 64).fractions.getLastD
          (ReducedRational.ofNat 0)).denominator := by
    simpa [ReducedRational.ofNat] using
      (List.getLastD_map
        (f := ReducedRational.denominator)
        (l := (finiteContinuedFractionTrace 5 64).fractions)
        (a := ReducedRational.ofNat 0))
  have hlast :
      ((finiteContinuedFractionTrace 5 64).fractions.getLastD
        (ReducedRational.ofNat 0)).denominator = 64 := by
    rw [← hmapLast, hdenominators]
    norm_num
  simp only [DyadicContinuedFractionTrace.denominators,
    dyadicContinuedFractionTrace, List.map_append, List.map_replicate,
    Fin.val_mk]
  rw [show 2 ^ 6 = 64 by norm_num]
  rw [hdenominators, hlength, hlast]
  norm_num [dyadicFuel]
  decide

end RationalContinuedFraction
end QuantumAlg

end

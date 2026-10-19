/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Classical.Modular.Basic
public import Batteries.Tactic.Lint.Misc
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Util.Classical.Modular.Additive
import all QuantumAlg.Util.NumberTheory.RationalContinuedFraction

/-!
# Typed finite continued-fraction order recovery

This module gives the pure, fixed-width post-processing contract for one
terminal phase measurement. It decodes that measurement in big-endian order,
enumerates the finite continued-fraction trace, and validates every denominator
produced by that trace in order. Validation stops at the first accepted
candidate; rejected candidates before that point remain in the exposed path.

The exposed path is a pure candidate-validation path. It is not a Components
execution trace and carries no physical resource, space, or depth claim.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace OrderRecovery

open Modular

/-- The fixed terminal bit vector read from a phase register. -/
public abbrev TerminalBits (phaseBits : Nat) : Type := Fin phaseBits → Bool

/-- Canonical full-register recovery is the typed big-endian terminal decoder. -/
def fullRegisterIndex {phaseBits : Nat} (bits : TerminalBits phaseBits) :
    Word phaseBits :=
  TerminalDecode.fullRegisterIndex bits

/-- The canonical full-register name is a transparent bridge to the typed
terminal decoder. -/
lemma fullRegisterIndex_eq_terminalDecode_bigEndian {phaseBits : Nat}
    (bits : TerminalBits phaseBits) :
    fullRegisterIndex bits =
      TerminalDecode.eval
        ({ order := .bigEndian, bits := bits } : TerminalDecode.Input phaseBits) :=
  rfl

/-- Big-endian terminal decoding agrees with the library-wide finite-index
convention. -/
lemma fullRegisterIndex_val {phaseBits : Nat}
    (bits : TerminalBits phaseBits) :
    (fullRegisterIndex bits).val = Nat.ofBits (bits ∘ Fin.rev) :=
  TerminalDecode.fullRegisterIndex_val bits

/-- The fixed big-endian terminal bits representing one bounded index. -/
def terminalMeasurement (phaseBits : Nat) (value : Word phaseBits) :
    TerminalBits phaseBits :=
  fun outputIndex => value.val.testBit (phaseBits - 1 - outputIndex.val)

/-- Decoding the canonical big-endian terminal bits recovers the original
fixed-width index. -/
lemma fullRegisterIndex_terminalMeasurement (phaseBits : Nat)
    (value : Word phaseBits) :
    fullRegisterIndex (terminalMeasurement phaseBits value) = value := by
  apply Fin.val_injective
  rw [fullRegisterIndex_val]
  have hbits :
      (terminalMeasurement phaseBits value) ∘ Fin.rev =
        fun bit : Fin phaseBits => value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, terminalMeasurement]
    apply congrArg value.val.testBit
    calc
      phaseBits - 1 - (Fin.rev bit).val =
          phaseBits - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

/-- Static modulus data for fixed-width order recovery. -/
public structure Spec (modulusWidth phaseBits : Nat) where
  /-- The nontrivial modulus and its declared storage bound. -/
  modulusSpec : ModulusSpec modulusWidth

/-- A typed base and a terminal phase measurement for one recovery attempt. -/
public structure Input {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) where
  /-- The base is stored in the declared fixed-width word. -/
  base : Word modulusWidth
  /-- The stored word denotes a canonical residue for this modulus. -/
  baseInDomain : base.val < spec.modulusSpec.modulus
  /-- Order recovery is defined only for a witnessed unit base. -/
  baseCoprime : Nat.Coprime base.val spec.modulusSpec.modulus
  /-- Raw terminal bits; `decodedIndex` fixes their big-endian interpretation. -/
  terminalBits : TerminalBits phaseBits

/-- The canonical residue denoted by the fixed-width input base. -/
def Input.baseResidue {modulusWidth phaseBits : Nat}
    {spec : Spec modulusWidth phaseBits} (input : Input spec) :
    Residue spec.modulusSpec :=
  ⟨input.base.val, input.baseInDomain⟩

/-- Recovery returns either no accepted denominator or one word with the
declared `phaseBits + 1` candidate width.  The modulus-width parameter keeps
the endpoint carrier aligned with `Spec` and `Input`; it does not affect this
terminal encoding. -/
@[nolint unusedArguments]
public abbrev Output (_modulusWidth phaseBits : Nat) : Type :=
  Option (Word (phaseBits + 1))

/-- The big-endian finite index used as the measured dyadic numerator. -/
def decodedIndex {modulusWidth phaseBits : Nat}
    {spec : Spec modulusWidth phaseBits} (input : Input spec) :
    Word phaseBits :=
  fullRegisterIndex input.terminalBits

/-- The unpadded continued-fraction execution for the decoded dyadic value. -/
def finiteContinuedFraction {modulusWidth phaseBits : Nat}
    {spec : Spec modulusWidth phaseBits} (input : Input spec) :
    RationalContinuedFraction.FiniteContinuedFractionTrace
      (decodedIndex input).val (2 ^ phaseBits) :=
  RationalContinuedFraction.finiteContinuedFractionTrace
    (decodedIndex input).val (2 ^ phaseBits)

/-- Actual denominator candidates in finite continued-fraction order. This is
not the padded dyadic schedule: every entry comes from a genuine convergent,
including any repeated denominator produced by distinct convergents. -/
def finiteCandidates {phaseBits : Nat} (numerator : Word phaseBits) : List Nat :=
  ((RationalContinuedFraction.finiteContinuedFractionTrace
      numerator.val (2 ^ phaseBits)).fractions.map
        RationalContinuedFraction.ReducedRational.denominator)

/-- Every genuine continued-fraction denominator fits the phase-register
cardinality.  This is a bound on the unpadded finite path; the padded dyadic
trace is used only as an already-proved carrier of the same finite prefix. -/
lemma finiteCandidate_le_phaseCardinality {phaseBits : Nat}
    (numerator : Word phaseBits) {candidate : Nat}
    (member : candidate ∈ finiteCandidates numerator) :
    candidate ≤ 2 ^ phaseBits := by
  unfold finiteCandidates at member
  rcases List.mem_map.mp member with ⟨fraction, fractionMember, rfl⟩
  apply
    RationalContinuedFraction.dyadicContinuedFractionTrace_fraction_denominator_le
      numerator
  change fraction ∈
    (RationalContinuedFraction.finiteContinuedFractionTrace
      numerator.val (2 ^ phaseBits)).fractions ++ _
  exact List.mem_append_left _ fractionMember

/-- A static upper bound on the number of genuine convergents produced by a
`phaseBits`-bit dyadic measurement.  It is a capacity bound, not a schedule. -/
def finiteCandidateFuel (phaseBits : Nat) : Nat :=
  2 * (phaseBits + 1)

/-! ## Machine-compatible Euclidean/continuant cursor -/

/-- A natural numerator/denominator pair used by the executable continuant
recurrence.  This deliberately keeps the two predecessor pairs explicit: a
fixed-width implementation can materialize their denominator coordinates
without consulting a host-side candidate list. -/
structure EuclideanContinuantPair where
  /-- Numerator coordinate of the continuant pair. -/
  numerator : Nat
  /-- Denominator coordinate of the continuant pair. -/
  denominator : Nat

namespace EuclideanContinuantPair

/-- The rational value represented by one raw continuant pair. -/
def value (pair : EuclideanContinuantPair) : ℚ :=
  (pair.numerator : ℚ) / pair.denominator

/-- The two standard continuant basis pairs, indexed by `-2` and `-1`. -/
def initialOlder : EuclideanContinuantPair := ⟨0, 1⟩

/-- The standard continuant basis pair indexed by `-1`. -/
def initialPrevious : EuclideanContinuantPair := ⟨1, 0⟩

/-- One genuine continuant update from an actual Euclidean quotient. -/
def advance (quotient : Nat) (older previous : EuclideanContinuantPair) :
    EuclideanContinuantPair where
  numerator := quotient * previous.numerator + older.numerator
  denominator := quotient * previous.denominator + older.denominator

/-- Apply an already-computed continuant basis to a tail pair. -/
def transform (older previous tail : EuclideanContinuantPair) :
    EuclideanContinuantPair where
  numerator :=
    tail.numerator * previous.numerator + tail.denominator * older.numerator
  denominator :=
    tail.numerator * previous.denominator + tail.denominator * older.denominator

/-- Transport a tail convergent through one integer part.  The formula is the
same continuant recurrence as `advance`, specialized to the standard basis. -/
def lift (integerPart : Nat) (tail : EuclideanContinuantPair) :
    EuclideanContinuantPair :=
  transform initialPrevious
    (advance integerPart initialOlder initialPrevious) tail

/-- The explicit formula for lifting a positive reciprocal tail. -/
lemma lift_eq (integerPart : Nat) (tail : EuclideanContinuantPair) :
    lift integerPart tail =
      ⟨integerPart * tail.numerator + tail.denominator, tail.numerator⟩ := by
  cases tail
  simp [lift, transform, advance, initialOlder, initialPrevious, Nat.mul_comm]

/-- Lifting implements the rational reciprocal continued-fraction update. -/
lemma lift_value (integerPart : Nat) (tail : EuclideanContinuantPair)
    (hnumerator : 0 < tail.numerator)
    (hdenominator : 0 < tail.denominator) :
    (lift integerPart tail).value =
      (integerPart : ℚ) + tail.value⁻¹ := by
  have hnum : (tail.numerator : ℚ) ≠ 0 := by
    exact_mod_cast hnumerator.ne'
  have hden : (tail.denominator : ℚ) ≠ 0 := by
    exact_mod_cast hdenominator.ne'
  simp only [lift_eq, value, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- A positive reduced raw pair has its stored denominator as rational
denominator.  This is the local counterpart of
`RationalContinuedFraction.ReducedRational.value_den`. -/
lemma value_den (pair : EuclideanContinuantPair)
    (hdenominator : 0 < pair.denominator)
    (hreduced : Nat.Coprime pair.numerator pair.denominator) :
    pair.value.den = pair.denominator := by
  change
    (((pair.numerator : Int) : ℚ) /
      ((pair.denominator : Int) : ℚ)).den = pair.denominator
  have hpositive : (0 : Int) < (pair.denominator : Int) := by
    exact_mod_cast hdenominator
  have hcoprime :
      Nat.Coprime (pair.numerator : Int).natAbs
        (pair.denominator : Int).natAbs := by
    simpa using hreduced
  have hvalue := Rat.den_div_eq_of_coprime hpositive hcoprime
  exact_mod_cast hvalue

end EuclideanContinuantPair

open EuclideanContinuantPair

/-- The genuine quotient sequence of Euclid's algorithm.  It contains one
entry per actual division and terminates at the first zero remainder. -/
def euclideanQuotients (numerator denominator : Nat) : List Nat :=
  if _hdenominator : denominator = 0 then
    []
  else
    numerator / denominator ::
      euclideanQuotients denominator (numerator % denominator)
termination_by denominator
decreasing_by
  exact Nat.mod_lt numerator (Nat.pos_of_ne_zero _hdenominator)

@[simp] lemma euclideanQuotients_zero (numerator : Nat) :
    euclideanQuotients numerator 0 = [] := by
  rw [euclideanQuotients]
  simp

/-- One nonzero Euclidean divisor exposes exactly its quotient and recursive
remainder tail. -/
lemma euclideanQuotients_step (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0) :
    euclideanQuotients numerator denominator =
      numerator / denominator ::
        euclideanQuotients denominator (numerator % denominator) := by
  rw [euclideanQuotients]
  simp [hdenominator]

/-- Every quotient after a positive reciprocal tail is positive. -/
lemma euclideanQuotients_all_positive_of_le
    (numerator denominator : Nat) (hdenominator : 0 < denominator)
    (hle : denominator ≤ numerator) :
    ∀ quotient ∈ euclideanQuotients numerator denominator, 0 < quotient := by
  induction denominator using Nat.strong_induction_on generalizing numerator with
  | h denominator inductionHypothesis =>
      have hdenominatorNe : denominator ≠ 0 := hdenominator.ne'
      rw [euclideanQuotients_step numerator denominator hdenominatorNe]
      intro quotient hquotient
      simp only [List.mem_cons] at hquotient
      rcases hquotient with rfl | htail
      · exact Nat.div_pos hle hdenominator
      · by_cases hremainder : numerator % denominator = 0
        · rw [hremainder, euclideanQuotients_zero] at htail
          simp at htail
        · have hremainderPos : 0 < numerator % denominator :=
            Nat.pos_of_ne_zero hremainder
          have hremainderLt : numerator % denominator < denominator :=
            Nat.mod_lt numerator hdenominator
          exact
            inductionHypothesis (numerator % denominator) hremainderLt
              denominator hremainderPos (Nat.le_of_lt hremainderLt)
              quotient htail

/-- Run the continuant recurrence left-to-right over a finite quotient list.
This is the raw recurrence that a Components cursor materializes. -/
def forwardContinuantPairs :
    EuclideanContinuantPair → EuclideanContinuantPair →
      List Nat → List EuclideanContinuantPair
  | _older, _previous, [] => []
  | older, previous, quotient :: quotients =>
      let current := EuclideanContinuantPair.advance quotient older previous
      current :: forwardContinuantPairs previous current quotients

private lemma forwardContinuantPairs_transform
    (older previous : EuclideanContinuantPair) (quotients : List Nat) :
    forwardContinuantPairs older previous quotients =
      (forwardContinuantPairs initialOlder initialPrevious quotients).map
        (EuclideanContinuantPair.transform older previous) := by
  induction quotients generalizing older previous with
  | nil => rfl
  | cons quotient quotients inductionHypothesis =>
      let current := EuclideanContinuantPair.advance quotient older previous
      let initialCurrent :=
        EuclideanContinuantPair.advance quotient initialOlder initialPrevious
      have hhead :
          EuclideanContinuantPair.transform older previous initialCurrent =
            current := by
        cases older
        cases previous
        simp [EuclideanContinuantPair.transform,
          EuclideanContinuantPair.advance, initialOlder, initialPrevious,
          current, initialCurrent]
      have hcomposition (tail : EuclideanContinuantPair) :
          EuclideanContinuantPair.transform previous current tail =
            EuclideanContinuantPair.transform older previous
              (EuclideanContinuantPair.transform
                initialPrevious initialCurrent tail) := by
        cases older
        cases previous
        cases tail
        simp [EuclideanContinuantPair.transform,
          EuclideanContinuantPair.advance, initialOlder, initialPrevious,
          current, initialCurrent]
        constructor
        · ring
        · ring
      simp only [forwardContinuantPairs, List.map_cons]
      rw [hhead, inductionHypothesis previous current,
        inductionHypothesis initialPrevious initialCurrent]
      simp only [List.map_map]
      apply congrArg (List.cons current)
      apply List.map_congr_left
      intro tail _htail
      exact hcomposition tail

/-- The canonical backwards presentation of the same forward continuants.
Its recursion follows the public `convergents` recursion, while its values are
still the concrete left-to-right recurrence above. -/
def canonicalContinuantPairs : List Nat → List EuclideanContinuantPair
  | [] => []
  | quotient :: quotients =>
      EuclideanContinuantPair.advance quotient initialOlder initialPrevious ::
        (canonicalContinuantPairs quotients).map
          (EuclideanContinuantPair.lift quotient)

private lemma forwardContinuantPairs_initial_cons
    (quotient : Nat) (quotients : List Nat) :
    forwardContinuantPairs initialOlder initialPrevious
      (quotient :: quotients) =
        EuclideanContinuantPair.advance quotient initialOlder initialPrevious ::
          (forwardContinuantPairs initialOlder initialPrevious quotients).map
            (EuclideanContinuantPair.lift quotient) := by
  change
    EuclideanContinuantPair.advance quotient initialOlder initialPrevious ::
      forwardContinuantPairs initialPrevious
        (EuclideanContinuantPair.advance quotient initialOlder initialPrevious)
        quotients =
      EuclideanContinuantPair.advance quotient initialOlder initialPrevious ::
        (forwardContinuantPairs initialOlder initialPrevious quotients).map
          (EuclideanContinuantPair.lift quotient)
  rw [forwardContinuantPairs_transform initialPrevious
    (EuclideanContinuantPair.advance quotient initialOlder initialPrevious)
    quotients]
  rfl

/-- The forward raw recurrence and the canonical recursive presentation agree
for every finite quotient list. -/
lemma forwardContinuantPairs_initial_eq_canonical
    (quotients : List Nat) :
    forwardContinuantPairs initialOlder initialPrevious quotients =
      canonicalContinuantPairs quotients := by
  induction quotients with
  | nil => rfl
  | cons quotient quotients inductionHypothesis =>
      rw [forwardContinuantPairs_initial_cons, inductionHypothesis]
      rfl

/-- A positive quotient suffix makes every later continuant denominator at
least the previous denominator, and orders the emitted denominator list. -/
private lemma forwardContinuantPairs_denominators_bounded_pairwise
    (older previous : EuclideanContinuantPair) (quotients : List Nat)
    (holderPrevious : older.denominator ≤ previous.denominator)
    (hquotients : ∀ quotient ∈ quotients, 0 < quotient) :
    (∀ pair ∈ forwardContinuantPairs older previous quotients,
        previous.denominator ≤ pair.denominator) ∧
      ((forwardContinuantPairs older previous quotients).map
        EuclideanContinuantPair.denominator).Pairwise (· ≤ ·) := by
  induction quotients generalizing older previous with
  | nil => simp [forwardContinuantPairs]
  | cons quotient quotients inductionHypothesis =>
      let current := EuclideanContinuantPair.advance quotient older previous
      have hquotient : 0 < quotient := hquotients quotient (by simp)
      have htail : ∀ tailQuotient ∈ quotients, 0 < tailQuotient := by
        intro tailQuotient member
        exact hquotients tailQuotient (by simp [member])
      have hpreviousCurrent :
          previous.denominator ≤ current.denominator := by
        simp only [current, EuclideanContinuantPair.advance]
        calc
          previous.denominator = 1 * previous.denominator := by simp
          _ ≤ quotient * previous.denominator :=
            Nat.mul_le_mul_right previous.denominator hquotient
          _ ≤ quotient * previous.denominator + older.denominator :=
            Nat.le_add_right _ _
      have rest := inductionHypothesis previous current hpreviousCurrent htail
      constructor
      · intro pair member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact hpreviousCurrent
        · exact hpreviousCurrent.trans (rest.1 pair tailMember)
      · simp only [forwardContinuantPairs, List.map_cons, List.pairwise_cons]
        constructor
        · intro denominator member
          rcases List.mem_map.mp member with ⟨pair, pairMember, rfl⟩
          exact rest.1 pair pairMember
        · exact rest.2

/-- Every canonical continuant pair is reduced. -/
lemma canonicalContinuantPairs_reduced (quotients : List Nat) :
    ∀ pair ∈ canonicalContinuantPairs quotients,
      Nat.Coprime pair.numerator pair.denominator := by
  induction quotients with
  | nil => simp [canonicalContinuantPairs]
  | cons quotient quotients inductionHypothesis =>
      simp only [canonicalContinuantPairs, List.mem_cons, List.mem_map]
      intro pair hpair
      rcases hpair with rfl | ⟨tail, htail, rfl⟩
      · simp [EuclideanContinuantPair.advance, initialOlder, initialPrevious]
      · simpa [EuclideanContinuantPair.lift_eq] using
          (Nat.coprime_mul_right_add_left
            tail.denominator tail.numerator quotient).2
            (inductionHypothesis tail htail).symm

/-- Positive quotient lists produce positive numerator and denominator
coordinates at every canonical continuant. -/
lemma canonicalContinuantPairs_positive_of_all_positive
    (quotients : List Nat)
    (hquotients : ∀ quotient ∈ quotients, 0 < quotient) :
    ∀ pair ∈ canonicalContinuantPairs quotients,
      0 < pair.numerator ∧ 0 < pair.denominator := by
  induction quotients with
  | nil => simp [canonicalContinuantPairs]
  | cons quotient quotients inductionHypothesis =>
      have hquotient : 0 < quotient := hquotients quotient (by simp)
      have htailQuotients :
          ∀ tailQuotient ∈ quotients, 0 < tailQuotient := by
        intro tailQuotient htailQuotient
        exact hquotients tailQuotient (by simp [htailQuotient])
      have htail := inductionHypothesis htailQuotients
      simp only [canonicalContinuantPairs, List.mem_cons, List.mem_map]
      intro pair hpair
      rcases hpair with rfl | ⟨tail, htailPair, rfl⟩
      · constructor <;>
          simp [EuclideanContinuantPair.advance, initialOlder,
            initialPrevious, hquotient]
      · rcases htail tail htailPair with ⟨htailNumerator, htailDenominator⟩
        rw [EuclideanContinuantPair.lift_eq]
        exact ⟨Nat.add_pos_right _ htailDenominator, htailNumerator⟩

/-- The canonical pairs evaluate to the public finite list of rational
convergents. -/
lemma canonicalContinuantPairs_values_eq_convergents
    (numerator denominator : Nat) (hdenominator : 0 < denominator) :
    (canonicalContinuantPairs
      (euclideanQuotients numerator denominator)).map
        EuclideanContinuantPair.value =
      RationalContinuedFraction.convergents numerator denominator := by
  induction denominator using Nat.strong_induction_on generalizing numerator with
  | h denominator inductionHypothesis =>
      have hdenominatorNe : denominator ≠ 0 := hdenominator.ne'
      let quotient := numerator / denominator
      let remainder := numerator % denominator
      by_cases hremainder : remainder = 0
      · have htrace :=
          RationalContinuedFraction.convergents_eq_singleton_of_mod_eq_zero
            hdenominatorNe (by simpa [remainder] using hremainder)
        rw [euclideanQuotients_step numerator denominator hdenominatorNe]
        rw [show euclideanQuotients denominator remainder = [] by
          rw [hremainder]
          exact euclideanQuotients_zero denominator]
        simp [canonicalContinuantPairs,
          EuclideanContinuantPair.advance, EuclideanContinuantPair.value,
          initialOlder, initialPrevious, htrace]
      · have hremainderPos : 0 < remainder :=
          Nat.pos_of_ne_zero hremainder
        have hremainderLt : remainder < denominator := by
          simpa [remainder] using Nat.mod_lt numerator hdenominator
        have htailValues :
            (canonicalContinuantPairs
              (euclideanQuotients denominator remainder)).map
                EuclideanContinuantPair.value =
              RationalContinuedFraction.convergents denominator remainder := by
          exact inductionHypothesis remainder hremainderLt denominator
            hremainderPos
        have htailQuotients :
            ∀ tailQuotient ∈ euclideanQuotients denominator remainder,
              0 < tailQuotient := by
          apply euclideanQuotients_all_positive_of_le
          · exact hremainderPos
          · exact Nat.le_of_lt hremainderLt
        have htailPositive :=
          canonicalContinuantPairs_positive_of_all_positive
            (euclideanQuotients denominator remainder) htailQuotients
        have hliftValues :
            (canonicalContinuantPairs
              (euclideanQuotients denominator remainder)).map
                (fun tail =>
                  (EuclideanContinuantPair.lift quotient tail).value) =
              ((canonicalContinuantPairs
                (euclideanQuotients denominator remainder)).map
                  EuclideanContinuantPair.value).map
                    (fun tail => (quotient : ℚ) + tail⁻¹) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro tail htail
          rcases htailPositive tail htail with
            ⟨htailNumerator, htailDenominator⟩
          simpa [Function.comp_apply] using
            EuclideanContinuantPair.lift_value quotient tail
              htailNumerator htailDenominator
        have htrace :=
          RationalContinuedFraction.convergents_eq_cons_of_mod_ne_zero
            hdenominatorNe (by simpa [remainder] using hremainder)
        rw [euclideanQuotients_step numerator denominator hdenominatorNe]
        simp only [canonicalContinuantPairs, List.map_cons, List.map_map]
        change
          (EuclideanContinuantPair.advance quotient initialOlder
              initialPrevious).value ::
              (canonicalContinuantPairs
                (euclideanQuotients denominator remainder)).map
                  (fun tail =>
                    (EuclideanContinuantPair.lift quotient tail).value) =
            RationalContinuedFraction.convergents numerator denominator
        rw [hliftValues]
        have htailValuesMapped :
            ((canonicalContinuantPairs
              (euclideanQuotients denominator (numerator % denominator))).map
                EuclideanContinuantPair.value).map
                  (fun tail => (quotient : ℚ) + tail⁻¹) =
              (RationalContinuedFraction.convergents denominator
                (numerator % denominator)).map
                  (fun tail => (quotient : ℚ) + tail⁻¹) := by
          simpa only [remainder] using
            congrArg (List.map (fun tail : ℚ => (quotient : ℚ) + tail⁻¹))
              htailValues
        change
          (EuclideanContinuantPair.advance quotient initialOlder
              initialPrevious).value ::
              ((canonicalContinuantPairs
                (euclideanQuotients denominator (numerator % denominator))).map
                  EuclideanContinuantPair.value).map
                    (fun tail => (quotient : ℚ) + tail⁻¹) =
            RationalContinuedFraction.convergents numerator denominator
        rw [htailValuesMapped, htrace]
        simp [quotient, EuclideanContinuantPair.advance,
          EuclideanContinuantPair.value, initialOlder, initialPrevious]

/-- All raw denominator coordinates in the Euclidean quotient execution are
positive, including the initial integer convergent. -/
lemma canonicalContinuantPairs_denominator_pos
    (numerator denominator : Nat) (hdenominator : 0 < denominator) :
    ∀ pair ∈ canonicalContinuantPairs
        (euclideanQuotients numerator denominator),
      0 < pair.denominator := by
  have hdenominatorNe : denominator ≠ 0 := hdenominator.ne'
  let remainder := numerator % denominator
  by_cases hremainder : remainder = 0
  · rw [euclideanQuotients_step numerator denominator hdenominatorNe]
    rw [show euclideanQuotients denominator remainder = [] by
      rw [hremainder]
      exact euclideanQuotients_zero denominator]
    simp [canonicalContinuantPairs, EuclideanContinuantPair.advance,
      initialOlder, initialPrevious]
  · have hremainderPos : 0 < remainder := Nat.pos_of_ne_zero hremainder
    have hremainderLt : remainder < denominator := by
      simpa [remainder] using Nat.mod_lt numerator hdenominator
    have htailQuotients :
        ∀ tailQuotient ∈ euclideanQuotients denominator remainder,
          0 < tailQuotient := by
      apply euclideanQuotients_all_positive_of_le
      · exact hremainderPos
      · exact Nat.le_of_lt hremainderLt
    have htailPositive :=
      canonicalContinuantPairs_positive_of_all_positive
        (euclideanQuotients denominator remainder) htailQuotients
    rw [euclideanQuotients_step numerator denominator hdenominatorNe]
    simp only [canonicalContinuantPairs, List.mem_cons, List.mem_map]
    intro pair hpair
    rcases hpair with rfl | ⟨tail, htail, rfl⟩
    · simp [EuclideanContinuantPair.advance, initialOlder, initialPrevious]
    · simpa [EuclideanContinuantPair.lift_eq] using
        (htailPositive tail htail).1

/-- The raw continuant denominators are exactly the denominators of the
public rational convergent sequence. -/
lemma canonicalContinuantPairs_denominators_eq_convergents_denominators
    (numerator denominator : Nat) (hdenominator : 0 < denominator) :
    (canonicalContinuantPairs
      (euclideanQuotients numerator denominator)).map
        EuclideanContinuantPair.denominator =
      (RationalContinuedFraction.convergents numerator denominator).map
        (fun value : ℚ => value.den) := by
  let pairs := canonicalContinuantPairs
    (euclideanQuotients numerator denominator)
  have hpositive :=
    canonicalContinuantPairs_denominator_pos numerator denominator hdenominator
  have hreduced := canonicalContinuantPairs_reduced
    (euclideanQuotients numerator denominator)
  calc
    pairs.map EuclideanContinuantPair.denominator =
        (pairs.map EuclideanContinuantPair.value).map
          (fun value : ℚ => value.den) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro pair hpair
      exact
        (EuclideanContinuantPair.value_den pair
          (hpositive pair hpair) (hreduced pair hpair)).symm
    _ = (RationalContinuedFraction.convergents numerator denominator).map
          (fun value : ℚ => value.den) := by
      rw [canonicalContinuantPairs_values_eq_convergents
        numerator denominator hdenominator]

/-- Machine-compatible state for a forward Euclidean/continuant cursor.  The
`older` and `previous` fields are full convergent pairs, while the Components
realization needs only their denominator coordinates. -/
structure EuclideanContinuantCursor where
  /-- Current Euclidean dividend. -/
  numerator : Nat
  /-- Current Euclidean divisor. -/
  denominator : Nat
  /-- Continuant pair preceding `previous`. -/
  older : EuclideanContinuantPair
  /-- Most recently materialized continuant pair. -/
  previous : EuclideanContinuantPair

namespace EuclideanContinuantCursor

/-- A cursor is active exactly when its next divisor is nonzero. -/
def active (cursor : EuclideanContinuantCursor) : Bool :=
  decide (cursor.denominator ≠ 0)

lemma active_eq_true_iff (cursor : EuclideanContinuantCursor) :
    cursor.active = true ↔ cursor.denominator ≠ 0 := by
  simp [active]

/-- The actual Euclidean quotient read by one active cursor visit. -/
def quotient (cursor : EuclideanContinuantCursor) : Nat :=
  cursor.numerator / cursor.denominator

/-- The actual Euclidean remainder read by one active cursor visit. -/
def remainder (cursor : EuclideanContinuantCursor) : Nat :=
  cursor.numerator % cursor.denominator

/-- The convergent materialized by one active cursor visit. -/
def candidate (cursor : EuclideanContinuantCursor) :
    EuclideanContinuantPair :=
  EuclideanContinuantPair.advance cursor.quotient cursor.older cursor.previous

/-- Advance the Euclidean operands and both continuant predecessors after one
real quotient/remainder step. -/
def advance (cursor : EuclideanContinuantCursor) : EuclideanContinuantCursor where
  numerator := cursor.denominator
  denominator := cursor.remainder
  older := cursor.previous
  previous := cursor.candidate

/-- Advance through at most `fuel` genuine cursor visits.  Once the Euclidean
cursor is finished, further fixed-fuel slots retain that finished state rather
than applying a synthetic division by zero. -/
def advanceN : Nat → EuclideanContinuantCursor → EuclideanContinuantCursor
  | 0, cursor => cursor
  | Nat.succ fuel, cursor =>
      if cursor.denominator = 0 then cursor else advanceN fuel cursor.advance

/-- The raw observable data of one cursor visit. -/
structure Visit where
  /-- Dividend consumed by this Euclidean visit. -/
  dividend : Nat
  /-- Nonzero divisor consumed by an active visit. -/
  divisor : Nat
  /-- Quotient produced by the visit. -/
  quotient : Nat
  /-- Remainder produced by the visit. -/
  remainder : Nat
  /-- Denominator coordinate of the older continuant. -/
  olderDenominator : Nat
  /-- Denominator coordinate of the previous continuant. -/
  previousDenominator : Nat
  /-- Denominator coordinate materialized by this visit. -/
  candidate : Nat

/-- Read one raw Euclidean/continuant visit from the same cursor state. -/
def visit (cursor : EuclideanContinuantCursor) : Visit where
  dividend := cursor.numerator
  divisor := cursor.denominator
  quotient := cursor.quotient
  remainder := cursor.remainder
  olderDenominator := cursor.older.denominator
  previousDenominator := cursor.previous.denominator
  candidate := cursor.candidate.denominator

/-- The visit contains the literal division, remainder, and continuant
recurrence used by the machine. -/
lemma visit_real_of_active (cursor : EuclideanContinuantCursor)
    (hactive : cursor.denominator ≠ 0) :
    cursor.visit.divisor ≠ 0 ∧
      cursor.visit.quotient = cursor.visit.dividend / cursor.visit.divisor ∧
        cursor.visit.remainder = cursor.visit.dividend % cursor.visit.divisor ∧
          cursor.visit.candidate =
            cursor.visit.quotient * cursor.visit.previousDenominator +
              cursor.visit.olderDenominator := by
  exact ⟨hactive, rfl, rfl, rfl⟩

/-- Consume one genuine visit, or return `none` at the first finished
Euclidean state. -/
def step (cursor : EuclideanContinuantCursor) :
    Option (Nat × EuclideanContinuantCursor) :=
  if cursor.denominator = 0 then
    none
  else
    some (cursor.candidate.denominator, cursor.advance)

lemma step_eq_some_of_active (cursor : EuclideanContinuantCursor)
    (hactive : cursor.denominator ≠ 0) :
    cursor.step = some (cursor.candidate.denominator, cursor.advance) := by
  simp [step, hactive]

lemma step_eq_none_of_inactive (cursor : EuclideanContinuantCursor)
    (hinactive : cursor.denominator = 0) :
    cursor.step = none := by
  simp [step, hinactive]

/-- The unpadded candidates generated by the raw cursor.  The only list fed
to the continuant recurrence is the actual quotient/remainder sequence. -/
def actualCandidates (cursor : EuclideanContinuantCursor) : List Nat :=
  (forwardContinuantPairs cursor.older cursor.previous
    (euclideanQuotients cursor.numerator cursor.denominator)).map
      EuclideanContinuantPair.denominator

/-- A real active visit is the head of the remaining raw path, and its tail
is exactly the advanced cursor path. -/
lemma actualCandidates_cons_of_active (cursor : EuclideanContinuantCursor)
    (hactive : cursor.denominator ≠ 0) :
    cursor.actualCandidates =
      cursor.candidate.denominator :: cursor.advance.actualCandidates := by
  rw [actualCandidates, euclideanQuotients_step
    cursor.numerator cursor.denominator hactive]
  rfl

/-- A finished cursor has no fabricated candidate. -/
lemma actualCandidates_eq_nil_of_inactive
    (cursor : EuclideanContinuantCursor)
    (hinactive : cursor.denominator = 0) :
    cursor.actualCandidates = [] := by
  rw [actualCandidates, hinactive, euclideanQuotients_zero]
  rfl

/-- The actual cursor path is empty only at a finished Euclidean divisor. -/
lemma actualCandidates_eq_nil_iff_denominator_eq_zero
    (cursor : EuclideanContinuantCursor) :
    cursor.actualCandidates = [] ↔ cursor.denominator = 0 := by
  constructor
  · intro hactual
    by_contra hactive
    have hcons := actualCandidates_cons_of_active cursor hactive
    rw [hactual] at hcons
    simp at hcons
  · exact actualCandidates_eq_nil_of_inactive cursor

/-- The remaining actual cursor path after fixed fuel is precisely the
unconsumed suffix of the original path. -/
lemma actualCandidates_advanceN (fuel : Nat)
    (cursor : EuclideanContinuantCursor) :
    (cursor.advanceN fuel).actualCandidates = cursor.actualCandidates.drop fuel := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      by_cases hinactive : cursor.denominator = 0
      · rw [advanceN, if_pos hinactive]
        rw [actualCandidates_eq_nil_of_inactive cursor hinactive]
        rfl
      · rw [advanceN, if_neg hinactive]
        rw [inductionHypothesis cursor.advance]
        rw [actualCandidates_cons_of_active cursor hinactive]
        rfl

/-- A fuel bound covering the original actual path leaves no remaining
candidate after the corresponding guarded cursor advancement. -/
lemma advanceN_actualCandidates_eq_nil_of_length_le
    (fuel : Nat) (cursor : EuclideanContinuantCursor)
    (hbound : cursor.actualCandidates.length ≤ fuel) :
    (cursor.advanceN fuel).actualCandidates = [] := by
  rw [actualCandidates_advanceN]
  exact List.drop_eq_nil_of_le hbound

/-- A fuel bound covering the original actual path reaches a finished
Euclidean divisor. -/
lemma advanceN_denominator_eq_zero_of_length_le
    (fuel : Nat) (cursor : EuclideanContinuantCursor)
    (hbound : cursor.actualCandidates.length ≤ fuel) :
    (cursor.advanceN fuel).denominator = 0 := by
  apply (actualCandidates_eq_nil_iff_denominator_eq_zero
    (cursor.advanceN fuel)).mp
  exact advanceN_actualCandidates_eq_nil_of_length_le fuel cursor hbound

/-- A fuel bound covering the original actual path leaves the raw active bit
false. -/
lemma advanceN_active_eq_false_of_length_le
    (fuel : Nat) (cursor : EuclideanContinuantCursor)
    (hbound : cursor.actualCandidates.length ≤ fuel) :
    (cursor.advanceN fuel).active = false := by
  have hinactive := advanceN_denominator_eq_zero_of_length_le fuel cursor hbound
  simp [active, hinactive]

/-- The initial cursor for one exact rational numerator/denominator pair. -/
def initial (numerator denominator : Nat) : EuclideanContinuantCursor where
  numerator := numerator
  denominator := denominator
  older := initialOlder
  previous := initialPrevious

/-- The initial raw candidate path is the canonical continuant path. -/
lemma initial_actualCandidates_eq_canonical
    (numerator denominator : Nat) :
    (initial numerator denominator).actualCandidates =
      (canonicalContinuantPairs
        (euclideanQuotients numerator denominator)).map
          EuclideanContinuantPair.denominator := by
  rw [actualCandidates, initial, forwardContinuantPairs_initial_eq_canonical]

/-- A fixed-fuel controller observes a prefix of genuine visits only.  It
does not append a repeated candidate after the raw cursor terminates. -/
def fixedFuelCandidates (fuel : Nat) (cursor : EuclideanContinuantCursor) :
    List Nat :=
  cursor.actualCandidates.take fuel

lemma fixedFuelCandidates_eq_actualCandidates_of_length_le
    (fuel : Nat) (cursor : EuclideanContinuantCursor)
    (hbound : cursor.actualCandidates.length ≤ fuel) :
    cursor.fixedFuelCandidates fuel = cursor.actualCandidates := by
  exact (List.take_eq_self_iff cursor.actualCandidates).mpr hbound

end EuclideanContinuantCursor

/-- The public finite trace's denominator projection is equivalently the
denominator projection of the public rational convergents. -/
lemma finiteCandidates_eq_convergents_denominators
    {phaseBits : Nat} (numerator : Word phaseBits) :
    finiteCandidates numerator =
      (RationalContinuedFraction.convergents numerator.val
        (2 ^ phaseBits)).map (fun value : ℚ => value.den) := by
  calc
    finiteCandidates numerator =
        (RationalContinuedFraction.finiteContinuedFractionTrace
          numerator.val (2 ^ phaseBits)).fractions.map
            RationalContinuedFraction.ReducedRational.denominator :=
      rfl
    _ =
        ((RationalContinuedFraction.finiteContinuedFractionTrace
          numerator.val (2 ^ phaseBits)).fractions.map
            RationalContinuedFraction.ReducedRational.value).map
              (fun value : ℚ => value.den) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro fraction _hfraction
      exact (RationalContinuedFraction.ReducedRational.value_den fraction).symm
    _ = (RationalContinuedFraction.convergents numerator.val
          (2 ^ phaseBits)).map (fun value : ℚ => value.den) := by
      rw [RationalContinuedFraction.finiteContinuedFractionTrace_values]

/-- The initial machine-compatible cursor enumerates exactly the unpadded
finite-trace denominator schedule.  Thus every active quotient/remainder and
continuant recurrence reaches the next genuine trace candidate, with no
padding witness or host-side list substitution. -/
lemma initialEuclideanContinuantCandidates_eq_finiteCandidates
    {phaseBits : Nat} (numerator : Word phaseBits) :
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).actualCandidates =
      finiteCandidates numerator := by
  calc
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).actualCandidates =
        (canonicalContinuantPairs
          (euclideanQuotients numerator.val (2 ^ phaseBits))).map
            EuclideanContinuantPair.denominator :=
      EuclideanContinuantCursor.initial_actualCandidates_eq_canonical
        numerator.val (2 ^ phaseBits)
    _ = (RationalContinuedFraction.convergents numerator.val
          (2 ^ phaseBits)).map (fun value : ℚ => value.den) :=
      canonicalContinuantPairs_denominators_eq_convergents_denominators
        numerator.val (2 ^ phaseBits) (by positivity)
    _ = finiteCandidates numerator :=
      (finiteCandidates_eq_convergents_denominators numerator).symm

/-- Genuine finite continued-fraction denominators are nondecreasing in their
actual execution order.  Equality is allowed because distinct convergents can
share a denominator; no synthetic padding is involved. -/
lemma finiteCandidates_pairwise_le {phaseBits : Nat}
    (numerator : Word phaseBits) :
    (finiteCandidates numerator).Pairwise (· ≤ ·) := by
  rw [← initialEuclideanContinuantCandidates_eq_finiteCandidates numerator,
    EuclideanContinuantCursor.initial_actualCandidates_eq_canonical,
    ← forwardContinuantPairs_initial_eq_canonical]
  have denominatorPositive : 0 < 2 ^ phaseBits := by positivity
  rw [euclideanQuotients_step numerator.val (2 ^ phaseBits)
    denominatorPositive.ne']
  let current := EuclideanContinuantPair.advance
    (numerator.val / 2 ^ phaseBits) initialOlder initialPrevious
  have tailPositive :
      ∀ quotient ∈ euclideanQuotients (2 ^ phaseBits)
          (numerator.val % 2 ^ phaseBits),
        0 < quotient := by
    by_cases remainderZero : numerator.val % 2 ^ phaseBits = 0
    · simp [remainderZero]
    · apply euclideanQuotients_all_positive_of_le
      · exact Nat.pos_of_ne_zero remainderZero
      · exact Nat.le_of_lt (Nat.mod_lt numerator.val denominatorPositive)
  have rest := forwardContinuantPairs_denominators_bounded_pairwise
    initialPrevious current
    (euclideanQuotients (2 ^ phaseBits) (numerator.val % 2 ^ phaseBits))
    (by simp [current, EuclideanContinuantPair.advance, initialOlder,
      initialPrevious])
    tailPositive
  simp only [forwardContinuantPairs, List.map_cons, List.pairwise_cons]
  constructor
  · intro denominator member
    rcases List.mem_map.mp member with ⟨pair, pairMember, rfl⟩
    simpa [current, EuclideanContinuantPair.advance, initialOlder,
      initialPrevious] using rest.1 pair pairMember
  · exact rest.2

/-- A component-facing cursor over the remaining genuine continued-fraction
denominators.  Its list contains only actual convergents and is never extended
to its fuel bound. -/
structure ContinuedFractionState (_phaseBits : Nat) where
  /-- Denominators still available for validation, in finite-trace order. -/
  remaining : List Nat

/-- Initialize the cursor from the exact finite continued-fraction schedule. -/
def initialContinuedFractionState {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    ContinuedFractionState phaseBits where
  remaining := finiteCandidates (decodedIndex input)

/-- Whether an actual candidate remains available for one continued-fraction
validation step. -/
def cfActive {phaseBits : Nat} (state : ContinuedFractionState phaseBits) : Bool :=
  match state.remaining with
  | [] => false
  | _ :: _ => true

/-- Consume one actual continued-fraction denominator, or stop at the end of
the finite trace. -/
def cfStep {phaseBits : Nat} (state : ContinuedFractionState phaseBits) :
    Option (Nat × ContinuedFractionState phaseBits) :=
  match state.remaining with
  | [] => none
  | candidate :: remaining => some (candidate, { remaining := remaining })

/-- The ordered candidates that an active continued-fraction cursor can still
visit. -/
def cfPath {phaseBits : Nat} (state : ContinuedFractionState phaseBits) : List Nat :=
  state.remaining

namespace EuclideanContinuantCursor

/-- Project the remaining genuine raw visits into the existing pure recovery
cursor.  This is a representation bridge, not a second scan or a padded
schedule. -/
def asContinuedFractionState {phaseBits : Nat}
    (cursor : EuclideanContinuantCursor) :
    ContinuedFractionState phaseBits where
  remaining := cursor.actualCandidates

@[simp] lemma cfPath_asContinuedFractionState {phaseBits : Nat}
    (cursor : EuclideanContinuantCursor) :
    cfPath (cursor.asContinuedFractionState (phaseBits := phaseBits)) =
      cursor.actualCandidates :=
  rfl

/-- The pure cursor-active bit is exactly the raw nonzero-divisor bit. -/
lemma cfActive_asContinuedFractionState {phaseBits : Nat}
    (cursor : EuclideanContinuantCursor) :
    cfActive (cursor.asContinuedFractionState (phaseBits := phaseBits)) =
      cursor.active := by
  by_cases hactive : cursor.denominator = 0
  · rw [asContinuedFractionState,
      actualCandidates_eq_nil_of_inactive cursor hactive]
    simp [cfActive, active, hactive]
  · rw [asContinuedFractionState,
      actualCandidates_cons_of_active cursor hactive]
    simp [cfActive, active, hactive]

/-- One active raw visit is exactly the next `cfStep` candidate and suffix. -/
lemma cfStep_asContinuedFractionState_of_active {phaseBits : Nat}
    (cursor : EuclideanContinuantCursor)
    (hactive : cursor.denominator ≠ 0) :
    cfStep (cursor.asContinuedFractionState (phaseBits := phaseBits)) =
      some (cursor.candidate.denominator,
        cursor.advance.asContinuedFractionState (phaseBits := phaseBits)) := by
  rw [asContinuedFractionState,
    actualCandidates_cons_of_active cursor hactive]
  rfl

/-- A finished raw cursor has the same `none` step as the pure recovery
cursor and therefore contributes no later candidate. -/
lemma cfStep_asContinuedFractionState_of_inactive {phaseBits : Nat}
    (cursor : EuclideanContinuantCursor)
    (hinactive : cursor.denominator = 0) :
    cfStep (cursor.asContinuedFractionState (phaseBits := phaseBits)) = none := by
  rw [asContinuedFractionState,
    actualCandidates_eq_nil_of_inactive cursor hinactive]
  rfl

/-- The raw dyadic initialization represents exactly the old canonical
unpadding cursor used by recovery selection. -/
lemma initial_asContinuedFractionState_eq_initialContinuedFractionState
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) :
    (initial (decodedIndex input).val (2 ^ phaseBits)).asContinuedFractionState
      (phaseBits := phaseBits) = initialContinuedFractionState spec input := by
  unfold asContinuedFractionState initialContinuedFractionState
  apply congrArg (fun remaining : List Nat =>
    ({ remaining := remaining } : ContinuedFractionState phaseBits))
  exact initialEuclideanContinuantCandidates_eq_finiteCandidates
    (decodedIndex input)

end EuclideanContinuantCursor

@[simp] lemma cfPath_initialContinuedFractionState
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) :
    cfPath (initialContinuedFractionState spec input) =
      finiteCandidates (decodedIndex input) :=
  rfl

/-- Every active cursor step exposes the first real candidate in its remaining
path and advances to exactly the remaining suffix. -/
lemma cfActive_visit {phaseBits : Nat} (state : ContinuedFractionState phaseBits)
    (hactive : cfActive state = true) :
    ∃ candidate remaining,
      cfPath state = candidate :: remaining ∧
        cfStep state = some (candidate, { remaining := remaining }) := by
  cases state with
  | mk queued =>
      cases queued with
      | nil => simp [cfActive] at hactive
      | cons candidate remaining =>
          exact ⟨candidate, remaining, rfl, rfl⟩

/-- The exact finite candidate list is bounded by the static cursor capacity. -/
lemma finiteCandidates_length_le_finiteCandidateFuel
    {phaseBits : Nat} (numerator : Word phaseBits) :
    (finiteCandidates numerator).length ≤ finiteCandidateFuel phaseBits := by
  calc
    (finiteCandidates numerator).length =
        (RationalContinuedFraction.finiteContinuedFractionTrace
          numerator.val (2 ^ phaseBits)).fractions.length := by
      simp [finiteCandidates]
    _ =
        ((RationalContinuedFraction.finiteContinuedFractionTrace
          numerator.val (2 ^ phaseBits)).fractions.map
          RationalContinuedFraction.ReducedRational.value).length := by
      simp
    _ = (RationalContinuedFraction.convergents numerator.val (2 ^ phaseBits)).length := by
      rw [RationalContinuedFraction.finiteContinuedFractionTrace_values]
    _ ≤ finiteCandidateFuel phaseBits := by
      simpa [finiteCandidateFuel, Nat.size_pow, Nat.mul_add] using
        (RationalContinuedFraction.convergents_length_le numerator.val
          (2 ^ phaseBits) (by positivity))

/-- The raw initial cursor has at most the same fixed fuel as the canonical
unpadding schedule. -/
lemma initialEuclideanContinuantCandidates_length_le_finiteCandidateFuel
    {phaseBits : Nat} (numerator : Word phaseBits) :
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).actualCandidates.length ≤
      finiteCandidateFuel phaseBits := by
  rw [initialEuclideanContinuantCandidates_eq_finiteCandidates]
  exact finiteCandidates_length_le_finiteCandidateFuel numerator

/-- The prescribed finite fuel consumes every genuine raw candidate of the
initial dyadic Euclidean cursor. -/
lemma initialEuclideanContinuantAdvanceN_actualCandidates_eq_nil
    {phaseBits : Nat} (numerator : Word phaseBits) :
    ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      (finiteCandidateFuel phaseBits)).actualCandidates = [] := by
  exact EuclideanContinuantCursor.advanceN_actualCandidates_eq_nil_of_length_le
    (finiteCandidateFuel phaseBits)
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits))
    (initialEuclideanContinuantCandidates_length_le_finiteCandidateFuel numerator)

/-- The prescribed finite fuel leaves the initialized raw cursor inactive. -/
lemma initialEuclideanContinuantAdvanceN_active_eq_false
    {phaseBits : Nat} (numerator : Word phaseBits) :
    ((EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).advanceN
      (finiteCandidateFuel phaseBits)).active = false := by
  exact EuclideanContinuantCursor.advanceN_active_eq_false_of_length_le
    (finiteCandidateFuel phaseBits)
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits))
    (initialEuclideanContinuantCandidates_length_le_finiteCandidateFuel numerator)

/-- At the public fixed fuel, the raw cursor exposes every genuine candidate
and no extra slot. -/
lemma initialFixedFuelCandidates_eq_finiteCandidates
    {phaseBits : Nat} (numerator : Word phaseBits) :
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).fixedFuelCandidates
        (finiteCandidateFuel phaseBits) =
        finiteCandidates numerator := by
  calc
    (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).fixedFuelCandidates
          (finiteCandidateFuel phaseBits) =
        (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits)).actualCandidates :=
      EuclideanContinuantCursor.fixedFuelCandidates_eq_actualCandidates_of_length_le
          (finiteCandidateFuel phaseBits)
          (EuclideanContinuantCursor.initial numerator.val (2 ^ phaseBits))
          (initialEuclideanContinuantCandidates_length_le_finiteCandidateFuel
            numerator)
    _ = finiteCandidates numerator :=
      initialEuclideanContinuantCandidates_eq_finiteCandidates numerator

/-- The initialized cursor has no more active visits than its static capacity. -/
lemma cfPath_initial_length_le_finiteCandidateFuel
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) :
    (cfPath (initialContinuedFractionState spec input)).length ≤
      finiteCandidateFuel phaseBits := by
  rw [cfPath_initialContinuedFractionState]
  exact finiteCandidates_length_le_finiteCandidateFuel (decodedIndex input)

/-- A candidate passes the complete mathematical validation performed by this
pure recovery layer. -/
def CandidateAccepted {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (candidate : Nat) : Prop :=
  candidate < 2 ^ (phaseBits + 1) ∧
    0 < candidate ∧
      input.base.val ^ candidate ≡ 1 [MOD spec.modulusSpec.modulus]

/-- The ordinary mathematical least-positive-exponent condition for the unit
base.  It is deliberately separate from candidate validation: an early scan
tests modular return, not global leastness. -/
def MinimalUnitOrder {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (order : Nat) : Prop :=
  0 < order ∧
    input.base.val ^ order ≡ 1 [MOD spec.modulusSpec.modulus] ∧
      ∀ smaller : Nat, 0 < smaller → smaller < order →
        ¬ (input.base.val ^ smaller ≡ 1 [MOD spec.modulusSpec.modulus])

/-- The executable Boolean observation of one complete candidate validation. -/
def validateCandidate {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (candidate : Nat) : Bool :=
  decide
    (candidate < 2 ^ (phaseBits + 1) ∧
      0 < candidate ∧
        input.base.val ^ candidate ≡ 1 [MOD spec.modulusSpec.modulus])

lemma validateCandidate_eq_true_iff {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (candidate : Nat) :
    validateCandidate spec input candidate = true ↔
      CandidateAccepted spec input candidate := by
  simp [validateCandidate, CandidateAccepted]

lemma validateCandidate_eq_false_iff {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (candidate : Nat) :
    validateCandidate spec input candidate = false ↔
      ¬ CandidateAccepted spec input candidate := by
  simp [validateCandidate, CandidateAccepted]

/-- A nonaccepting Boolean validation has the canonical `false` result. -/
private lemma validateCandidate_eq_false_of_ne_true
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidate : Nat)
    (hnot : validateCandidate spec input candidate ≠ true) :
    validateCandidate spec input candidate = false := by
  apply (validateCandidate_eq_false_iff spec input candidate).mpr
  intro haccepted
  exact hnot ((validateCandidate_eq_true_iff spec input candidate).mpr haccepted)

/-- One actually validated continued-fraction candidate. A `false` result is
an explicit rejection, rather than skipped padding. -/
structure CandidateValidation where
  /-- The denominator tested at this position of the actual path. -/
  candidate : Nat
  /-- The complete validation result for that denominator. -/
  accepted : Bool

/-- Materialize the deterministic validation result for one candidate. -/
def CandidateValidation.ofCandidate {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (candidate : Nat) : CandidateValidation where
  candidate := candidate
  accepted := validateCandidate spec input candidate

@[simp] lemma CandidateValidation.ofCandidate_candidate
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidate : Nat) :
    (CandidateValidation.ofCandidate spec input candidate).candidate = candidate :=
  rfl

@[simp] lemma CandidateValidation.ofCandidate_accepted
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidate : Nat) :
    (CandidateValidation.ofCandidate spec input candidate).accepted =
      validateCandidate spec input candidate :=
  rfl

/-- The path and selected candidate produced by one initial scan. -/
structure ScanResult where
  private mk ::
  /-- Every candidate actually validated before termination. -/
  path : List CandidateValidation
  /-- The first accepted candidate, if the full finite schedule has one. -/
  selection : Option Nat

/-- Scan candidates in finite continued-fraction order. Each rejection
continues to the next candidate; a successful validation terminates immediately. -/
private def scanCandidates {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    List Nat → ScanResult
  | [] => .mk [] none
  | candidate :: candidates =>
      let record := CandidateValidation.ofCandidate spec input candidate
      if validateCandidate spec input candidate = true then
        .mk [record] (some candidate)
      else
        let tail := scanCandidates spec input candidates
        .mk (record :: tail.path) tail.selection

private lemma scanCandidates_selection_some_sound
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidates : List Nat) {output : Nat}
    (hresult : (scanCandidates spec input candidates).selection = some output) :
    output ∈ candidates ∧ CandidateAccepted spec input output := by
  induction candidates generalizing output with
  | nil =>
      simp [scanCandidates] at hresult
  | cons candidate candidates inductionHypothesis =>
      by_cases hacceptedBool : validateCandidate spec input candidate = true
      · have hacceptedProp :=
          (validateCandidate_eq_true_iff spec input candidate).mp hacceptedBool
        have same : candidate = output := by
          apply Option.some.inj
          simpa only [scanCandidates, hacceptedBool, if_pos] using hresult
        subst output
        exact ⟨by simp, hacceptedProp⟩
      · have htail :
            (scanCandidates spec input candidates).selection = some output := by
          simpa [scanCandidates, hacceptedBool] using hresult
        rcases inductionHypothesis htail with ⟨hmember, hacceptedTail⟩
        exact ⟨by simp [hmember], hacceptedTail⟩

private lemma scanCandidates_selection_none_noAccepted
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidates : List Nat)
    (hresult : (scanCandidates spec input candidates).selection = none) :
    ∀ candidate ∈ candidates, ¬ CandidateAccepted spec input candidate := by
  induction candidates with
  | nil => simp
  | cons candidate candidates inductionHypothesis =>
      by_cases hacceptedBool : validateCandidate spec input candidate = true
      · simp [scanCandidates, hacceptedBool] at hresult
      · have hrejected : ¬ CandidateAccepted spec input candidate := by
          intro hacceptedProp
          exact hacceptedBool
            ((validateCandidate_eq_true_iff spec input candidate).mpr hacceptedProp)
        have htail :
            (scanCandidates spec input candidates).selection = none := by
          simpa [scanCandidates, hacceptedBool] using hresult
        intro checked hmember
        rcases List.mem_cons.mp hmember with hsame | hlater
        · subst checked
          exact hrejected
        · exact inductionHypothesis htail checked hlater

/-- A successful scan path ends in the accepted candidate and records only
rejections before that final validation. -/
private lemma scanCandidates_path_some_characterization
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidates : List Nat) {output : Nat}
    (hresult : (scanCandidates spec input candidates).selection = some output) :
    ∃ priorPath,
      (scanCandidates spec input candidates).path =
          priorPath ++ [CandidateValidation.ofCandidate spec input output] ∧
        CandidateAccepted spec input output ∧
          ∀ record ∈ priorPath, record.accepted = false := by
  induction candidates generalizing output with
  | nil =>
      simp [scanCandidates] at hresult
  | cons candidate candidates inductionHypothesis =>
      by_cases hacceptedBool : validateCandidate spec input candidate = true
      · have hvalue : candidate = output := by
          simpa [scanCandidates, hacceptedBool] using hresult
        subst output
        refine ⟨[], ?_,
          (validateCandidate_eq_true_iff spec input candidate).mp hacceptedBool, ?_⟩
        · simp [scanCandidates, hacceptedBool]
        · simp
      · have htail :
            (scanCandidates spec input candidates).selection = some output := by
          simpa [scanCandidates, hacceptedBool] using hresult
        rcases inductionHypothesis htail with
          ⟨priorPath, hpath, houtputAccepted, hpriorPathRejected⟩
        refine ⟨CandidateValidation.ofCandidate spec input candidate :: priorPath,
          ?_, houtputAccepted, ?_⟩
        · simp [scanCandidates, hacceptedBool, hpath, List.cons_append]
        · intro record hmember
          rcases List.mem_cons.mp hmember with hrecord | hprior
          · subst record
            rw [CandidateValidation.ofCandidate_accepted]
            exact validateCandidate_eq_false_of_ne_true spec input candidate hacceptedBool
          · exact hpriorPathRejected record hprior

/-- If the scan fails, it has visited every scheduled candidate. -/
private lemma scanCandidates_path_eq_map_of_selection_none
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidates : List Nat)
    (hresult : (scanCandidates spec input candidates).selection = none) :
    (scanCandidates spec input candidates).path =
      candidates.map (CandidateValidation.ofCandidate spec input) := by
  induction candidates with
  | nil => simp [scanCandidates]
  | cons candidate candidates inductionHypothesis =>
      by_cases hacceptedBool : validateCandidate spec input candidate = true
      · simp [scanCandidates, hacceptedBool] at hresult
      · have htail :
            (scanCandidates spec input candidates).selection = none := by
          simpa [scanCandidates, hacceptedBool] using hresult
        have hpath := inductionHypothesis htail
        simp [scanCandidates, hacceptedBool, hpath]

/-- The strongest honest success condition for an early-stopping scan: the
candidate is the first accepted candidate in this actual schedule. It is not a
claim that the candidate is the global multiplicative order. -/
def FirstAccepted {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    List Nat → Nat → Prop
  | [], _ => False
  | candidate :: candidates, output =>
      (candidate = output ∧ CandidateAccepted spec input candidate) ∨
        (¬ CandidateAccepted spec input candidate ∧
          FirstAccepted spec input candidates output)

private lemma scanCandidates_selection_eq_some_of_firstAccepted
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (candidates : List Nat) {output : Nat}
    (hfirst : FirstAccepted spec input candidates output) :
    (scanCandidates spec input candidates).selection = some output := by
  induction candidates generalizing output with
  | nil =>
      simp [FirstAccepted] at hfirst
  | cons candidate candidates inductionHypothesis =>
      rcases hfirst with hnow | hlater
      · rcases hnow with ⟨hvalue, haccepted⟩
        subst output
        have hacceptedBool :=
          (validateCandidate_eq_true_iff spec input candidate).mpr haccepted
        simp [scanCandidates, hacceptedBool]
      · rcases hlater with ⟨hrejected, hfirstTail⟩
        have hrejectedBool :=
          (validateCandidate_eq_false_iff spec input candidate).mpr hrejected
        simpa [scanCandidates, hrejectedBool] using
          inductionHypothesis hfirstTail

/-- The sealed pure recovery object binds the finite continued-fraction trace,
its unpadded candidate schedule, and the one early-stopping scan. -/
structure RecoveryTrace {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) where
  private mk ::
  /-- The exact finite Euclidean continued-fraction trace. -/
  continuedFraction :
    RationalContinuedFraction.FiniteContinuedFractionTrace
      (decodedIndex input).val (2 ^ phaseBits)
  /-- The unpadded denominator candidates derived from that trace. -/
  candidates : List Nat
  /-- The validations actually executed until success or exhaustion. -/
  scan : ScanResult

/-- Execute the canonical finite, early-stopping recovery path. -/
def recoveryTrace {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    RecoveryTrace spec input :=
  let continuedFraction := finiteContinuedFraction input
  let candidates :=
    (continuedFraction.fractions.map
      RationalContinuedFraction.ReducedRational.denominator)
  .mk continuedFraction candidates (scanCandidates spec input candidates)

/-- The exact finite continued-fraction projection of the recovery path. -/
def continuedFraction {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :=
  (recoveryTrace spec input).continuedFraction

/-- The actual unpadded candidate schedule. -/
def candidateSchedule {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) : List Nat :=
  (recoveryTrace spec input).candidates

/-- The actual candidate-validation path, including each rejection before an
early success. -/
def exactPath {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    List CandidateValidation :=
  (recoveryTrace spec input).scan.path

/-- The first accepted candidate selected by the same actual path. -/
def selection {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) : Option Nat :=
  (recoveryTrace spec input).scan.selection

/-- Arithmetic emitted by the finite continued-fraction construction alone.
Candidate validation is represented by `exactPath`, not by a fabricated
arithmetic or Components trace. -/
def continuedFractionArithmetic {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :=
  (continuedFraction spec input).arithmetic

lemma candidateSchedule_eq_finiteCandidates {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    candidateSchedule spec input = finiteCandidates (decodedIndex input) :=
  rfl

/-- Every mathematical convergent denominator occurs in the genuine unpadded
candidate schedule consumed by the typed recovery routine. -/
lemma realConvergentDen_mem_candidateSchedule
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (index : Nat) :
    ((((decodedIndex input).val : Real) / (2 : Real) ^ phaseBits).convergent
        index).den ∈ candidateSchedule spec input := by
  rw [candidateSchedule_eq_finiteCandidates,
    finiteCandidates_eq_convergents_denominators]
  apply List.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (RationalContinuedFraction.real_convergent_mem
      (decodedIndex input).val (2 ^ phaseBits) index)

/-- The actual candidate schedule is nondecreasing, with equality retained
when distinct convergents share one denominator. -/
lemma candidateSchedule_pairwise_le {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    (candidateSchedule spec input).Pairwise (· ≤ ·) := by
  rw [candidateSchedule_eq_finiteCandidates]
  exact finiteCandidates_pairwise_le (decodedIndex input)

private lemma exists_first_occurrence_of_mem_of_pairwise_le
    {target : Nat} : ∀ {schedule : List Nat},
      schedule.Pairwise (· ≤ ·) → target ∈ schedule →
        ∃ rejected suffix,
          schedule = rejected ++ target :: suffix ∧
            ∀ candidate ∈ rejected, candidate < target
  | [], _pairwise, member => by simp at member
  | candidate :: candidates, pairwise, member => by
      by_cases equal : candidate = target
      · subst candidate
        exact ⟨[], candidates, rfl, by simp⟩
      · have tailMember : target ∈ candidates := by
          rcases List.mem_cons.mp member with head | tail
          · exact (equal head.symm).elim
          · exact tail
        have pairwiseParts := List.pairwise_cons.mp pairwise
        rcases exists_first_occurrence_of_mem_of_pairwise_le
            pairwiseParts.2 tailMember with
          ⟨rejected, suffix, scheduleEq, earlier⟩
        refine ⟨candidate :: rejected, suffix, ?_, ?_⟩
        · simp [scheduleEq]
        · intro prior priorMember
          rcases List.mem_cons.mp priorMember with rfl | rejectedMember
          · exact lt_of_le_of_ne (pairwiseParts.1 target tailMember) equal
          · exact earlier prior rejectedMember

/-- Any scheduled denominator admits a first-occurrence split whose genuine
earlier denominators are strictly smaller. -/
lemma candidateSchedule_firstOccurrence
    {modulusWidth phaseBits target : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (member : target ∈ candidateSchedule spec input) :
    ∃ rejected suffix,
      candidateSchedule spec input = rejected ++ target :: suffix ∧
        ∀ candidate ∈ rejected, candidate < target := by
  exact exists_first_occurrence_of_mem_of_pairwise_le
    (candidateSchedule_pairwise_le spec input) member

/-- The initialized cursor's active visits are exactly the current unpadded
candidate schedule used by recovery. -/
lemma cfPath_initial_eq_candidateSchedule {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    cfPath (initialContinuedFractionState spec input) =
      candidateSchedule spec input := by
  rw [cfPath_initialContinuedFractionState,
    candidateSchedule_eq_finiteCandidates]

/-- The recovery candidate schedule inherits the finite, nonpadding capacity
bound of its continued-fraction source. -/
lemma candidateSchedule_length_le_finiteCandidateFuel
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) :
    (candidateSchedule spec input).length ≤ finiteCandidateFuel phaseBits := by
  rw [candidateSchedule_eq_finiteCandidates]
  exact finiteCandidates_length_le_finiteCandidateFuel (decodedIndex input)

private lemma exactPath_eq_scanPath {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    exactPath spec input =
      (scanCandidates spec input (candidateSchedule spec input)).path :=
  rfl

private lemma selection_eq_scanSelection {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    selection spec input =
      (scanCandidates spec input (candidateSchedule spec input)).selection :=
  rfl

/-- A consecutive rejected prefix followed by an accepted candidate is the
schedule-local first-accepted witness for that candidate. -/
private lemma firstAccepted_of_rejected_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    FirstAccepted spec input (rejected ++ candidate :: suffix) candidate := by
  induction rejected with
  | nil =>
      change
        (candidate = candidate ∧ CandidateAccepted spec input candidate) ∨
          (¬ CandidateAccepted spec input candidate ∧
            FirstAccepted spec input suffix candidate)
      exact Or.inl ⟨rfl, haccepted⟩
  | cons rejectedCandidate rejected inductionHypothesis =>
      have hrejectedCandidate :
          ¬ CandidateAccepted spec input rejectedCandidate :=
        hrejected rejectedCandidate (by simp)
      have hrejectedTail :
          ∀ checked ∈ rejected, ¬ CandidateAccepted spec input checked := by
        intro checked hmember
        exact hrejected checked (by simp [hmember])
      change
        (rejectedCandidate = candidate ∧
            CandidateAccepted spec input rejectedCandidate) ∨
          (¬ CandidateAccepted spec input rejectedCandidate ∧
            FirstAccepted spec input (rejected ++ candidate :: suffix) candidate)
      exact Or.inr
        ⟨hrejectedCandidate, inductionHypothesis hrejectedTail⟩

/-- A concrete schedule split into rejected visits and one accepted visit
proves that the latter is the schedule-local first accepted candidate. -/
lemma firstAccepted_of_candidateSchedule_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hprefix : candidateSchedule spec input = rejected ++ candidate :: suffix)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    FirstAccepted spec input (candidateSchedule spec input) candidate := by
  rw [hprefix]
  exact firstAccepted_of_rejected_prefix spec input rejected candidate suffix
    hrejected haccepted

/-- A scan whose actual schedule has a rejected prefix followed by an
accepted candidate selects that candidate. -/
lemma selection_eq_some_of_candidateSchedule_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hprefix : candidateSchedule spec input = rejected ++ candidate :: suffix)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    selection spec input = some candidate := by
  rw [selection_eq_scanSelection]
  exact scanCandidates_selection_eq_some_of_firstAccepted spec input
    (candidateSchedule spec input)
    (firstAccepted_of_candidateSchedule_prefix spec input rejected candidate suffix
      hprefix hrejected haccepted)

/-- The literal scan path for a rejected prefix stops at its first accepted
candidate, so it contains neither padding nor a later scheduled candidate. -/
private lemma scanCandidates_path_eq_of_rejected_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    (scanCandidates spec input (rejected ++ candidate :: suffix)).path =
      rejected.map (CandidateValidation.ofCandidate spec input) ++
        [CandidateValidation.ofCandidate spec input candidate] := by
  induction rejected with
  | nil =>
      have hacceptedBool : validateCandidate spec input candidate = true :=
        (validateCandidate_eq_true_iff spec input candidate).mpr haccepted
      simp [scanCandidates, hacceptedBool]
  | cons rejectedCandidate rejected inductionHypothesis =>
      have hrejectedCandidate :
          ¬ CandidateAccepted spec input rejectedCandidate :=
        hrejected rejectedCandidate (by simp)
      have hrejectedBool :
          validateCandidate spec input rejectedCandidate = false :=
        (validateCandidate_eq_false_iff spec input rejectedCandidate).mpr
          hrejectedCandidate
      have hrejectedTail :
          ∀ checked ∈ rejected, ¬ CandidateAccepted spec input checked := by
        intro checked hmember
        exact hrejected checked (by simp [hmember])
      have htail := inductionHypothesis hrejectedTail
      simp [scanCandidates, hrejectedBool, htail]

/-- When the actual schedule is a rejected prefix followed by one accepted
candidate, the public path is exactly those rejected validations and that
accepted validation. -/
lemma exactPath_eq_of_candidateSchedule_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hprefix : candidateSchedule spec input = rejected ++ candidate :: suffix)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    exactPath spec input =
      rejected.map (CandidateValidation.ofCandidate spec input) ++
        [CandidateValidation.ofCandidate spec input candidate] := by
  calc
    exactPath spec input =
        (scanCandidates spec input (candidateSchedule spec input)).path :=
      exactPath_eq_scanPath spec input
    _ = rejected.map (CandidateValidation.ofCandidate spec input) ++
        [CandidateValidation.ofCandidate spec input candidate] := by
      rw [hprefix]
      exact scanCandidates_path_eq_of_rejected_prefix spec input
        rejected candidate suffix hrejected haccepted

/-- A successful public path ends at the selected candidate, with every prior
validation recorded as a rejection. -/
lemma exactPath_some_characterization
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) {output : Nat}
    (hselection : selection spec input = some output) :
    ∃ priorPath,
      exactPath spec input =
          priorPath ++ [CandidateValidation.ofCandidate spec input output] ∧
        (CandidateValidation.ofCandidate spec input output).accepted = true ∧
          ∀ record ∈ priorPath, record.accepted = false := by
  have hscan :
      (scanCandidates spec input (candidateSchedule spec input)).selection =
        some output := by
    rw [← selection_eq_scanSelection]
    exact hselection
  rcases scanCandidates_path_some_characterization spec input
    (candidateSchedule spec input) hscan with
      ⟨priorPath, hpath, houtputAccepted, hpriorPathRejected⟩
  refine ⟨priorPath, ?_, ?_, hpriorPathRejected⟩
  · rw [exactPath_eq_scanPath]
    exact hpath
  · rw [CandidateValidation.ofCandidate_accepted]
    exact (validateCandidate_eq_true_iff spec input output).mpr houtputAccepted

/-- A failed public path covers the full finite schedule and records every
candidate as rejected. -/
lemma exactPath_none_characterization
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (hselection : selection spec input = none) :
    exactPath spec input =
        (candidateSchedule spec input).map
          (CandidateValidation.ofCandidate spec input) ∧
      ∀ record ∈ exactPath spec input, record.accepted = false := by
  have hscan :
      (scanCandidates spec input (candidateSchedule spec input)).selection =
        none := by
    rw [← selection_eq_scanSelection]
    exact hselection
  have hpath := scanCandidates_path_eq_map_of_selection_none spec input
    (candidateSchedule spec input) hscan
  have hnoAccepted := scanCandidates_selection_none_noAccepted spec input
    (candidateSchedule spec input) hscan
  constructor
  · rw [exactPath_eq_scanPath]
    exact hpath
  · intro record hrecord
    have hmember :
        record ∈ (candidateSchedule spec input).map
          (CandidateValidation.ofCandidate spec input) := by
      rw [exactPath_eq_scanPath] at hrecord
      rwa [hpath] at hrecord
    rcases List.mem_map.mp hmember with ⟨candidate, hcandidate, hrecord⟩
    subst record
    rw [CandidateValidation.ofCandidate_accepted]
    exact (validateCandidate_eq_false_iff spec input candidate).mpr
      (hnoAccepted candidate hcandidate)

/-- Store an accepted natural denominator in its public output width. -/
def candidateWord (phaseBits candidate : Nat) : Word (phaseBits + 1) :=
  wordOfNat (phaseBits + 1) candidate

lemma candidateWord_val_of_lt {phaseBits candidate : Nat}
    (hfit : candidate < 2 ^ (phaseBits + 1)) :
    (candidateWord phaseBits candidate).val = candidate := by
  change candidate % 2 ^ (phaseBits + 1) = candidate
  exact Nat.mod_eq_of_lt hfit

/-- Canonical typed order recovery. -/
public def recoverUnitOrder {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    Output modulusWidth phaseBits :=
  Option.map (candidateWord phaseBits) (selection spec input)

/-- The conventional evaluator name for canonical typed order recovery. -/
def eval {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    Output modulusWidth phaseBits :=
  recoverUnitOrder spec input

lemma eval_eq_recoverUnitOrder {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    eval spec input = recoverUnitOrder spec input :=
  rfl

/-- Project an optional fixed-width output back to its natural candidate. -/
def candidate {modulusWidth phaseBits : Nat}
    (output : Output modulusWidth phaseBits) : Option Nat :=
  output.map (fun word => word.val)

lemma candidate_recoverUnitOrder {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) :
    candidate (recoverUnitOrder spec input) = selection spec input := by
  unfold candidate recoverUnitOrder
  cases hselection : selection spec input with
  | none => simp
  | some rawCandidate =>
      have hscan :
          (scanCandidates spec input (candidateSchedule spec input)).selection =
            some rawCandidate := by
        rw [← selection_eq_scanSelection]
        exact hselection
      have hsound :=
        scanCandidates_selection_some_sound spec input
          (candidateSchedule spec input) hscan
      have hfit : rawCandidate < 2 ^ (phaseBits + 1) := hsound.2.1
      simp [candidateWord_val_of_lt hfit]

/-- Every successful output is one actually visited finite
continued-fraction denominator and passes the complete modular-return test. -/
lemma recoverUnitOrder_some_sound {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    {output : Word (phaseBits + 1)}
    (hresult : recoverUnitOrder spec input = some output) :
    output.val ∈ candidateSchedule spec input ∧
      0 < output.val ∧
        output.val < 2 ^ (phaseBits + 1) ∧
          input.base.val ^ output.val ≡ 1 [MOD spec.modulusSpec.modulus] := by
  have hselection : selection spec input = some output.val := by
    calc
      selection spec input = candidate (recoverUnitOrder spec input) :=
        (candidate_recoverUnitOrder spec input).symm
      _ = some output.val := by simp [candidate, hresult]
  have hscan :
      (scanCandidates spec input (candidateSchedule spec input)).selection =
        some output.val := by
    rw [← selection_eq_scanSelection]
    exact hselection
  rcases scanCandidates_selection_some_sound spec input
    (candidateSchedule spec input) hscan with ⟨hmember, haccepted⟩
  exact ⟨hmember, haccepted.2.1, haccepted.1, haccepted.2.2⟩

/-- No candidate of the actual finite schedule passed complete validation. -/
def NoAcceptedCandidate {modulusWidth phaseBits : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec) : Prop :=
  ∀ candidate ∈ candidateSchedule spec input,
    ¬ CandidateAccepted spec input candidate

/-- Failure exposes exactly the absence of an accepted actual candidate; it
does not conceal skipped padding or an unvisited later candidate. -/
lemma recoverUnitOrder_eq_none_iff_noAcceptedCandidate
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) :
    recoverUnitOrder spec input = none ↔ NoAcceptedCandidate spec input := by
  constructor
  · intro hresult
    have hselection : selection spec input = none := by
      cases hraw : selection spec input with
      | none => simp
      | some rawCandidate =>
          simp [recoverUnitOrder, hraw] at hresult
    have hscan :
        (scanCandidates spec input (candidateSchedule spec input)).selection =
          none := by
      rw [← selection_eq_scanSelection]
      exact hselection
    exact scanCandidates_selection_none_noAccepted spec input
      (candidateSchedule spec input) hscan
  · intro hnone
    have hscan :
        (scanCandidates spec input (candidateSchedule spec input)).selection =
          none := by
      cases hraw :
          (scanCandidates spec input (candidateSchedule spec input)).selection with
      | none => simp
      | some rawCandidate =>
          rcases scanCandidates_selection_some_sound spec input
            (candidateSchedule spec input) hraw with ⟨hmember, haccepted⟩
          exact (hnone rawCandidate hmember haccepted).elim
    have hselection : selection spec input = none := by
      rw [selection_eq_scanSelection]
      exact hscan
    simp [recoverUnitOrder, hselection]

/-- A rejected schedule prefix followed by an accepted candidate produces the
corresponding fixed-width recovery output. -/
lemma recoverUnitOrder_eq_some_of_candidateSchedule_prefix
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec) (rejected : List Nat) (candidate : Nat)
    (suffix : List Nat)
    (hprefix : candidateSchedule spec input = rejected ++ candidate :: suffix)
    (hrejected : ∀ rejectedCandidate ∈ rejected,
      ¬ CandidateAccepted spec input rejectedCandidate)
    (haccepted : CandidateAccepted spec input candidate) :
    recoverUnitOrder spec input =
      some (candidateWord phaseBits candidate) := by
  have selected : selection spec input = some candidate :=
    selection_eq_some_of_candidateSchedule_prefix spec input
      rejected candidate suffix hprefix hrejected haccepted
  simp [recoverUnitOrder, selected]

/-- A source-facing recoverable schedule split selects the true order in the
typed routine.

The hypotheses deliberately expose exactly what a continued-fraction bridge
must prove: the true order occurs in the actual unpadded candidate schedule,
every earlier denominator is strictly smaller, the public output width fits
the order, and the order is the least positive modular return.  No legacy
recovery evaluator or detached post-processing function enters the result. -/
lemma recoverUnitOrder_eq_some_of_recoverableSchedule
    {modulusWidth phaseBits order : Nat}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (rejected suffix : List Nat)
    (schedule : candidateSchedule spec input = rejected ++ order :: suffix)
    (earlier : ∀ candidate ∈ rejected, candidate < order)
    (fits : order < 2 ^ (phaseBits + 1))
    (minimal : MinimalUnitOrder spec input order) :
    recoverUnitOrder spec input = some (candidateWord phaseBits order) := by
  apply recoverUnitOrder_eq_some_of_candidateSchedule_prefix spec input
    rejected order suffix schedule
  · intro candidate member accepted
    exact minimal.2.2 candidate accepted.2.1 (earlier candidate member)
      accepted.2.2
  · exact ⟨fits, minimal.1, minimal.2.1⟩

/-- If every candidate in the actual finite schedule is rejected, recovery
returns no candidate. -/
lemma recoverUnitOrder_eq_none_of_all_scheduled_rejected
    {modulusWidth phaseBits : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec)
    (hrejected : ∀ candidate ∈ candidateSchedule spec input,
      ¬ CandidateAccepted spec input candidate) :
    recoverUnitOrder spec input = none := by
  exact (recoverUnitOrder_eq_none_iff_noAcceptedCandidate spec input).mpr
    hrejected

/-- The early-stopping scan recovers a candidate exactly under the honest
schedule-local first-accepted condition. No global order-minimality conclusion
is asserted here. -/
lemma recoverUnitOrder_eq_some_of_firstAccepted
    {modulusWidth phaseBits order : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec)
    (hfirst : FirstAccepted spec input (candidateSchedule spec input) order) :
    recoverUnitOrder spec input = some (candidateWord phaseBits order) := by
  have hscan :
      (scanCandidates spec input (candidateSchedule spec input)).selection =
        some order :=
    scanCandidates_selection_eq_some_of_firstAccepted spec input
      (candidateSchedule spec input) hfirst
  have hselection : selection spec input = some order := by
    rw [selection_eq_scanSelection]
    exact hscan
  simp [recoverUnitOrder, hselection]

/-- Exact recovery of the mathematical order requires two separate facts:
the least positive return exponent is present as the scan's first accepted
candidate, and that exponent really is minimal.  Minimality alone cannot
prevent an earlier nonminimal multiple from passing modular validation. -/
lemma recoverUnitOrder_eq_some_of_firstAccepted_minimal
    {modulusWidth phaseBits order : Nat} (spec : Spec modulusWidth phaseBits)
    (input : Input spec)
    (hfirst : FirstAccepted spec input (candidateSchedule spec input) order)
    (hminimal : MinimalUnitOrder spec input order) :
    recoverUnitOrder spec input = some (candidateWord phaseBits order) ∧
      MinimalUnitOrder spec input order := by
  exact ⟨recoverUnitOrder_eq_some_of_firstAccepted spec input hfirst, hminimal⟩

/-- A concrete fixed-width specification for the finite `5 / 64` regression. -/
def fifteenTwoSixSpec : Spec 4 6 where
  modulusSpec :=
    { modulus := 15
      two_le := by norm_num
      le_capacity := by norm_num [ClassicalAlgorithms.modulus] }

/-- The fixed-width base used by the finite `5 / 64` regression. -/
def fifteenTwoSixBase : Word 4 := ⟨2, by norm_num⟩

/-- The terminal index used by the finite `5 / 64` regression. -/
def fifteenTwoSixIndex : Word 6 := ⟨5, by norm_num⟩

/-- A typed input whose raw terminal bits are explicitly big-endian. -/
def fifteenTwoSixInput : Input fifteenTwoSixSpec where
  base := fifteenTwoSixBase
  baseInDomain := by norm_num [fifteenTwoSixBase, fifteenTwoSixSpec]
  baseCoprime := by norm_num [fifteenTwoSixBase, fifteenTwoSixSpec]
  terminalBits := terminalMeasurement 6 fifteenTwoSixIndex

lemma decodedIndex_fifteenTwoSix :
    decodedIndex fifteenTwoSixInput = fifteenTwoSixIndex := by
  simpa [decodedIndex, fifteenTwoSixInput] using
    (fullRegisterIndex_terminalMeasurement 6 fifteenTwoSixIndex)

/-- The unpadded finite convergent denominators for `5 / 64`. -/
lemma finiteCandidates_five_of_six :
    finiteCandidates (⟨5, by norm_num⟩ : Word 6) = [1, 12, 13, 64] := by
  have hconvergents :
      RationalContinuedFraction.convergents 5 64 =
        [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13, (5 : ℚ) / 64] := by
    rw [RationalContinuedFraction.convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [RationalContinuedFraction.convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [RationalContinuedFraction.convergents_eq_cons_of_mod_ne_zero
      (by norm_num) (by norm_num)]
    rw [RationalContinuedFraction.convergents_eq_singleton_of_mod_eq_zero
      (by norm_num) (by norm_num)]
    norm_num
  have hvalues :
      (RationalContinuedFraction.finiteContinuedFractionTrace 5 64).fractions.map
          RationalContinuedFraction.ReducedRational.value =
        [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13, (5 : ℚ) / 64] := by
    rw [RationalContinuedFraction.finiteContinuedFractionTrace_values,
      hconvergents]
  have hdenominators :
      (RationalContinuedFraction.finiteContinuedFractionTrace 5 64).fractions.map
          RationalContinuedFraction.ReducedRational.denominator =
        [1, 12, 13, 64] := by
    have hfive : (((5 : ℚ) / 64).den) = 64 := by
      change ((((5 : Int) : ℚ) / ((64 : Int) : ℚ)).den) = 64
      have hfiveInt :=
        Rat.den_div_eq_of_coprime
          (a := 5) (b := 64) (by norm_num)
            (by decide : Nat.Coprime (5 : Int).natAbs (64 : Int).natAbs)
      exact_mod_cast hfiveInt
    calc
      (RationalContinuedFraction.finiteContinuedFractionTrace 5 64).fractions.map
          RationalContinuedFraction.ReducedRational.denominator =
          ((RationalContinuedFraction.finiteContinuedFractionTrace 5 64).fractions.map
            RationalContinuedFraction.ReducedRational.value).map
              (fun value : ℚ => value.den) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro fraction _hmem
            exact (RationalContinuedFraction.ReducedRational.value_den fraction).symm
      _ = [(0 : ℚ), (1 : ℚ) / 12, (1 : ℚ) / 13,
          (5 : ℚ) / 64].map (fun value : ℚ => value.den) := by
            rw [hvalues]
      _ = [1, 12, 13, 64] := by
            simp [hfive]
  change
    (RationalContinuedFraction.finiteContinuedFractionTrace 5 64).fractions.map
      RationalContinuedFraction.ReducedRational.denominator =
        [1, 12, 13, 64]
  exact hdenominators

lemma candidateSchedule_fifteenTwoSix :
    candidateSchedule fifteenTwoSixSpec fifteenTwoSixInput = [1, 12, 13, 64] := by
  rw [candidateSchedule_eq_finiteCandidates, decodedIndex_fifteenTwoSix]
  simpa [fifteenTwoSixIndex] using finiteCandidates_five_of_six

lemma validateCandidate_fifteenTwoSix_one :
    validateCandidate fifteenTwoSixSpec fifteenTwoSixInput 1 = false := by
  norm_num [validateCandidate, CandidateAccepted, fifteenTwoSixSpec,
    fifteenTwoSixInput, fifteenTwoSixBase]

lemma validateCandidate_fifteenTwoSix_twelve :
    validateCandidate fifteenTwoSixSpec fifteenTwoSixInput 12 = true := by
  norm_num [validateCandidate, CandidateAccepted, fifteenTwoSixSpec,
    fifteenTwoSixInput, fifteenTwoSixBase]

lemma selection_fifteen_two_six_five :
    selection fifteenTwoSixSpec fifteenTwoSixInput = some 12 := by
  rw [selection_eq_scanSelection, candidateSchedule_fifteenTwoSix]
  simp [scanCandidates, validateCandidate_fifteenTwoSix_one,
    validateCandidate_fifteenTwoSix_twelve]

/-- Finite regression: the explicit `5 / 64` measurement first validates
denominator twelve. This records a schedule-local raw candidate only; it does
not assert that every raw recovery candidate is the true multiplicative order. -/
lemma recoverUnitOrder_fifteen_two_six_five :
    recoverUnitOrder fifteenTwoSixSpec fifteenTwoSixInput =
      some (candidateWord 6 12) := by
  simp [recoverUnitOrder, selection_fifteen_two_six_five]

lemma candidate_recoverUnitOrder_fifteen_two_six_five :
    candidate (recoverUnitOrder fifteenTwoSixSpec fifteenTwoSixInput) = some 12 := by
  rw [candidate_recoverUnitOrder, selection_fifteen_two_six_five]

end OrderRecovery

end ClassicalAlgorithms
end QuantumAlg

end

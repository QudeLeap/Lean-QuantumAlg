/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.ExactArithmetic
import all QuantumAlg.Util.NumberTheory.RationalContinuedFraction
import Mathlib.Data.List.MinMax

/-!
# Executable multiplicative-order recovery

This module scans every slot of the fixed rational-convergent schedule. Each
slot runs a fixed-width modular exponentiation and carries the arithmetic
events emitted by that same run. The final value is the least visited positive
in-width denominator whose computed power is one.

The trace constructor is private: clients may project the candidates, output,
and arithmetic, but cannot attach an unrelated result or charge.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- One actually executed denominator-validation slot. -/
structure MultiplicativeOrderSlotTrace (modulus : Nat) where
  private mk ::
  /-- Continued-fraction denominator visited by this slot. -/
  candidate : Nat
  /-- Public natural representative normalized for this slot's modular power. -/
  base : Nat
  /-- Fixed-width modular-power execution for the same candidate. -/
  power : ModularPowerTrace modulus

namespace MultiplicativeOrderSlotTrace

/-- A slot validates exactly when its positive denominator fits the public
phase-width schedule and the modular-power execution returns one. -/
def Accepts {modulus : Nat}
    (phaseBits : Nat) (slot : MultiplicativeOrderSlotTrace modulus) : Prop :=
  slot.candidate < 2 ^ (phaseBits + 1) ∧
    0 < slot.candidate ∧ slot.power.value = 1

instance instDecidableAccepts {modulus phaseBits : Nat}
    (slot : MultiplicativeOrderSlotTrace modulus) :
    Decidable (slot.Accepts phaseBits) := by
  unfold Accepts
  infer_instance

/-- Optional validated candidate projected from the same modular-power slot. -/
def accepted {modulus : Nat} (phaseBits : Nat)
    (slot : MultiplicativeOrderSlotTrace modulus) : Option Nat :=
  if slot.Accepts phaseBits then some slot.candidate else none

/-- Operand-sensitive events emitted by one complete validation slot.  Base
normalization and the exponent-width guard precede modular power; the three
acceptance comparisons are then executed unconditionally, so the trace does
not hide short-circuit work behind the acceptance predicate. -/
def arithmetic {modulus : Nat} (phaseBits : Nat)
    (slot : MultiplicativeOrderSlotTrace modulus) : List ArithmeticEvent :=
  [ .natMod slot.base modulus
  , .natLt slot.candidate (2 ^ (phaseBits + 1)) ] ++
    slot.power.arithmetic ++
    [ .natLt slot.candidate (2 ^ (phaseBits + 1))
    , .natLt 0 slot.candidate
    , .natEq slot.power.value.val (1 : ZMod modulus).val ]

end MultiplicativeOrderSlotTrace

/-- Exponent supplied to a fixed public-width scan. Oversized denominators are
rejected by the slot and use zero only to keep the arithmetic schedule total. -/
private def boundedRecoveryExponent (phaseBits candidate : Nat) : Nat :=
  if candidate < 2 ^ (phaseBits + 1) then candidate else 0

/-- The exponent supplied to the binary scan always fits its public width. -/
private lemma boundedRecoveryExponent_lt (phaseBits candidate : Nat) :
    boundedRecoveryExponent phaseBits candidate <
      2 ^ (phaseBits + 1) := by
  unfold boundedRecoveryExponent
  split
  · assumption
  · positivity

/-- Execute one fixed-width denominator-validation slot. -/
private def multiplicativeOrderSlotTrace
    (modulus base phaseBits candidate : Nat) :
    MultiplicativeOrderSlotTrace modulus :=
  let power :=
    modularPowerTrace (phaseBits + 1) (base : ZMod modulus)
      (boundedRecoveryExponent phaseBits candidate)
  .mk candidate base power

/-- Internal state of the least-candidate scan.  Arithmetic is accumulated in
reverse so each retention comparison is constant-time list construction. -/
private structure LeastAcceptedState where
  best : Option Nat
  arithmeticRev : List ArithmeticEvent

/-- Visit one accepted candidate using the same strict comparison as
`List.argmin`. -/
private def retainLeast
    (state : LeastAcceptedState) (candidate : Nat) :
    LeastAcceptedState :=
  match state.best with
  | none =>
      { best := some candidate, arithmeticRev := state.arithmeticRev }
  | some best =>
      { best := List.argAux (fun left right : Nat => left < right)
          (some best) candidate,
        arithmeticRev := .natLt candidate best :: state.arithmeticRev }

/-- Visit one schedule slot. Rejected slots preserve the accumulator; accepted
slots execute the ordinary least-candidate update. -/
private def retainLeastOption
    (state : LeastAcceptedState) : Option Nat → LeastAcceptedState
  | none => state
  | some candidate => retainLeast state candidate

private lemma foldl_retainLeastOption_eq_filterMap
    (values : List (Option Nat)) (state : LeastAcceptedState) :
    values.foldl retainLeastOption state =
      (values.filterMap id).foldl retainLeast state := by
  induction values generalizing state with
  | nil => rfl
  | cons value rest ih =>
      cases value with
      | none => simpa [retainLeastOption] using ih state
      | some candidate =>
          simpa [retainLeastOption] using
            ih (retainLeast state candidate)

@[simp] private lemma retainLeast_best
    (state : LeastAcceptedState) (candidate : Nat) :
    (retainLeast state candidate).best =
      List.argAux (fun left right : Nat => left < right)
        state.best candidate := by
  cases state with
  | mk best arithmeticRev =>
      cases best <;> rfl

/-- Folding the traced state computes exactly Mathlib's finite argmin. -/
private lemma foldl_retainLeast_best
    (values : List Nat) (state : LeastAcceptedState) :
    (values.foldl retainLeast state).best =
      values.foldl
        (List.argAux (fun left right : Nat => left < right))
        state.best := by
  induction values generalizing state with
  | nil => rfl
  | cons candidate values ih =>
      simp only [List.foldl_cons]
      rw [ih, retainLeast_best]

/-- A sealed execution of the final least-accepted-candidate scan. -/
structure LeastAcceptedTrace (values : List (Option Nat)) where
  private mk ::
  /-- Least accepted candidate, if any. -/
  output : Option Nat
  /-- Strict comparisons actually evaluated by the scan. -/
  arithmetic : List ArithmeticEvent

/-- Execute one retention visit for every fixed-schedule slot. -/
def leastAcceptedTrace (values : List (Option Nat)) :
    LeastAcceptedTrace values :=
  let state :=
    values.foldl retainLeastOption
      { best := none, arithmeticRev := [] }
  .mk state.best state.arithmeticRev.reverse

/-- The traced selector computes the ordinary finite argmin. -/
lemma leastAcceptedTrace_output (values : List (Option Nat)) :
    (leastAcceptedTrace values).output =
      List.argmin id (values.filterMap id) := by
  rw [leastAcceptedTrace]
  change
    (values.foldl retainLeastOption
      { best := none, arithmeticRev := [] }).best =
        List.argmin id (values.filterMap id)
  rw [foldl_retainLeastOption_eq_filterMap, foldl_retainLeast_best]
  rfl

/-- One selector step preserves a common operand-width bound on both its
retained candidate and the comparisons accumulated so far. -/
private lemma retainLeast_width_invariant
    (state : LeastAcceptedState) (candidate width : Nat)
    (harithmetic :
      arithmeticEventListMaxOperandWidth state.arithmeticRev ≤ width)
    (hbest :
      ∀ best, state.best = some best → Nat.size best ≤ width)
    (hcandidate : Nat.size candidate ≤ width) :
    arithmeticEventListMaxOperandWidth
        (retainLeast state candidate).arithmeticRev ≤ width ∧
      ∀ best, (retainLeast state candidate).best = some best →
        Nat.size best ≤ width := by
  rcases state with ⟨best, arithmeticRev⟩
  cases best with
  | none =>
      constructor
      · simpa [retainLeast] using harithmetic
      · intro retained hretained
        have heq : candidate = retained := by
          simpa [retainLeast] using hretained
        simpa [← heq] using hcandidate
  | some current =>
      have hcurrent : Nat.size current ≤ width :=
        hbest current rfl
      constructor
      · change
          arithmeticEventListMaxOperandWidth
              (.natLt candidate current :: arithmeticRev) ≤ width
        rw [arithmeticEventListMaxOperandWidth_cons]
        exact max_le (max_le hcandidate hcurrent) harithmetic
      · intro retained hretained
        by_cases hlt : candidate < current
        · have heq : candidate = retained := by
            simpa [retainLeast, List.argAux, hlt] using hretained
          simpa [← heq] using hcandidate
        · have heq : current = retained := by
            simpa [retainLeast, List.argAux, hlt] using hretained
          simpa [← heq] using hcurrent

/-- Folding the selector preserves a pointwise width bound on every visited
candidate and on every strict comparison emitted by the fold. -/
private lemma foldl_retainLeast_width_invariant
    (values : List Nat) (state : LeastAcceptedState) (width : Nat)
    (harithmetic :
      arithmeticEventListMaxOperandWidth state.arithmeticRev ≤ width)
    (hbest :
      ∀ best, state.best = some best → Nat.size best ≤ width)
    (hvalues : ∀ value ∈ values, Nat.size value ≤ width) :
    arithmeticEventListMaxOperandWidth
        (values.foldl retainLeast state).arithmeticRev ≤ width ∧
      ∀ best, (values.foldl retainLeast state).best = some best →
        Nat.size best ≤ width := by
  induction values generalizing state with
  | nil =>
      exact ⟨harithmetic, hbest⟩
  | cons candidate rest ih =>
      have hcandidate : Nat.size candidate ≤ width :=
        hvalues candidate (by simp)
      have hstep :=
        retainLeast_width_invariant
          state candidate width harithmetic hbest hcandidate
      rw [List.foldl_cons]
      exact ih (retainLeast state candidate) hstep.1 hstep.2
        (by
          intro value hvalue
          exact hvalues value (by simp [hvalue]))

/-- The selector emits at most one strict comparison per input option. -/
private lemma foldl_retainLeast_arithmeticRev_length_le
    (values : List Nat) (state : LeastAcceptedState) :
    (values.foldl retainLeast state).arithmeticRev.length ≤
      state.arithmeticRev.length + values.length := by
  induction values generalizing state with
  | nil => simp
  | cons candidate rest ih =>
      rw [List.foldl_cons]
      calc
        (rest.foldl retainLeast
            (retainLeast state candidate)).arithmeticRev.length ≤
            (retainLeast state candidate).arithmeticRev.length +
              rest.length :=
          ih (retainLeast state candidate)
        _ ≤ state.arithmeticRev.length + 1 + rest.length := by
          rcases state with ⟨best, arithmeticRev⟩
          cases best <;> simp [retainLeast]
        _ = state.arithmeticRev.length + (candidate :: rest).length := by
          simp only [List.length_cons]
          omega

/-- The sealed selector evaluates no more strict comparisons than there are
input slots, including rejected slots. -/
lemma leastAcceptedTrace_arithmetic_length_le
    (values : List (Option Nat)) :
    (leastAcceptedTrace values).arithmetic.length ≤ values.length := by
  let accepted := values.filterMap id
  have hfold :=
    foldl_retainLeast_arithmeticRev_length_le accepted
      { best := none, arithmeticRev := [] }
  have hfold' :
      (accepted.foldl retainLeast
        { best := none, arithmeticRev := [] }).arithmeticRev.length ≤
          accepted.length := by
    simpa using hfold
  have hfilter : (values.filterMap id).length ≤ values.length :=
    List.length_filterMap_le id values
  change
    ((values.foldl retainLeastOption
      { best := none, arithmeticRev := [] }).arithmeticRev.reverse).length ≤
        values.length
  rw [foldl_retainLeastOption_eq_filterMap, List.length_reverse]
  exact hfold'.trans (by simpa [accepted] using hfilter)

/-- When every accepted input fits a common binary width, all comparisons in
the sealed selector fit the same width. -/
lemma leastAcceptedTrace_maxOperandWidth_le
    (values : List (Option Nat)) (width : Nat)
    (hvalues :
      ∀ value ∈ values.filterMap id, Nat.size value ≤ width) :
    arithmeticEventListMaxOperandWidth
        (leastAcceptedTrace values).arithmetic ≤ width := by
  let accepted := values.filterMap id
  have hfold :=
    (foldl_retainLeast_width_invariant accepted
      { best := none, arithmeticRev := [] } width
      (by simp [arithmeticEventListMaxOperandWidth])
      (by simp) (by simpa [accepted] using hvalues)).1
  change
    arithmeticEventListMaxOperandWidth
      ((values.foldl retainLeastOption
        { best := none, arithmeticRev := [] }).arithmeticRev.reverse) ≤ width
  rw [foldl_retainLeastOption_eq_filterMap]
  apply arithmeticEventListMaxOperandWidth_le
  intro event hevent
  have heventForward :
      event ∈
        (accepted.foldl retainLeast
          { best := none, arithmeticRev := [] }).arithmeticRev := by
    simpa [accepted] using hevent
  exact
    (ArithmeticEvent.operandWidth_le_listMax heventForward).trans hfold

/-- A sealed recovery execution over the full fixed denominator schedule. -/
structure MultiplicativeOrderRecoveryTrace
    (modulus : Nat) {phaseBits : Nat}
    (numerator : Fin (2 ^ phaseBits)) where
  private mk ::
  /-- Exact continued-fraction execution for the measured dyadic rational. -/
  continuedFraction :
    RationalContinuedFraction.DyadicContinuedFractionTrace numerator
  /-- Every visited denominator slot, including repeated padding slots. -/
  slots : List (MultiplicativeOrderSlotTrace modulus)
  /-- Least accepted candidate selected from those exact slots. -/
  selection :
    LeastAcceptedTrace
      (slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits))

/-- Least visited positive in-width denominator whose computed power is one. -/
def MultiplicativeOrderRecoveryTrace.output
    {modulus phaseBits : Nat} {numerator : Fin (2 ^ phaseBits)}
    (trace : MultiplicativeOrderRecoveryTrace modulus numerator) : Option Nat :=
  trace.selection.output

/-- Exact arithmetic emitted by continued fractions, candidate validation,
and least-result retention, in execution order. -/
def MultiplicativeOrderRecoveryTrace.arithmetic
    {modulus phaseBits : Nat} {numerator : Fin (2 ^ phaseBits)}
    (trace : MultiplicativeOrderRecoveryTrace modulus numerator) :
    List ArithmeticEvent :=
  trace.continuedFraction.arithmetic ++
    trace.slots.flatMap
      (MultiplicativeOrderSlotTrace.arithmetic phaseBits) ++
    trace.selection.arithmetic

/-- Execute the complete fixed measured-phase recovery schedule. -/
def multiplicativeOrderRecoveryTrace
    (modulus base phaseBits : Nat) (numerator : Fin (2 ^ phaseBits)) :
    MultiplicativeOrderRecoveryTrace modulus numerator :=
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let slots :=
    continuedFraction.denominators.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  .mk continuedFraction slots
    (leastAcceptedTrace
      (slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits)))

/-- The trace visits exactly the public fixed number of denominator slots. -/
lemma multiplicativeOrderRecoveryTrace_slots_length
    (modulus base phaseBits : Nat) (numerator : Fin (2 ^ phaseBits)) :
    (multiplicativeOrderRecoveryTrace
      modulus base phaseBits numerator).slots.length =
        RationalContinuedFraction.dyadicFuel phaseBits := by
  simp [multiplicativeOrderRecoveryTrace,
    RationalContinuedFraction.dyadicContinuedFractionTrace_denominators_length]

/-- Every slot emits base normalization, the exponent guard, seven
modular-power events per public exponent bit, and three validation
comparisons. -/
lemma multiplicativeOrderSlotTrace_arithmetic_length
    (modulus base phaseBits candidate : Nat) :
    (MultiplicativeOrderSlotTrace.arithmetic phaseBits
      (multiplicativeOrderSlotTrace
        modulus base phaseBits candidate)).length =
        7 * (phaseBits + 1) + 5 := by
  simp [MultiplicativeOrderSlotTrace.arithmetic,
    multiplicativeOrderSlotTrace,
    modularPowerTrace_arithmetic_length]

/-- Every operand in an actually executed validation slot is bounded by the
combined public modulus, base representative, and phase-register envelope. -/
private lemma multiplicativeOrderSlotTrace_maxOperandWidth_le
    (modulus base phaseBits candidate : Nat) (hmodulus : 0 < modulus)
    (hcandidate : candidate ≤ 2 ^ phaseBits) :
    arithmeticEventListMaxOperandWidth
        (MultiplicativeOrderSlotTrace.arithmetic phaseBits
          (multiplicativeOrderSlotTrace
            modulus base phaseBits candidate)) ≤
      2 * (Nat.size modulus + Nat.size base + phaseBits + 2) := by
  let _ : NeZero modulus := ⟨Nat.ne_of_gt hmodulus⟩
  let exponent := boundedRecoveryExponent phaseBits candidate
  let power :=
    modularPowerTrace (phaseBits + 1) (base : ZMod modulus) exponent
  let envelope := Nat.size modulus + Nat.size base + phaseBits + 2
  have hpower :
      arithmeticEventListMaxOperandWidth power.arithmetic ≤
        2 * envelope := by
    have hbound :=
      modularPowerTrace_maxOperandWidth_le
        (base : ZMod modulus) hmodulus
          (boundedRecoveryExponent_lt phaseBits candidate)
    have hbound' :
        arithmeticEventListMaxOperandWidth power.arithmetic ≤
          2 * (Nat.size modulus + (phaseBits + 1) + 1) := by
      simpa only [power, exponent] using hbound
    exact hbound'.trans (by dsimp [envelope]; omega)
  have hcandidateSize : Nat.size candidate ≤ phaseBits + 1 := by
    calc
      Nat.size candidate ≤ Nat.size (2 ^ phaseBits) :=
        Nat.size_le_size hcandidate
      _ = phaseBits + 1 := by simp [Nat.size_pow]
  have hcandidateEnvelope : Nat.size candidate ≤ 2 * envelope := by
    exact hcandidateSize.trans (by dsimp [envelope]; omega)
  have hthresholdEnvelope :
      Nat.size (2 ^ (phaseBits + 1)) ≤ 2 * envelope := by
    simp only [Nat.size_pow]
    dsimp [envelope]
    omega
  have hzeroEnvelope : Nat.size 0 ≤ 2 * envelope := by
    simp [envelope]
  have hbaseEnvelope : Nat.size base ≤ 2 * envelope := by
    dsimp [envelope]
    omega
  have hmodulusEnvelope : Nat.size modulus ≤ 2 * envelope := by
    dsimp [envelope]
    omega
  have hpowerValueEnvelope : Nat.size power.value.val ≤ 2 * envelope := by
    calc
      Nat.size power.value.val ≤ Nat.size modulus :=
        Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt power.value))
      _ ≤ 2 * envelope := by dsimp [envelope]; omega
  have honeValueEnvelope :
      Nat.size (1 : ZMod modulus).val ≤ 2 * envelope := by
    calc
      Nat.size (1 : ZMod modulus).val ≤ Nat.size modulus :=
        Nat.size_le_size
          (Nat.le_of_lt (ZMod.val_lt (1 : ZMod modulus)))
      _ ≤ 2 * envelope := by dsimp [envelope]; omega
  change
    arithmeticEventListMaxOperandWidth
        ([ .natMod base modulus
         , .natLt candidate (2 ^ (phaseBits + 1)) ] ++
          power.arithmetic ++
          [ .natLt candidate (2 ^ (phaseBits + 1))
          , .natLt 0 candidate
          , .natEq power.value.val (1 : ZMod modulus).val ]) ≤
      2 * envelope
  simp only [arithmeticEventListMaxOperandWidth_append]
  exact
    max_le
      (max_le
        (by
          apply arithmeticEventListMaxOperandWidth_le
          intro event hevent
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
          rcases hevent with rfl | rfl
          · exact max_le hbaseEnvelope hmodulusEnvelope
          · exact max_le hcandidateEnvelope hthresholdEnvelope)
        hpower)
      (by
        apply arithmeticEventListMaxOperandWidth_le
        intro event hevent
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
        rcases hevent with rfl | rfl | rfl
        · exact max_le hcandidateEnvelope hthresholdEnvelope
        · exact max_le hzeroEnvelope hcandidateEnvelope
        · exact max_le hpowerValueEnvelope honeValueEnvelope)

/-- A list of denominator slots emits the fixed validation schedule once for
every visited denominator. -/
private lemma multiplicativeOrderSlots_arithmetic_length
    (modulus base phaseBits : Nat) (candidates : List Nat) :
    ((candidates.map
        (multiplicativeOrderSlotTrace modulus base phaseBits)).flatMap
      (MultiplicativeOrderSlotTrace.arithmetic phaseBits)).length =
        candidates.length * (7 * (phaseBits + 1) + 5) := by
  induction candidates with
  | nil => simp
  | cons candidate rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_append,
        List.length_cons,
        multiplicativeOrderSlotTrace_arithmetic_length, ih]
      ring

/-- A complete list of actual denominator-validation slots preserves the
common public max-operand envelope. -/
private lemma multiplicativeOrderSlots_maxOperandWidth_le
    (modulus base phaseBits : Nat) (candidates : List Nat)
    (hmodulus : 0 < modulus)
    (hcandidates :
      ∀ candidate ∈ candidates, candidate ≤ 2 ^ phaseBits) :
    arithmeticEventListMaxOperandWidth
        ((candidates.map
            (multiplicativeOrderSlotTrace modulus base phaseBits)).flatMap
          (MultiplicativeOrderSlotTrace.arithmetic phaseBits)) ≤
      2 * (Nat.size modulus + Nat.size base + phaseBits + 2) := by
  apply arithmeticEventListMaxOperandWidth_le
  intro event hevent
  rcases List.mem_flatMap.mp hevent with
    ⟨slot, hslot, hevent⟩
  rcases List.mem_map.mp hslot with
    ⟨candidate, hcandidate, rfl⟩
  exact
    (ArithmeticEvent.operandWidth_le_listMax hevent).trans
      (multiplicativeOrderSlotTrace_maxOperandWidth_le
        modulus base phaseBits candidate hmodulus
          (hcandidates candidate hcandidate))

/-- Every value retained by the validation-option projection fits the public
phase-width schedule. -/
private lemma acceptedCandidates_size_le
    {modulus phaseBits : Nat}
    (slots : List (MultiplicativeOrderSlotTrace modulus)) :
    ∀ candidate ∈
        (slots.map
          (MultiplicativeOrderSlotTrace.accepted phaseBits)).filterMap id,
      Nat.size candidate ≤ phaseBits + 1 := by
  intro candidate hcandidate
  rcases List.mem_filterMap.mp hcandidate with
    ⟨accepted, haccepted, hcandidateEq⟩
  rcases List.mem_map.mp haccepted with
    ⟨slot, _hslot, hslotEq⟩
  subst accepted
  unfold MultiplicativeOrderSlotTrace.accepted at hcandidateEq
  split at hcandidateEq
  next haccepts =>
    have heq : slot.candidate = candidate := by
      simpa using hcandidateEq
    rw [← heq]
    exact Nat.size_le.2 haccepts.1
  next =>
    simp at hcandidateEq

/-- The final least-candidate selection compares only accepted in-width
denominators, so its operands fit the public phase width. -/
lemma multiplicativeOrderRecoveryTrace_selection_maxOperandWidth_le
    (modulus base phaseBits : Nat)
    (numerator : Fin (2 ^ phaseBits)) :
    arithmeticEventListMaxOperandWidth
        (multiplicativeOrderRecoveryTrace
          modulus base phaseBits numerator).selection.arithmetic ≤
      phaseBits + 1 := by
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let slots :=
    continuedFraction.denominators.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  change
    arithmeticEventListMaxOperandWidth
        (leastAcceptedTrace
          (slots.map
            (MultiplicativeOrderSlotTrace.accepted phaseBits))).arithmetic ≤
      phaseBits + 1
  exact leastAcceptedTrace_maxOperandWidth_le _ _
    (acceptedCandidates_size_le slots)

/-- The complete recovery emits at most a quadratic number of arithmetic
events in the public phase-register width. -/
lemma multiplicativeOrderRecoveryTrace_arithmetic_length_le
    (modulus base phaseBits : Nat)
    (numerator : Fin (2 ^ phaseBits)) :
    (multiplicativeOrderRecoveryTrace
      modulus base phaseBits numerator).arithmetic.length ≤
        43 * (phaseBits + 1) ^ 2 := by
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let candidates := continuedFraction.denominators
  let slots :=
    candidates.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  let values :=
    slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits)
  have hcontinuedFraction :
      continuedFraction.arithmetic.length ≤
        17 * (phaseBits + 1) ^ 2 := by
    simpa [continuedFraction] using
      RationalContinuedFraction.dyadicContinuedFractionTrace_arithmetic_length_le
        numerator
  have hcandidates :
      candidates.length =
        RationalContinuedFraction.dyadicFuel phaseBits := by
    simpa [candidates, continuedFraction] using
      RationalContinuedFraction.dyadicContinuedFractionTrace_denominators_length
        numerator
  have hslots :
      (slots.flatMap
        (MultiplicativeOrderSlotTrace.arithmetic phaseBits)).length =
          RationalContinuedFraction.dyadicFuel phaseBits *
            (7 * (phaseBits + 1) + 5) := by
    rw [show slots =
      candidates.map
        (multiplicativeOrderSlotTrace modulus base phaseBits) by rfl,
      multiplicativeOrderSlots_arithmetic_length, hcandidates]
  have hselection :
      (leastAcceptedTrace values).arithmetic.length ≤
        RationalContinuedFraction.dyadicFuel phaseBits := by
    calc
      (leastAcceptedTrace values).arithmetic.length ≤ values.length :=
        leastAcceptedTrace_arithmetic_length_le values
      _ = slots.length := by simp [values]
      _ = candidates.length := by simp [slots]
      _ = RationalContinuedFraction.dyadicFuel phaseBits := hcandidates
  change
    (continuedFraction.arithmetic ++
      slots.flatMap
        (MultiplicativeOrderSlotTrace.arithmetic phaseBits) ++
      (leastAcceptedTrace values).arithmetic).length ≤
        43 * (phaseBits + 1) ^ 2
  simp only [List.length_append]
  calc
    continuedFraction.arithmetic.length +
          (slots.flatMap
            (MultiplicativeOrderSlotTrace.arithmetic phaseBits)).length +
        (leastAcceptedTrace values).arithmetic.length ≤
      17 * (phaseBits + 1) ^ 2 +
          (RationalContinuedFraction.dyadicFuel phaseBits *
            (7 * (phaseBits + 1) + 5)) +
        RationalContinuedFraction.dyadicFuel phaseBits :=
      Nat.add_le_add
        (Nat.add_le_add hcontinuedFraction hslots.le)
        hselection
    _ ≤ 43 * (phaseBits + 1) ^ 2 := by
      simp only [RationalContinuedFraction.dyadicFuel]
      nlinarith

/-- Every operand evaluated by the complete sealed recovery fits a linear
binary-width envelope derived from the public modulus, base representative,
and phase register. -/
lemma multiplicativeOrderRecoveryTrace_maxOperandWidth_le
    (modulus base phaseBits : Nat)
    (numerator : Fin (2 ^ phaseBits)) (hmodulus : 0 < modulus) :
    arithmeticEventListMaxOperandWidth
        (multiplicativeOrderRecoveryTrace
          modulus base phaseBits numerator).arithmetic ≤
      2 * (Nat.size modulus + Nat.size base + phaseBits + 2) := by
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let candidates := continuedFraction.denominators
  let slots :=
    candidates.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  let values :=
    slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits)
  let envelope := Nat.size modulus + Nat.size base + phaseBits + 2
  have hcontinuedFraction :
      arithmeticEventListMaxOperandWidth continuedFraction.arithmetic ≤
        2 * envelope := by
    exact
      (RationalContinuedFraction.dyadicContinuedFractionTrace_maxOperandWidth_le
        numerator).trans (by dsimp [envelope]; omega)
  have hcandidates :
      ∀ candidate ∈ candidates, candidate ≤ 2 ^ phaseBits := by
    intro candidate hcandidate
    exact
      RationalContinuedFraction.dyadicContinuedFractionTrace_denominator_le
        numerator
          (by simpa [candidates, continuedFraction] using hcandidate)
  have hslots :
      arithmeticEventListMaxOperandWidth
          (slots.flatMap
            (MultiplicativeOrderSlotTrace.arithmetic phaseBits)) ≤
        2 * envelope := by
    simpa [slots, envelope] using
      multiplicativeOrderSlots_maxOperandWidth_le
        modulus base phaseBits candidates hmodulus hcandidates
  have hselection :
      arithmeticEventListMaxOperandWidth
          (leastAcceptedTrace values).arithmetic ≤
        2 * envelope := by
    exact
      (leastAcceptedTrace_maxOperandWidth_le _ _
        (acceptedCandidates_size_le slots)).trans
          (by dsimp [envelope]; omega)
  change
    arithmeticEventListMaxOperandWidth
        (continuedFraction.arithmetic ++
          slots.flatMap
            (MultiplicativeOrderSlotTrace.arithmetic phaseBits) ++
          (leastAcceptedTrace values).arithmetic) ≤
      2 * envelope
  simp only [arithmeticEventListMaxOperandWidth_append]
  exact max_le (max_le hcontinuedFraction hslots) hselection

/-- A slot accepts exactly a positive in-width denominator whose ordinary
natural modular power returns one. -/
lemma multiplicativeOrderSlotTrace_accepts_iff
    (modulus base phaseBits candidate : Nat) :
    (multiplicativeOrderSlotTrace
        modulus base phaseBits candidate).Accepts phaseBits ↔
      candidate < 2 ^ (phaseBits + 1) ∧
        0 < candidate ∧ base ^ candidate ≡ 1 [MOD modulus] := by
  constructor
  · intro haccepts
    change
      candidate < 2 ^ (phaseBits + 1) ∧
        0 < candidate ∧
          (modularPowerTrace (phaseBits + 1)
            (base : ZMod modulus)
              (boundedRecoveryExponent phaseBits candidate)).value = 1
        at haccepts
    refine ⟨haccepts.1, haccepts.2.1, ?_⟩
    have hpower :
        (base : ZMod modulus) ^ candidate = 1 :=
      (by
        rw [← modularPowerTrace_value
          (base : ZMod modulus) haccepts.1]
        simpa [boundedRecoveryExponent, haccepts.1] using haccepts.2.2)
    have hzmod :
        ((base ^ candidate : Nat) : ZMod modulus) =
          ((1 : Nat) : ZMod modulus) := by
      simpa only [Nat.cast_pow, Nat.cast_one] using hpower
    exact
      (ZMod.natCast_eq_natCast_iff
        (base ^ candidate) 1 modulus).mp hzmod
  · rintro ⟨hfit, hpositive, hreturn⟩
    have hzmod :
        ((base ^ candidate : Nat) : ZMod modulus) =
          ((1 : Nat) : ZMod modulus) :=
      (ZMod.natCast_eq_natCast_iff
        (base ^ candidate) 1 modulus).mpr hreturn
    change
      candidate < 2 ^ (phaseBits + 1) ∧
        0 < candidate ∧
          (modularPowerTrace (phaseBits + 1)
            (base : ZMod modulus)
              (boundedRecoveryExponent phaseBits candidate)).value = 1
    refine ⟨hfit, hpositive, ?_⟩
    rw [modularPowerTrace_value (base : ZMod modulus)
      (boundedRecoveryExponent_lt phaseBits candidate)]
    rw [boundedRecoveryExponent, if_pos hfit]
    simpa using hzmod

/-- A returned candidate came from an actually visited denominator slot and
passed that slot's modular-power execution. -/
lemma multiplicativeOrderRecoveryTrace_output_some_sound
    {modulus base phaseBits candidate : Nat}
    {numerator : Fin (2 ^ phaseBits)}
    (hresult :
      (multiplicativeOrderRecoveryTrace
        modulus base phaseBits numerator).output = some candidate) :
    candidate ∈
        (RationalContinuedFraction.dyadicContinuedFractionTrace
          numerator).denominators ∧
      candidate < 2 ^ (phaseBits + 1) ∧
      0 < candidate ∧ base ^ candidate ≡ 1 [MOD modulus] := by
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let denominators := continuedFraction.denominators
  let slots :=
    denominators.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  let acceptedOptions :=
    slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits)
  have hselection :
      (leastAcceptedTrace acceptedOptions).output = some candidate := by
    simpa [MultiplicativeOrderRecoveryTrace.output,
      multiplicativeOrderRecoveryTrace, continuedFraction,
      denominators, slots, acceptedOptions] using hresult
  rw [leastAcceptedTrace_output] at hselection
  have hargmin :
      candidate ∈ List.argmin id (acceptedOptions.filterMap id) := by
    rw [hselection]
    simp
  have hmember :
      candidate ∈ acceptedOptions.filterMap id :=
    List.argmin_mem hargmin
  rcases List.mem_filterMap.mp hmember with
    ⟨accepted, hacceptedOption, hacceptedCandidate⟩
  rcases List.mem_map.mp hacceptedOption with
    ⟨slot, hslot, hslotAccepted⟩
  subst accepted
  unfold MultiplicativeOrderSlotTrace.accepted at hacceptedCandidate
  split at hacceptedCandidate
  next haccepts =>
    have hcand : slot.candidate = candidate := by
      simpa using hacceptedCandidate
    rcases List.mem_map.mp hslot with
      ⟨sourceCandidate, hsource, hsourceSlot⟩
    subst slot
    change sourceCandidate = candidate at hcand
    have hsourceEq : sourceCandidate = candidate := hcand
    subst sourceCandidate
    exact ⟨hsource,
      (multiplicativeOrderSlotTrace_accepts_iff
        modulus base phaseBits candidate).mp haccepts⟩
  next =>
    simp at hacceptedCandidate

/-- If a positive in-width denominator occurs in the actual schedule, returns
one, and is globally least among positive modular returns, the recovery output
is exactly that denominator. -/
lemma multiplicativeOrderRecoveryTrace_output_eq_some
    {modulus base phaseBits order : Nat}
    {numerator : Fin (2 ^ phaseBits)}
    (hmember :
      order ∈
        (RationalContinuedFraction.dyadicContinuedFractionTrace
          numerator).denominators)
    (hfit : order < 2 ^ (phaseBits + 1))
    (hpositive : 0 < order)
    (hreturn : base ^ order ≡ 1 [MOD modulus])
    (hminimal :
      ∀ candidate, 0 < candidate →
        base ^ candidate ≡ 1 [MOD modulus] → order ≤ candidate) :
    (multiplicativeOrderRecoveryTrace
      modulus base phaseBits numerator).output = some order := by
  let continuedFraction :=
    RationalContinuedFraction.dyadicContinuedFractionTrace numerator
  let denominators := continuedFraction.denominators
  let slots :=
    denominators.map
      (multiplicativeOrderSlotTrace modulus base phaseBits)
  let acceptedOptions :=
    slots.map (MultiplicativeOrderSlotTrace.accepted phaseBits)
  let accepted := acceptedOptions.filterMap id
  have haccepts :
      (multiplicativeOrderSlotTrace
        modulus base phaseBits order).Accepts phaseBits :=
    (multiplicativeOrderSlotTrace_accepts_iff
      modulus base phaseBits order).mpr
        ⟨hfit, hpositive, hreturn⟩
  have haccepted : order ∈ accepted := by
    apply List.mem_filterMap.mpr
    refine ⟨some order, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨multiplicativeOrderSlotTrace
      modulus base phaseBits order, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨order, hmember, rfl⟩
    · change
        (if (multiplicativeOrderSlotTrace
            modulus base phaseBits order).Accepts phaseBits then
          some order
        else none) = some order
      simp [haccepts]
  have hleast :
      ∀ candidate ∈ accepted, order ≤ candidate := by
    intro candidate hcandidate
    rcases List.mem_filterMap.mp hcandidate with
      ⟨acceptedCandidate, hacceptedCandidate, hcandidateEq⟩
    rcases List.mem_map.mp hacceptedCandidate with
      ⟨slot, hslot, hslotAccepted⟩
    subst acceptedCandidate
    unfold MultiplicativeOrderSlotTrace.accepted at hcandidateEq
    split at hcandidateEq
    next hslotAccepts =>
      have hslotEq : slot.candidate = candidate := by
        simpa using hcandidateEq
      rcases List.mem_map.mp hslot with
        ⟨sourceCandidate, _hsource, hsourceSlot⟩
      subst slot
      change sourceCandidate = candidate at hslotEq
      subst sourceCandidate
      have hvalid :=
        (multiplicativeOrderSlotTrace_accepts_iff
          modulus base phaseBits candidate).mp hslotAccepts
      exact hminimal candidate hvalid.2.1 hvalid.2.2
    next =>
      simp at hcandidateEq
  change
    (leastAcceptedTrace acceptedOptions).output = some order
  rw [leastAcceptedTrace_output]
  apply List.argmin_eq_some_iff.mpr
  refine ⟨haccepted, hleast, ?_⟩
  intro candidate hcandidate hcandidateLe
  have heq : candidate = order :=
    Nat.le_antisymm hcandidateLe (hleast candidate hcandidate)
  subst candidate
  exact Nat.le_refl _

/-- Operand-sensitive schoolbook charge of one sealed recovery. -/
def MultiplicativeOrderRecoveryTrace.schoolbookCharge
    {modulus phaseBits : Nat} {numerator : Fin (2 ^ phaseBits)}
    (trace : MultiplicativeOrderRecoveryTrace modulus numerator) : Nat :=
  arithmeticEventListCharge trace.arithmetic

/-- Complete executable order recovery has quartic schoolbook charge in the
combined public modulus, base-representative, and phase-register bit
envelope. -/
lemma multiplicativeOrderRecoveryTrace_schoolbookCharge_quartic
    (modulus base phaseBits : Nat)
    (numerator : Fin (2 ^ phaseBits)) (hmodulus : 0 < modulus) :
    (multiplicativeOrderRecoveryTrace
      modulus base phaseBits numerator).schoolbookCharge ≤
        2 ^ 11 *
          (Nat.size modulus + Nat.size base + phaseBits + 2) ^ 4 := by
  let trace :=
    multiplicativeOrderRecoveryTrace modulus base phaseBits numerator
  let envelope := Nat.size modulus + Nat.size base + phaseBits + 2
  have henvelopePos : 0 < envelope := by
    dsimp [envelope]
    omega
  have hphase : phaseBits + 1 ≤ envelope := by
    dsimp [envelope]
    omega
  have hlength : trace.arithmetic.length ≤ 43 * envelope ^ 2 := by
    calc
      trace.arithmetic.length ≤ 43 * (phaseBits + 1) ^ 2 := by
        simpa [trace] using
          multiplicativeOrderRecoveryTrace_arithmetic_length_le
            modulus base phaseBits numerator
      _ ≤ 43 * envelope ^ 2 :=
        Nat.mul_le_mul_left 43 (Nat.pow_le_pow_left hphase 2)
  have hwidth :
      arithmeticEventListMaxOperandWidth trace.arithmetic ≤
        2 * envelope := by
    simpa [trace, envelope] using
      multiplicativeOrderRecoveryTrace_maxOperandWidth_le
        modulus base phaseBits numerator hmodulus
  have hwidthSucc :
      arithmeticEventListMaxOperandWidth trace.arithmetic + 1 ≤
        3 * envelope := by
    have := Nat.add_le_add_right hwidth 1
    omega
  calc
    trace.schoolbookCharge =
        arithmeticEventListCharge trace.arithmetic := rfl
    _ ≤ 4 * trace.arithmetic.length *
          (arithmeticEventListMaxOperandWidth trace.arithmetic + 1) ^ 2 :=
      arithmeticEventListCharge_le trace.arithmetic
    _ ≤ 4 * (43 * envelope ^ 2) * (3 * envelope) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength)
        (Nat.pow_le_pow_left hwidthSucc 2)
    _ = 1548 * envelope ^ 4 := by ring
    _ ≤ 2 ^ 11 * envelope ^ 4 := by
      exact Nat.mul_le_mul_right (envelope ^ 4) (by norm_num)

/-- Executable finite regression: for the observed phase numerator `5/64`,
base two modulo fifteen validates denominator twelve.  The hidden true order
four is intentionally not substituted when it is absent from this observation's
continued-fraction candidates. -/
lemma multiplicativeOrderRecoveryTrace_fifteen_two_six_five :
    (multiplicativeOrderRecoveryTrace 15 2 6
      ⟨5, by norm_num⟩).output = some 12 := by
  unfold multiplicativeOrderRecoveryTrace
    MultiplicativeOrderRecoveryTrace.output
  let numerator : Fin (2 ^ 6) := ⟨5, by norm_num⟩
  change
    (leastAcceptedTrace
      (((RationalContinuedFraction.dyadicContinuedFractionTrace
        numerator).denominators.map
          (multiplicativeOrderSlotTrace 15 2 6)).map
            (MultiplicativeOrderSlotTrace.accepted 6))).output =
      some 12
  have hdenominators :
      (RationalContinuedFraction.dyadicContinuedFractionTrace
        numerator).denominators =
        [1, 12, 13, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64] := by
    simpa [numerator] using
      RationalContinuedFraction.dyadicContinuedFractionTrace_five_of_six_denominators
  rw [hdenominators]
  norm_num [MultiplicativeOrderSlotTrace.accepted,
    multiplicativeOrderSlotTrace_accepts_iff, leastAcceptedTrace,
    retainLeastOption, retainLeast, List.argAux]
  decide

end NumberTheory
end QuantumAlg

end

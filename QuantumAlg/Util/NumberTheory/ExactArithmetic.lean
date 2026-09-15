/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.BitComplexity
import Mathlib.Data.Nat.Sqrt
import Lean.Elab.Tactic.Omega
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Sealed traces for exact elementary number theory

These traces connect values used by deterministic post-processing to the
operand-sensitive arithmetic events produced by the same closed execution.
No constructor accepts a claimed width or cost.  The charge is a projection
of the internally generated event list.
-/

section

namespace QuantumAlg
namespace NumberTheory

section ModularPower

/-- Internal state of the fixed-width right-to-left binary-power scan. -/
private structure ModularPowerState (modulus : Nat) where
  accumulator : ZMod modulus
  power : ZMod modulus
  remaining : Nat
  arithmetic : List ArithmeticEvent

/-- One fixed-work binary-power slot.  Multiplication and reduction of both
the selected product and the next square are evaluated on every slot; the
current exponent bit only selects the already-computed accumulator value. -/
private def modularPowerStep {modulus : Nat}
    (state : ModularPowerState modulus) : ModularPowerState modulus :=
  let bit := state.remaining % 2
  let product := state.accumulator * state.power
  let square := state.power * state.power
  { accumulator := if bit = 1 then product else state.accumulator
    power := square
    remaining := state.remaining / 2
    arithmetic := state.arithmetic ++
      [ .natMod state.remaining 2
      , .natEq bit 1
      , .natMul state.accumulator.val state.power.val
      , .natMod (state.accumulator.val * state.power.val) modulus
      , .natMul state.power.val state.power.val
      , .natMod (state.power.val * state.power.val) modulus
      , .natDiv state.remaining 2 ] }

/-- Execute exactly `width` binary-power slots. -/
private def modularPowerRun {modulus : Nat} :
    Nat → ModularPowerState modulus → ModularPowerState modulus
  | 0, state => state
  | width + 1, state => modularPowerRun width (modularPowerStep state)

/-- A fixed-width modular-power result and the exact arithmetic events emitted
by its binary scan.  The private constructor prevents attaching a fabricated
event list to an unrelated group element. -/
structure ModularPowerTrace (modulus : Nat) where
  private mk ::
  /-- Arithmetic emitted by the fixed-width scan. -/
  arithmetic : List ArithmeticEvent
  /-- Group element computed by that scan. -/
  value : ZMod modulus

/-- Execute a fixed-width modular exponentiation.  Correct callers prove the
exponent fits in `width` bits; the scan itself always visits all slots. -/
def modularPowerTrace {modulus : Nat} (width : Nat)
    (base : ZMod modulus) (exponent : Nat) : ModularPowerTrace modulus :=
  let final := modularPowerRun width
    { accumulator := 1
      power := base
      remaining := exponent
      arithmetic := [] }
  .mk final.arithmetic final.accumulator

/-- The binary slot preserves `accumulator * power^remaining`. -/
private theorem modularPowerStep_invariant {modulus exponent : Nat}
    (base : ZMod modulus) (state : ModularPowerState modulus)
    (hstate : state.accumulator * state.power ^ state.remaining =
      base ^ exponent) :
    (modularPowerStep state).accumulator *
        (modularPowerStep state).power ^
          (modularPowerStep state).remaining =
      base ^ exponent := by
  have hmodLt : state.remaining % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdecomp := Nat.mod_add_div state.remaining 2
  by_cases hbit : state.remaining % 2 = 1
  · have hremaining :
        state.remaining = 2 * (state.remaining / 2) + 1 := by omega
    change
      (if state.remaining % 2 = 1 then
          state.accumulator * state.power
        else state.accumulator) *
        (state.power * state.power) ^ (state.remaining / 2) =
      base ^ exponent
    rw [if_pos hbit]
    calc
      (state.accumulator * state.power) *
          (state.power * state.power) ^ (state.remaining / 2) =
        (state.accumulator * state.power) *
          state.power ^ (2 * (state.remaining / 2)) := by
            rw [← pow_two, pow_mul]
      _ = state.accumulator *
          state.power ^ (2 * (state.remaining / 2) + 1) := by
            rw [pow_add, pow_one]
            ring
      _ = state.accumulator * state.power ^ state.remaining := by
            rw [← hremaining]
      _ = base ^ exponent := hstate
  · have hzero : state.remaining % 2 = 0 := by omega
    have hremaining : state.remaining = 2 * (state.remaining / 2) := by omega
    change
      (if state.remaining % 2 = 1 then
          state.accumulator * state.power
        else state.accumulator) *
        (state.power * state.power) ^ (state.remaining / 2) =
      base ^ exponent
    rw [if_neg hbit]
    calc
      state.accumulator *
          (state.power * state.power) ^ (state.remaining / 2) =
        state.accumulator * state.power ^ (2 * (state.remaining / 2)) := by
            rw [← pow_two, pow_mul]
      _ = state.accumulator * state.power ^ state.remaining := by
            rw [← hremaining]
      _ = base ^ exponent := hstate

/-- Every fixed-width run preserves the binary-power invariant. -/
private theorem modularPowerRun_invariant {modulus exponent : Nat}
    (base : ZMod modulus) (width : Nat) (state : ModularPowerState modulus)
    (hstate : state.accumulator * state.power ^ state.remaining =
      base ^ exponent) :
    (modularPowerRun width state).accumulator *
        (modularPowerRun width state).power ^
          (modularPowerRun width state).remaining =
      base ^ exponent := by
  induction width generalizing state with
  | zero => simpa [modularPowerRun] using hstate
  | succ width ih =>
      simp only [modularPowerRun]
      exact ih (modularPowerStep state)
        (modularPowerStep_invariant base state hstate)

/-- After enough binary slots the remaining exponent is zero. -/
private theorem modularPowerRun_remaining_eq_zero_of_lt {modulus width : Nat}
    (state : ModularPowerState modulus)
    (hfit : state.remaining < 2 ^ width) :
    (modularPowerRun width state).remaining = 0 := by
  induction width generalizing state with
  | zero =>
      have hzero : state.remaining = 0 := by simpa using hfit
      simp [modularPowerRun, hzero]
  | succ width ih =>
      simp only [modularPowerRun]
      apply ih
      simp only [modularPowerStep]
      rw [pow_succ] at hfit
      omega

/-- The fixed-width trace computes the ordinary group power whenever the
exponent fits in the scanned bit width. -/
theorem modularPowerTrace_value {modulus width exponent : Nat}
    (base : ZMod modulus) (hfit : exponent < 2 ^ width) :
    (modularPowerTrace width base exponent).value = base ^ exponent := by
  let initial : ModularPowerState modulus :=
    { accumulator := 1
      power := base
      remaining := exponent
      arithmetic := [] }
  have hinvariant := modularPowerRun_invariant (exponent := exponent)
    base width initial (by simp [initial])
  have hzero := modularPowerRun_remaining_eq_zero_of_lt initial hfit
  change (modularPowerRun width initial).accumulator = base ^ exponent
  rw [hzero] at hinvariant
  simpa using hinvariant

/-- A fixed-width modular-power run appends exactly seven events per scanned
bit. -/
private theorem modularPowerRun_arithmetic_length {modulus : Nat}
    (width : Nat) (state : ModularPowerState modulus) :
    (modularPowerRun width state).arithmetic.length =
      state.arithmetic.length + 7 * width := by
  induction width generalizing state with
  | zero => simp [modularPowerRun]
  | succ width ih =>
      rw [modularPowerRun, ih]
      simp [modularPowerStep]
      ring

/-- The exact modular-power event list has seven entries per scanned bit. -/
theorem modularPowerTrace_arithmetic_length {modulus width : Nat}
    (base : ZMod modulus) (exponent : Nat) :
    (modularPowerTrace width base exponent).arithmetic.length =
      7 * width := by
  simpa [modularPowerTrace] using
    modularPowerRun_arithmetic_length width
      ({ accumulator := 1
         power := base
         remaining := exponent
         arithmetic := [] } : ModularPowerState modulus)

/-- One modular-power slot stays within a uniform public input-width
envelope. -/
private theorem modularPowerSlot_maxOperandWidth_le {modulus : Nat}
    [NeZero modulus] (root : Nat) (state : ModularPowerState modulus)
    (hremaining : Nat.size state.remaining ≤ root) :
    arithmeticEventListMaxOperandWidth
        [ .natMod state.remaining 2
        , .natEq (state.remaining % 2) 1
        , .natMul state.accumulator.val state.power.val
        , .natMod (state.accumulator.val * state.power.val) modulus
        , .natMul state.power.val state.power.val
        , .natMod (state.power.val * state.power.val) modulus
        , .natDiv state.remaining 2 ] ≤
      2 * (Nat.size modulus + root + 1) := by
  let bound := 2 * (Nat.size modulus + root + 1)
  have hmodulus : 0 < modulus := NeZero.pos modulus
  have hmodulusSize : 1 ≤ Nat.size modulus := Nat.size_pos.2 hmodulus
  have hconstOne : Nat.size 1 ≤ bound := by
    rw [Nat.size_one]
    dsimp [bound]
    omega
  have hconstTwo : Nat.size 2 ≤ bound := by
    have hsizeTwo : Nat.size 2 = 2 := by decide
    rw [hsizeTwo]
    dsimp [bound]
    omega
  have hremainingBound : Nat.size state.remaining ≤ bound := by
    exact hremaining.trans (by dsimp [bound]; omega)
  have hbitLe : state.remaining % 2 ≤ 1 := by
    have hbitLt := Nat.mod_lt state.remaining (by decide : 0 < 2)
    omega
  have hbitSize : Nat.size (state.remaining % 2) ≤ bound := by
    exact (Nat.size_le_size hbitLe).trans
      (by simpa using hconstOne)
  have haccumulatorSize : Nat.size state.accumulator.val ≤ bound := by
    calc
      Nat.size state.accumulator.val ≤ Nat.size modulus :=
        Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.accumulator))
      _ ≤ bound := by dsimp [bound]; omega
  have hpowerSize : Nat.size state.power.val ≤ bound := by
    calc
      Nat.size state.power.val ≤ Nat.size modulus :=
        Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.power))
      _ ≤ bound := by dsimp [bound]; omega
  have hproductSize :
      Nat.size (state.accumulator.val * state.power.val) ≤ bound := by
    calc
      Nat.size (state.accumulator.val * state.power.val) ≤
          Nat.size state.accumulator.val + Nat.size state.power.val :=
        natSize_mul_le_add _ _
      _ ≤ Nat.size modulus + Nat.size modulus :=
        Nat.add_le_add
          (Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.accumulator)))
          (Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.power)))
      _ ≤ bound := by dsimp [bound]; omega
  have hsquareSize :
      Nat.size (state.power.val * state.power.val) ≤ bound := by
    calc
      Nat.size (state.power.val * state.power.val) ≤
          Nat.size state.power.val + Nat.size state.power.val :=
        natSize_mul_le_add _ _
      _ ≤ Nat.size modulus + Nat.size modulus :=
        Nat.add_le_add
          (Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.power)))
          (Nat.size_le_size (Nat.le_of_lt (ZMod.val_lt state.power)))
      _ ≤ bound := by dsimp [bound]; omega
  have hmodulusBound : Nat.size modulus ≤ bound := by
    dsimp [bound]
    omega
  apply arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
  rcases hevent with hremMod | hbitEq | hproduct | hproductMod |
      hsquare | hsquareMod | hremDiv
  · subst event
    exact max_le hremainingBound hconstTwo
  · subst event
    exact max_le hbitSize hconstOne
  · subst event
    exact max_le haccumulatorSize hpowerSize
  · subst event
    exact max_le hproductSize hmodulusBound
  · subst event
    exact max_le hpowerSize hpowerSize
  · subst event
    exact max_le hsquareSize hmodulusBound
  · subst event
    exact max_le hremainingBound hconstTwo

/-- A complete fixed-width run preserves the public max-operand envelope. -/
private theorem modularPowerRun_maxOperandWidth_le {modulus : Nat}
    [NeZero modulus] (root width : Nat) (state : ModularPowerState modulus)
    (hwidth : width ≤ root) (hfit : state.remaining < 2 ^ width)
    (hprior : arithmeticEventListMaxOperandWidth state.arithmetic ≤
      2 * (Nat.size modulus + root + 1)) :
    arithmeticEventListMaxOperandWidth
        (modularPowerRun width state).arithmetic ≤
      2 * (Nat.size modulus + root + 1) := by
  induction width generalizing state with
  | zero => simpa [modularPowerRun] using hprior
  | succ width ih =>
      have hremaining : Nat.size state.remaining ≤ root :=
        (Nat.size_le.2 hfit).trans hwidth
      have hslot := modularPowerSlot_maxOperandWidth_le root state hremaining
      have hnextPrior :
          arithmeticEventListMaxOperandWidth
              (modularPowerStep state).arithmetic ≤
            2 * (Nat.size modulus + root + 1) := by
        rw [show (modularPowerStep state).arithmetic =
          state.arithmetic ++
            [ .natMod state.remaining 2
            , .natEq (state.remaining % 2) 1
            , .natMul state.accumulator.val state.power.val
            , .natMod (state.accumulator.val * state.power.val) modulus
            , .natMul state.power.val state.power.val
            , .natMod (state.power.val * state.power.val) modulus
            , .natDiv state.remaining 2 ] by rfl,
          arithmeticEventListMaxOperandWidth_append]
        exact max_le hprior hslot
      have hnextFit :
          (modularPowerStep state).remaining < 2 ^ width := by
        simp only [modularPowerStep]
        rw [pow_succ] at hfit
        omega
      simpa [modularPowerRun] using
        ih (modularPowerStep state) (by omega) hnextFit hnextPrior

/-- Positive-modulus fixed-width modular power has a uniform max-operand
bound derived only from the modulus and scan width. -/
theorem modularPowerTrace_maxOperandWidth_le
    {modulus width exponent : Nat} (base : ZMod modulus)
    (hmodulus : 0 < modulus) (hfit : exponent < 2 ^ width) :
    arithmeticEventListMaxOperandWidth
        (modularPowerTrace width base exponent).arithmetic ≤
      2 * (Nat.size modulus + width + 1) := by
  let _ : NeZero modulus := ⟨Nat.ne_of_gt hmodulus⟩
  let initial : ModularPowerState modulus :=
    { accumulator := 1
      power := base
      remaining := exponent
      arithmetic := [] }
  change arithmeticEventListMaxOperandWidth
      (modularPowerRun width initial).arithmetic ≤
    2 * (Nat.size modulus + width + 1)
  exact modularPowerRun_maxOperandWidth_le width width initial
    (by rfl) hfit (by simp [initial, arithmeticEventListMaxOperandWidth])

/-- Exact schoolbook charge projected from the sealed modular-power trace. -/
def ModularPowerTrace.schoolbookCharge {modulus : Nat}
    (trace : ModularPowerTrace modulus) : Nat :=
  arithmeticEventListCharge trace.arithmetic

/-- Positive-modulus fixed-width modular power has cubic schoolbook arithmetic
charge in the combined public modulus and exponent-width envelope. -/
theorem modularPowerTrace_schoolbookCharge_cubic
    {modulus width exponent : Nat} (base : ZMod modulus)
    (hmodulus : 0 < modulus) (hfit : exponent < 2 ^ width) :
    (modularPowerTrace width base exponent).schoolbookCharge ≤
      252 * (Nat.size modulus + width + 1) ^ 3 := by
  let envelope := Nat.size modulus + width + 1
  have hwidth := modularPowerTrace_maxOperandWidth_le base hmodulus hfit
  have hlength := modularPowerTrace_arithmetic_length
    (width := width) base exponent
  have henvelopePos : 0 < envelope := by dsimp [envelope]; omega
  have hscan : width ≤ envelope := by dsimp [envelope]; omega
  have hopen : 2 * envelope + 1 ≤ 3 * envelope := by omega
  have hsquare : (2 * envelope + 1) ^ 2 ≤ (3 * envelope) ^ 2 :=
    Nat.pow_le_pow_left hopen 2
  calc
    (modularPowerTrace width base exponent).schoolbookCharge =
        arithmeticEventListCharge
          (modularPowerTrace width base exponent).arithmetic := rfl
    _ ≤ 4 * (modularPowerTrace width base exponent).arithmetic.length *
          (arithmeticEventListMaxOperandWidth
            (modularPowerTrace width base exponent).arithmetic + 1) ^ 2 :=
      arithmeticEventListCharge_le _
    _ ≤ 4 * (7 * width) * (2 * envelope + 1) ^ 2 := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength.le)
        (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2)
    _ ≤ 4 * (7 * envelope) * (3 * envelope) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4
        (Nat.mul_le_mul_left 7 hscan)) hsquare
    _ = 252 * (Nat.size modulus + width + 1) ^ 3 := by
      dsimp [envelope]
      ring

end ModularPower

section EuclideanGCD

/-- Internal result of the ordinary Euclidean gcd recursion. -/
private structure EuclideanGCDState where
  value : Nat
  arithmetic : List ArithmeticEvent

/-- Execute the same remainder recursion as `Nat.gcd`, retaining both each
zero test and each evaluated remainder operation. -/
private def euclideanGCDRun : Nat → Nat → EuclideanGCDState
  | 0, right =>
      { value := right
        arithmetic := [.natEq 0 0] }
  | left + 1, right =>
      let remainder := right % (left + 1)
      let final := euclideanGCDRun remainder (left + 1)
      { value := final.value
        arithmetic :=
          [ .natEq (left + 1) 0
          , .natMod right (left + 1) ] ++ final.arithmetic }
termination_by left _ => left
decreasing_by exact Nat.mod_lt right (Nat.succ_pos left)

/-- The traced remainder recursion computes `Nat.gcd`. -/
private theorem euclideanGCDRun_value (left right : Nat) :
    (euclideanGCDRun left right).value = Nat.gcd left right := by
  induction left using Nat.strong_induction_on generalizing right with
  | h left ih =>
      cases left with
      | zero => simp [euclideanGCDRun]
      | succ left =>
          rw [euclideanGCDRun, Nat.gcd_succ]
          exact ih (right % (left + 1))
            (Nat.mod_lt right (Nat.succ_pos left)) (left + 1)

/-- A gcd value paired with the Euclidean remainder trace generated from the
same operands. -/
structure EuclideanGCDTrace where
  private mk ::
  /-- Euclidean remainder events. -/
  arithmetic : List ArithmeticEvent
  /-- Exact gcd of the original operands. -/
  value : Nat

/-- Execute the ordinary Euclidean gcd trace. -/
def euclideanGCDTrace (left right : Nat) : EuclideanGCDTrace :=
  let final := euclideanGCDRun left right
  .mk final.arithmetic final.value

/-- The sealed Euclidean trace returns `Nat.gcd`. -/
theorem euclideanGCDTrace_value (left right : Nat) :
    (euclideanGCDTrace left right).value = Nat.gcd left right := by
  exact euclideanGCDRun_value left right

/-- Exact schoolbook charge projected from the sealed gcd trace. -/
def EuclideanGCDTrace.schoolbookCharge (trace : EuclideanGCDTrace) : Nat :=
  arithmeticEventListCharge trace.arithmetic

private theorem euclideanGCDRun_arithmetic_length_of_pos
    (left right : Nat) (hleft : 0 < left) :
    (euclideanGCDRun left right).arithmetic.length =
      2 + (euclideanGCDRun (right % left) left).arithmetic.length := by
  obtain ⟨left, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hleft)
  simp only [euclideanGCDRun, List.length_append, List.length_cons,
    List.length_nil]

/-- Two nonterminal Euclidean remainder steps reduce the first operand by
more than a factor of two. -/
private theorem secondEuclideanRemainder_double_lt
    (left right : Nat) (hleft : 0 < left)
    (hremainder : 0 < right % left) :
    2 * (left % (right % left)) < left := by
  have hremainderLt : right % left < left := Nat.mod_lt _ hleft
  by_cases hsmall : 2 * (right % left) ≤ left
  · have hnext := Nat.mod_lt left hremainder
    omega
  · have hremainderLe : right % left ≤ left :=
      Nat.le_of_lt hremainderLt
    have hsub : left - (right % left) < right % left := by omega
    rw [Nat.mod_eq_sub_mod hremainderLe, Nat.mod_eq_of_lt hsub]
    omega

/-- The binary width of the first Euclidean operand decreases after two
nonterminal steps. -/
private theorem secondEuclideanRemainder_size_succ_le
    (left right : Nat) (hleft : 0 < left)
    (hremainder : 0 < right % left) :
    Nat.size (left % (right % left)) + 1 ≤ Nat.size left := by
  let next := left % (right % left)
  change Nat.size next + 1 ≤ Nat.size left
  have hdouble :
      2 * next < left := by
    simpa [next] using
      secondEuclideanRemainder_double_lt left right hleft hremainder
  by_cases hnext : next = 0
  · have hsizePos : 0 < Nat.size left := Nat.size_pos.2 hleft
    rw [hnext, Nat.size_zero]
    omega
  · have hshift : 2 * next = next <<< 1 := by
      simp [Nat.shiftLeft_eq_mul_pow, Nat.mul_comm]
    have hdoubleSize : Nat.size (2 * next) = Nat.size next + 1 := by
      rw [hshift, Nat.size_shiftLeft hnext]
    have hmono :=
      Nat.size_le_size (Nat.le_of_lt hdouble)
    rw [hdoubleSize] at hmono
    exact hmono

private theorem euclideanGCDRun_arithmetic_length_le
    (left right : Nat) :
    (euclideanGCDRun left right).arithmetic.length ≤
      4 * Nat.size left + 1 := by
  induction left using Nat.strong_induction_on generalizing right with
  | h left ih =>
      by_cases hzero : left = 0
      · subst left
        simp [euclideanGCDRun]
      · have hleft : 0 < left := Nat.pos_of_ne_zero hzero
        rw [euclideanGCDRun_arithmetic_length_of_pos left right hleft]
        let remainder := right % left
        by_cases hremainderZero : remainder = 0
        · have hsizePos : 0 < Nat.size left := Nat.size_pos.2 hleft
          simp [remainder, hremainderZero, euclideanGCDRun]
          omega
        · have hremainder : 0 < remainder :=
            Nat.pos_of_ne_zero hremainderZero
          rw [euclideanGCDRun_arithmetic_length_of_pos
            remainder left hremainder]
          let next := left % remainder
          have hremainderLt : remainder < left := by
            simpa [remainder] using Nat.mod_lt right hleft
          have hnextLt : next < left :=
            (Nat.mod_lt left hremainder).trans hremainderLt
          have htail := ih next hnextLt remainder
          have hsize :
              Nat.size next + 1 ≤ Nat.size left := by
            simpa [next, remainder] using
              secondEuclideanRemainder_size_succ_le
                left right hleft (by simpa [remainder] using hremainder)
          change
            2 + (2 + (euclideanGCDRun next remainder).arithmetic.length) ≤
              4 * Nat.size left + 1
          omega

private theorem euclideanGCDRun_maxOperandWidth_le
    (left right bound : Nat)
    (hleft : Nat.size left ≤ bound) (hright : Nat.size right ≤ bound) :
    arithmeticEventListMaxOperandWidth
        (euclideanGCDRun left right).arithmetic ≤ bound := by
  induction left using Nat.strong_induction_on generalizing right with
  | h left ih =>
      cases left with
      | zero =>
          simp [euclideanGCDRun, ArithmeticEvent.operandWidth,
            arithmeticEventListMaxOperandWidth]
      | succ left =>
          have hpositive : 0 < left + 1 := Nat.succ_pos _
          have hremainderLt : right % (left + 1) < left + 1 :=
            Nat.mod_lt _ hpositive
          have hremainderSize : Nat.size (right % (left + 1)) ≤ bound :=
            (Nat.size_le_size (Nat.le_of_lt hremainderLt)).trans hleft
          have htail :=
            ih (right % (left + 1)) hremainderLt
              (left + 1) hremainderSize hleft
          have hequality :
              (ArithmeticEvent.natEq (left + 1) 0).operandWidth ≤ bound := by
            simpa [ArithmeticEvent.operandWidth] using hleft
          have hremainder :
              (ArithmeticEvent.natMod right (left + 1)).operandWidth ≤
                bound := by
            simpa [ArithmeticEvent.operandWidth] using max_le hright hleft
          simp only [euclideanGCDRun,
            arithmeticEventListMaxOperandWidth]
          exact max_le hequality (max_le hremainder htail)

/-- A Euclidean trace emits at most four events per input-width bit, plus its
terminal zero test. -/
theorem euclideanGCDTrace_arithmetic_length_le (left right : Nat) :
    (euclideanGCDTrace left right).arithmetic.length ≤
      4 * Nat.size left + 1 := by
  simpa [euclideanGCDTrace] using
    euclideanGCDRun_arithmetic_length_le left right

/-- Every Euclidean event operand stays within the initial binary-width
envelope. -/
theorem euclideanGCDTrace_maxOperandWidth_le (left right : Nat) :
    arithmeticEventListMaxOperandWidth
        (euclideanGCDTrace left right).arithmetic ≤
      max (Nat.size left) (Nat.size right) := by
  simpa [euclideanGCDTrace] using
    euclideanGCDRun_maxOperandWidth_le left right
      (max (Nat.size left) (Nat.size right))
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The complete sealed Euclidean execution has cubic schoolbook charge in
the larger input width. -/
theorem euclideanGCDTrace_schoolbookCharge_cubic (left right : Nat) :
    (euclideanGCDTrace left right).schoolbookCharge ≤
      16 * (max (Nat.size left) (Nat.size right) + 1) ^ 3 := by
  let width := max (Nat.size left) (Nat.size right)
  have hlength :
      (euclideanGCDTrace left right).arithmetic.length ≤
        4 * (width + 1) := by
    have hleft : Nat.size left ≤ width := Nat.le_max_left _ _
    have hraw := euclideanGCDTrace_arithmetic_length_le left right
    omega
  have hwidth :
      arithmeticEventListMaxOperandWidth
          (euclideanGCDTrace left right).arithmetic + 1 ≤ width + 1 :=
    Nat.add_le_add_right
      (by simpa [width] using
        euclideanGCDTrace_maxOperandWidth_le left right) 1
  calc
    (euclideanGCDTrace left right).schoolbookCharge ≤
        4 * (euclideanGCDTrace left right).arithmetic.length *
          (arithmeticEventListMaxOperandWidth
            (euclideanGCDTrace left right).arithmetic + 1) ^ 2 :=
      arithmeticEventListCharge_le _
    _ ≤ 4 * (4 * (width + 1)) * (width + 1) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 4 hlength)
        (Nat.pow_le_pow_left hwidth 2)
    _ = 16 * (width + 1) ^ 3 := by ring

end EuclideanGCD

section IntegerSquareRoot

/-- Internal result of one fixed-round square-root execution. -/
private structure IntegerSquareRootState where
  value : Nat
  arithmetic : List ArithmeticEvent

/-- Number of binary-refinement rounds needed for the floor square root of an
input with the given magnitude width. -/
def integerSquareRootRounds (value : Nat) : Nat :=
  (Nat.size value + 1) / 2

/-- Refine the lower endpoint of a certified square-root interval one binary
digit at a time.  At entry to a call with `remaining` rounds, the interval has
width `2 ^ remaining`; every call evaluates exactly one midpoint square. -/
private def integerSquareRootFixedRun
    (value : Nat) : Nat → Nat → IntegerSquareRootState
  | 0, low =>
      { value := low
        arithmetic := [] }
  | remaining + 1, low =>
      let half := 1 <<< remaining
      let mid := low + half
      let square := mid * mid
      let slot : List ArithmeticEvent :=
        [ .natShiftLeft 1 remaining
        , .natAdd low half
        , .natMul mid mid
        , .natLe square value ]
      let nextLow := if square ≤ value then mid else low
      let final := integerSquareRootFixedRun value remaining nextLow
      { value := final.value
        arithmetic := slot ++ final.arithmetic }

/-- Execute a fixed number of binary interval refinements derived only from
the public input width. -/
private def integerSquareRootRun (value : Nat) : IntegerSquareRootState :=
  let rounds := integerSquareRootRounds value
  let final := integerSquareRootFixedRun value rounds 0
  { value := final.value
    arithmetic :=
      [ .natLog2 value
      , .natAdd (Nat.size value) 1
      , .natDiv (Nat.size value + 1) 2 ] ++ final.arithmetic }

/-- One refinement preserves a bracketing interval and, after all rounds,
leaves the unique natural whose square is at most the input while its
successor's square is larger. -/
private theorem integerSquareRootFixedRun_bounds
    (value rounds low : Nat)
    (hlow : low * low ≤ value)
    (hhigh : value <
      (low + (1 <<< rounds)) * (low + (1 <<< rounds))) :
    (integerSquareRootFixedRun value rounds low).value *
        (integerSquareRootFixedRun value rounds low).value ≤ value ∧
      value <
        ((integerSquareRootFixedRun value rounds low).value + 1) *
          ((integerSquareRootFixedRun value rounds low).value + 1) := by
  induction rounds generalizing low with
  | zero =>
      simpa [integerSquareRootFixedRun, Nat.shiftLeft_eq] using
        And.intro hlow hhigh
  | succ rounds ih =>
      have hshift :
          1 <<< (rounds + 1) =
            (1 <<< rounds) + (1 <<< rounds) := by
        simp only [Nat.shiftLeft_eq, pow_succ]
        omega
      by_cases hsquare :
          (low + (1 <<< rounds)) * (low + (1 <<< rounds)) ≤ value
      · have hnextHigh :
            value <
              ((low + (1 <<< rounds)) + (1 <<< rounds)) *
                ((low + (1 <<< rounds)) + (1 <<< rounds)) := by
          simpa [hshift, Nat.add_assoc] using hhigh
        simpa [integerSquareRootFixedRun, hsquare] using
          ih (low + (1 <<< rounds)) hsquare hnextHigh
      · have hnextHigh :
            value < (low + (1 <<< rounds)) *
              (low + (1 <<< rounds)) :=
          Nat.lt_of_not_ge hsquare
        simpa [integerSquareRootFixedRun, hsquare] using
          ih low hlow hnextHigh

/-- The initial power-of-two interval contains the exact square root. -/
private theorem integerSquareRoot_lt_initial_square (value : Nat) :
    value <
      (1 <<< integerSquareRootRounds value) *
        (1 <<< integerSquareRootRounds value) := by
  have hwidth :
      Nat.size value ≤ 2 * integerSquareRootRounds value := by
    simp only [integerSquareRootRounds]
    omega
  calc
    value < 2 ^ Nat.size value := Nat.lt_size_self value
    _ ≤ 2 ^ (2 * integerSquareRootRounds value) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hwidth
    _ = (1 <<< integerSquareRootRounds value) *
        (1 <<< integerSquareRootRounds value) := by
      simp [Nat.shiftLeft_eq, pow_add, two_mul]

/-- The complete fixed-round execution returns `Nat.sqrt`. -/
private theorem integerSquareRootRun_value (value : Nat) :
    (integerSquareRootRun value).value = Nat.sqrt value := by
  apply Nat.eq_sqrt.2
  simpa [integerSquareRootRun] using
    integerSquareRootFixedRun_bounds value
      (integerSquareRootRounds value) 0 (by simp)
      (by simpa using integerSquareRoot_lt_initial_square value)

/-- Each binary refinement contributes exactly four operand-derived events. -/
private theorem integerSquareRootFixedRun_arithmetic_length
    (value rounds low : Nat) :
    (integerSquareRootFixedRun value rounds low).arithmetic.length =
      4 * rounds := by
  induction rounds generalizing low with
  | zero => simp [integerSquareRootFixedRun]
  | succ rounds ih =>
      simp [integerSquareRootFixedRun, ih, Nat.mul_succ]

/-- The number of square-root refinement rounds never exceeds the input's
binary magnitude width. -/
private theorem integerSquareRootRounds_le_size (value : Nat) :
    integerSquareRootRounds value ≤ Nat.size value := by
  simp only [integerSquareRootRounds]
  omega

/-- Every event in one refinement slot has width at most twice the public
input width.  The interval hypothesis ties `low` and the tested midpoint to
the original fixed power-of-two search interval. -/
private theorem integerSquareRootSlot_maxOperandWidth_le
    (value root remaining low : Nat)
    (hroot : root ≤ Nat.size value)
    (hremaining : remaining + 1 ≤ root)
    (hmid : low + (1 <<< remaining) ≤ 1 <<< root) :
    arithmeticEventListMaxOperandWidth
        [ .natShiftLeft 1 remaining
        , .natAdd low (1 <<< remaining)
        , .natMul (low + (1 <<< remaining))
            (low + (1 <<< remaining))
        , .natLe
            ((low + (1 <<< remaining)) *
              (low + (1 <<< remaining))) value ] ≤
      2 * (Nat.size value + 1) := by
  let half := 1 <<< remaining
  let mid := low + half
  let square := mid * mid
  let width := 2 * (Nat.size value + 1)
  have hremainingLe : remaining ≤ root := by omega
  have hremainingSize : Nat.size remaining ≤ width := by
    calc
      Nat.size remaining ≤ remaining :=
        Nat.size_le.2 remaining.lt_two_pow_self
      _ ≤ root := hremainingLe
      _ ≤ Nat.size value := hroot
      _ ≤ width := by omega
  have hhalfSizeEq : Nat.size half = remaining + 1 := by
    simp [half, Nat.add_comm]
  have hhalfSize : Nat.size half ≤ width := by
    rw [hhalfSizeEq]
    calc
      remaining + 1 ≤ root := hremaining
      _ ≤ Nat.size value := hroot
      _ ≤ width := by omega
  have hlowLe : low ≤ 1 <<< root := by
    exact le_trans (Nat.le_add_right low (1 <<< remaining)) hmid
  have hlowSize : Nat.size low ≤ width := by
    calc
      Nat.size low ≤ Nat.size (1 <<< root) := Nat.size_le_size hlowLe
      _ = root + 1 := by simp [Nat.add_comm]
      _ ≤ Nat.size value + 1 := Nat.add_le_add_right hroot 1
      _ ≤ width := by omega
  have hmidSizeSmall : Nat.size mid ≤ Nat.size value + 1 := by
    calc
      Nat.size mid ≤ Nat.size (1 <<< root) :=
        Nat.size_le_size (by simpa [mid, half] using hmid)
      _ = root + 1 := by simp [Nat.add_comm]
      _ ≤ Nat.size value + 1 := Nat.add_le_add_right hroot 1
  have hmidSize : Nat.size mid ≤ width := by
    exact hmidSizeSmall.trans (by omega)
  have hsquareSize : Nat.size square ≤ width := by
    calc
      Nat.size square ≤ Nat.size mid + Nat.size mid := by
        simpa [square] using natSize_mul_le_add mid mid
      _ ≤ (Nat.size value + 1) + (Nat.size value + 1) :=
        Nat.add_le_add hmidSizeSmall hmidSizeSmall
      _ = width := by simp [width, two_mul]
  have hvalueSize : Nat.size value ≤ width := by omega
  apply arithmeticEventListMaxOperandWidth_le
  intro event hevent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
  rcases hevent with hshift | hadd | hmul | hle
  · subst event
    exact max_le hremainingSize hhalfSize
  · subst event
    exact max_le hlowSize hhalfSize
  · subst event
    simpa [ArithmeticEvent.operandWidth, mid, half] using hmidSize
  · subst event
    exact max_le (by simpa [mid, square] using hsquareSize) hvalueSize

/-- Every event in a complete fixed-round refinement has width at most twice
the input width. -/
private theorem integerSquareRootFixedRun_maxOperandWidth_le
    (value root rounds low : Nat)
    (hroot : root ≤ Nat.size value)
    (hrounds : rounds ≤ root)
    (hinterval : low + (1 <<< rounds) ≤ 1 <<< root) :
    arithmeticEventListMaxOperandWidth
        (integerSquareRootFixedRun value rounds low).arithmetic ≤
      2 * (Nat.size value + 1) := by
  induction rounds generalizing low with
  | zero => simp [integerSquareRootFixedRun,
      arithmeticEventListMaxOperandWidth]
  | succ rounds ih =>
      have hshift :
          1 <<< (rounds + 1) =
            (1 <<< rounds) + (1 <<< rounds) := by
        simp only [Nat.shiftLeft_eq, pow_succ]
        omega
      have hendpoint :
          low + (1 <<< rounds) + (1 <<< rounds) ≤ 1 <<< root := by
        simpa [hshift, Nat.add_assoc] using hinterval
      have hmidBound : low + (1 <<< rounds) ≤ 1 <<< root :=
        (Nat.le_add_right (low + (1 <<< rounds)) (1 <<< rounds)).trans
          hendpoint
      have hslot := integerSquareRootSlot_maxOperandWidth_le
        value root rounds low hroot (by omega) hmidBound
      by_cases hsquare :
          (low + (1 <<< rounds)) * (low + (1 <<< rounds)) ≤ value
      · have hnextInterval :
            (low + (1 <<< rounds)) + (1 <<< rounds) ≤
              1 <<< root := hendpoint
        have htail := ih (low + (1 <<< rounds)) (by omega) hnextInterval
        simp only [integerSquareRootFixedRun, hsquare, if_pos,
          arithmeticEventListMaxOperandWidth_append]
        exact max_le hslot htail
      · have htail := ih low (by omega) hmidBound
        simp only [integerSquareRootFixedRun, hsquare,
          arithmeticEventListMaxOperandWidth_append]
        exact max_le hslot htail

/-- An exact integer square root paired with every arithmetic event emitted by
the same fixed-round binary refinement. -/
structure IntegerSquareRootTrace (input : Nat) where
  private mk ::
  /-- Arithmetic emitted by initialization and all binary-refinement slots. -/
  arithmetic : List ArithmeticEvent
  /-- Exact floor square root. -/
  value : Nat

/-- Execute one exact natural-number square root and seal its result together
with the events emitted by that execution. -/
def integerSquareRootTrace (value : Nat) : IntegerSquareRootTrace value :=
  let final := integerSquareRootRun value
  .mk final.arithmetic final.value

/-- The sealed square-root trace returns `Nat.sqrt`. -/
theorem integerSquareRootTrace_value (value : Nat) :
    (integerSquareRootTrace value).value = Nat.sqrt value := by
  exact integerSquareRootRun_value value

/-- Exact event count of the fixed-round square-root execution. -/
theorem integerSquareRootTrace_arithmetic_length (value : Nat) :
    (integerSquareRootTrace value).arithmetic.length =
      3 + 4 * integerSquareRootRounds value := by
  simp only [integerSquareRootTrace, integerSquareRootRun, List.length_append,
    List.length_cons, List.length_nil,
    integerSquareRootFixedRun_arithmetic_length]

/-- Every operand used by the sealed fixed-round square-root execution has at
most twice the public input width. -/
theorem integerSquareRootTrace_maxOperandWidth_le (value : Nat) :
    arithmeticEventListMaxOperandWidth
        (integerSquareRootTrace value).arithmetic ≤
      2 * (Nat.size value + 1) := by
  let width := 2 * (Nat.size value + 1)
  have hsizeSize : Nat.size (Nat.size value) ≤ width := by
    calc
      Nat.size (Nat.size value) ≤ Nat.size value :=
        Nat.size_le.2 (Nat.size value).lt_two_pow_self
      _ ≤ width := by omega
  have hvalueSize : Nat.size value ≤ width := by
    dsimp [width]
    omega
  have hsizeSucc : Nat.size (Nat.size value + 1) ≤ width := by
    calc
      Nat.size (Nat.size value + 1) ≤ Nat.size value + 1 :=
        Nat.size_le.2 (Nat.size value + 1).lt_two_pow_self
      _ ≤ width := by omega
  have honeSize : Nat.size 1 ≤ width := by
    rw [Nat.size_one]
    dsimp [width]
    omega
  have htwoSize : Nat.size 2 ≤ width := by
    have hsizeTwo : Nat.size 2 = 2 := by decide
    rw [hsizeTwo]
    dsimp [width]
    omega
  have hinit :
      arithmeticEventListMaxOperandWidth
          [ .natLog2 value
          , .natAdd (Nat.size value) 1
          , .natDiv (Nat.size value + 1) 2 ] ≤ width := by
    apply arithmeticEventListMaxOperandWidth_le
    intro event hevent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
    rcases hevent with hlog | hadd | hdiv
    · subst event
      exact hvalueSize
    · subst event
      exact max_le hsizeSize honeSize
    · subst event
      exact max_le hsizeSucc htwoSize
  have htail :
      arithmeticEventListMaxOperandWidth
          (integerSquareRootFixedRun value
            (integerSquareRootRounds value) 0).arithmetic ≤ width :=
    integerSquareRootFixedRun_maxOperandWidth_le value
      (integerSquareRootRounds value) (integerSquareRootRounds value) 0
      (integerSquareRootRounds_le_size value) (by rfl) (by simp)
  change arithmeticEventListMaxOperandWidth
      ([ .natLog2 value
       , .natAdd (Nat.size value) 1
       , .natDiv (Nat.size value + 1) 2 ] ++
        (integerSquareRootFixedRun value
          (integerSquareRootRounds value) 0).arithmetic) ≤ width
  rw [arithmeticEventListMaxOperandWidth_append]
  exact max_le hinit htail

/-- Exact schoolbook charge projected from the sealed square-root trace. -/
def IntegerSquareRootTrace.schoolbookCharge {input : Nat}
    (trace : IntegerSquareRootTrace input) : Nat :=
  arithmeticEventListCharge trace.arithmetic

/-- Explicit cubic schoolbook-charge envelope for the complete fixed-round
square-root execution. -/
theorem integerSquareRootTrace_schoolbookCharge_le (value : Nat) :
    (integerSquareRootTrace value).schoolbookCharge ≤
      4 * (3 + 4 * integerSquareRootRounds value) *
        (2 * (Nat.size value + 1) + 1) ^ 2 := by
  have hwidth := integerSquareRootTrace_maxOperandWidth_le value
  have hpow :
      (arithmeticEventListMaxOperandWidth
          (integerSquareRootTrace value).arithmetic + 1) ^ 2 ≤
        (2 * (Nat.size value + 1) + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2
  calc
    (integerSquareRootTrace value).schoolbookCharge =
        arithmeticEventListCharge
          (integerSquareRootTrace value).arithmetic := rfl
    _ ≤ 4 * (integerSquareRootTrace value).arithmetic.length *
          (arithmeticEventListMaxOperandWidth
            (integerSquareRootTrace value).arithmetic + 1) ^ 2 :=
      arithmeticEventListCharge_le _
    _ ≤ 4 * (integerSquareRootTrace value).arithmetic.length *
          (2 * (Nat.size value + 1) + 1) ^ 2 :=
      Nat.mul_le_mul_left
        (4 * (integerSquareRootTrace value).arithmetic.length) hpow
    _ = 4 * (3 + 4 * integerSquareRootRounds value) *
          (2 * (Nat.size value + 1) + 1) ^ 2 := by
      rw [integerSquareRootTrace_arithmetic_length]

/-- The sealed fixed-round square root has cubic schoolbook arithmetic charge
in the public input bit length. -/
theorem integerSquareRootTrace_schoolbookCharge_cubic (value : Nat) :
    (integerSquareRootTrace value).schoolbookCharge ≤
      144 * (Nat.size value + 1) ^ 3 := by
  let width := Nat.size value + 1
  have hrounds := integerSquareRootRounds_le_size value
  have hslots :
      3 + 4 * integerSquareRootRounds value ≤ 4 * width := by
    dsimp [width]
    omega
  have hopen : 2 * width + 1 ≤ 3 * width := by
    dsimp [width]
    omega
  have hsquare : (2 * width + 1) ^ 2 ≤ (3 * width) ^ 2 :=
    Nat.pow_le_pow_left hopen 2
  calc
    (integerSquareRootTrace value).schoolbookCharge ≤
        4 * (3 + 4 * integerSquareRootRounds value) *
          (2 * (Nat.size value + 1) + 1) ^ 2 :=
      integerSquareRootTrace_schoolbookCharge_le value
    _ ≤ 4 * (4 * width) * (3 * width) ^ 2 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hslots) hsquare
    _ = 144 * (Nat.size value + 1) ^ 3 := by
      dsimp [width]
      ring

end IntegerSquareRoot

end NumberTheory
end QuantumAlg

end

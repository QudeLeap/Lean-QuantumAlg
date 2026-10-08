/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

/-!
# Mathematical MSB-first group-power recovery

A faithful runtime encoding and square/multiply laws suffice to prove the
complete MSB-first scan. Its leading bit selects identity or generator and
its tail has exactly one fewer bit, including the empty-word boundary.
These are representation-independent mathematical laws; execution, persistent
service state and query accounting are specified by their actual callers
[Sho95, source.tex:1980-1987].
-/

namespace QuantumAlg.ClassicalAlgorithms.GroupPowerRecovery

universe u v

variable {G : Type u} [Group G]

/-- Concrete group-element code together with the semantics of its declared
square and multiply operations. -/
structure Access (G : Type u) [Group G] where
  /-- Runtime representation of an encoded group element. -/
  Code : Type v
  /-- Encode one mathematical group element. -/
  encode : G → Code
  /-- Declared group-square operation on runtime code. -/
  square : Code → Code
  /-- Declared group-multiply operation on runtime code. -/
  multiply : Code → Code → Code
  /-- Squaring encoded data represents the mathematical square. -/
  square_encode : ∀ value, square (encode value) = encode (value * value)
  /-- Multiplying encoded data represents mathematical multiplication. -/
  multiply_encode : ∀ left right,
    multiply (encode left) (encode right) = encode (left * right)

/-- Interpret one candidate bit as its natural-number digit. -/
def bitNat : Bool → Nat
  | false => 0
  | true => 1

/-- The natural value of a most-significant-bit-first candidate bit list. -/
def msbValue : List Bool → Nat
  | [] => 0
  | bit :: remaining => bitNat bit * 2 ^ remaining.length + msbValue remaining

/-- The exponent accumulated by the remaining MSB-first scan. -/
def scanExponent : Nat → List Bool → Nat
  | exponent, [] => exponent
  | exponent, bit :: remaining =>
      scanExponent (2 * exponent + bitNat bit) remaining

/-- Closed form for the exponent accumulated by a remaining bit suffix. -/
theorem scanExponent_eq (exponent : Nat) (bits : List Bool) :
    scanExponent exponent bits =
      exponent * 2 ^ bits.length + msbValue bits := by
  induction bits generalizing exponent with
  | nil => simp [scanExponent, msbValue]
  | cons bit remaining inductionHypothesis =>
      rw [scanExponent, inductionHypothesis]
      simp only [List.length_cons, msbValue, pow_succ]
      ring

/-- Seed the scan from the identity exponent selected by the omitted leading
bit. This is an encoding operation, not a declared group operation. -/
def initialAccumulator (A : Access G) (base : G) (leading : Bool) : A.Code :=
  A.encode (base ^ bitNat leading)

/-- One left-to-right tail step squares the accumulator and multiplies by the
base exactly when the next candidate bit is one. -/
def step (A : Access G) (base : G) (accumulator : A.Code)
    (bit : Bool) : A.Code :=
  let squared := A.square accumulator
  if bit then A.multiply squared (A.encode base) else squared

/-- One tail step advances exponent `a` to `2a + bit`. -/
theorem step_encode (A : Access G) (base : G) (exponent : Nat)
    (bit : Bool) :
    step A base (A.encode (base ^ exponent)) bit =
      A.encode (base ^ (2 * exponent + bitNat bit)) := by
  cases bit with
  | false =>
      rw [step, if_neg (by simp), A.square_encode]
      apply congrArg A.encode
      rw [← pow_add]
      congr 1
      simp [bitNat]
      omega
  | true =>
      rw [step, if_pos rfl, A.square_encode, A.multiply_encode]
      apply congrArg A.encode
      calc
        base ^ exponent * base ^ exponent * base =
            base ^ (exponent + exponent) * base := by
              rw [pow_add]
        _ = base ^ (exponent + exponent + 1) := by
              rw [pow_succ]
        _ = base ^ (2 * exponent + bitNat true) := by
              congr 1
              simp [bitNat]
              omega

/-- Process the bits below the leading candidate bit. -/
def scan (A : Access G) (base : G) : A.Code → List Bool → A.Code
  | accumulator, [] => accumulator
  | accumulator, bit :: remaining =>
      scan A base (step A base accumulator bit) remaining

/-- The encoded scan follows its arithmetic exponent recurrence exactly. -/
theorem scan_encode (A : Access G) (base : G) (exponent : Nat)
    (bits : List Bool) :
    scan A base (A.encode (base ^ exponent)) bits =
      A.encode (base ^ scanExponent exponent bits) := by
  induction bits generalizing exponent with
  | nil => rfl
  | cons bit remaining inductionHypothesis =>
      rw [scan, step_encode]
      exact inductionHypothesis (2 * exponent + bitNat bit)

/-- Evaluate a candidate by skipping its most-significant bit and scanning its
tail from the corresponding encoded identity/base seed. -/
def run (A : Access G) (base : G) : List Bool → A.Code
  | [] => A.encode 1
  | leading :: remaining =>
      scan A base (initialAccumulator A base leading) remaining

/-- The MSB-first run returns the code of the candidate group power. -/
theorem run_eq_encode_pow (A : Access G) (base : G) (candidate : List Bool) :
    run A base candidate = A.encode (base ^ msbValue candidate) := by
  cases candidate with
  | nil => simp [run, msbValue]
  | cons leading remaining =>
      change
        scan A base (A.encode (base ^ bitNat leading)) remaining =
          A.encode
            (base ^ (bitNat leading * 2 ^ remaining.length + msbValue remaining))
      rw [scan_encode, scanExponent_eq]

/-- Removing the skipped leading bit leaves one fewer tail position, with
truncated subtraction covering the empty candidate. -/
theorem tail_length_eq_length_sub_one (candidate : List Bool) :
    candidate.tail.length = candidate.length - 1 := by
  cases candidate <;> simp

end QuantumAlg.ClassicalAlgorithms.GroupPowerRecovery

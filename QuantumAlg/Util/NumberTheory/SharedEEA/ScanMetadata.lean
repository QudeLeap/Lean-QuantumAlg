/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.SwapBoundary
import Mathlib.Data.Nat.Size

/-!
# Full finite metadata ranges for a scanned shared-EEA selector

The address stores the natural sum of both complete finite length words and
the phase-two correction. One extra bit prevents wraparound even on labels
outside the reachable EEA trajectory. The corrected physical position follows
the original increment-before-swap boundary
[LYL+26, sec_EEA/sub_regshare.tex:281-296]. Widths and native-circuit workspace
derived from this representation are project refinements.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ScanMetadata

/-- One bit beyond either complete length field, including their maximum possible sum. -/
abbrev addressWidth (width : Nat) : Nat := width.size + 1

/-- Address, unary-prefix workspace and one conjunction bit, all explicitly separate. -/
def poolWidth (width : Nat) : Nat := 2 * addressWidth width + 1

/-- The exact untruncated zero-based position, including the original phase-two offset. -/
def position {width : Nat} (coefficient quotient : BitVec width.size) (firstPhase : Bool) : Nat :=
  coefficient.toNat + quotient.toNat + (if firstPhase then 0 else 1)

/-- Every complete metadata label fits; no trajectory or caller range premise is used. -/
lemma position_lt {width : Nat} (coefficient quotient : BitVec width.size) (firstPhase : Bool) :
    position coefficient quotient firstPhase < 2 ^ addressWidth width := by
  have left := coefficient.isLt
  have right := quotient.isLt
  rw [addressWidth, Nat.pow_succ]
  unfold position
  cases firstPhase <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- A finite address word records the entire natural position, rather than a truncated sum. -/
def address {width : Nat} (coefficient quotient : BitVec width.size) (firstPhase : Bool) :
    BitVec (addressWidth width) :=
  BitVec.ofNat (addressWidth width) (position coefficient quotient firstPhase)

/-- Encoding the address loses no carry on any finite input pattern. -/
lemma address_toNat {width : Nat} (coefficient quotient : BitVec width.size) (firstPhase : Bool) :
    (address coefficient quotient firstPhase).toNat = position coefficient quotient firstPhase :=
  Nat.mod_eq_of_lt (position_lt coefficient quotient firstPhase)

/-- All actual Work1 positions fit at every positive width, including near-power boundaries. -/
lemma targetIndex_lt (width : Nat) (positive : 1 ≤ width) (index : Fin (width + 3)) :
    index.val < 2 ^ addressWidth width := by
  have within := index.isLt
  have range := Nat.lt_size_self width
  have atLeastTwo : 2 ≤ 2 ^ width.size := by omega
  rw [addressWidth, Nat.pow_succ]
  omega

/-- The zero-width metadata still has a full address; its unreachable target is skipped. -/
lemma zero_position_lt (coefficient quotient : BitVec (0 : Nat).size) (firstPhase : Bool) :
    position coefficient quotient firstPhase < 2 :=
  position_lt coefficient quotient firstPhase

/-- The P-256 address retains ten bits, including the carry from two nine-bit lengths. -/
lemma p256_addressWidth : addressWidth 256 = 10 := by decide

/-- The shared arithmetic pool has exactly the selected twenty-one physical bits. -/
lemma p256_poolWidth : poolWidth 256 = 21 := by decide

/-- A P-256 Work1 selector retains exactly 259 valid target leaves. -/
lemma p256_targetCount : 256 + 3 = 259 := by decide

end QuantumAlg.NumberTheory.SharedEEA.ScanMetadata

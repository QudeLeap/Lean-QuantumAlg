/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Iteration
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Ring

/-!
# Reversible consumption of a shared-EEA quotient bit

Phase three adds the next quotient bit's contribution to the increasing
coefficient, then clears that bit using the updated coefficient
[LYL+26, sec_EEA/sub_4phase.tex:24-37]. If the already accumulated low
coefficient is below the next contribution, the updated value determines
the consumed bit exactly. The comparison must include equality. This
module proves that fact also when the previous coefficient and all lower
quotient bits are zero.

The strict comparison printed in `sec_EEA/sub_4phase.tex:29` does not cover
that reachable boundary. The construction below uses `≥`; the implemented
sign update in `sec_EEA/sub_regshare.tex:298` also uses `≥`. Relating the
complete phase/flag implementation to this local arithmetic transition is
a separate refinement obligation.

The quotient bit remains an explicit coordinate. The forward transition
clears it by XOR with a value recovered from the actual updated coefficient,
and the inverse reconstructs both the coefficient and the bit. This is a
natural-number specification, with no quantum operation or resource claim.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.QuotientBits

/-- Read the next consumed quotient bit from the updated coefficient. -/
def readBit (threshold value : Nat) : Bool := decide (threshold ≤ value)

/-- Add a quotient bit's contribution and clear that bit using the updated value. -/
def consumeBit (threshold : Nat) (state : Nat × Bool) : Nat × Bool :=
  let updated := state.1 + if state.2 then threshold else 0
  (updated, state.2 ^^ readBit threshold updated)

/-- Reconstruct the low coefficient and quotient bit from a valid cleared output. -/
def recoverBit (threshold : Nat) (state : Nat × Bool) : Nat × Bool :=
  (state.1 % threshold, readBit threshold state.1)

/-- The weak threshold comparison recovers the actual bit, including equality. -/
lemma readBit_add (threshold value : Nat) (bit : Bool) (below : value < threshold) :
    readBit threshold (value + if bit then threshold else 0) = bit := by
  cases bit
  · change decide (threshold ≤ value + 0) = false
    apply decide_eq_false
    omega
  · change decide (threshold ≤ value + threshold) = true
    exact decide_eq_true (Nat.le_add_left threshold value)

/-- The actual XOR clears the consumed coordinate on its reachable range. -/
lemma consumeBit_clears (threshold value : Nat) (bit : Bool) (below : value < threshold) :
    (consumeBit threshold (value, bit)).2 = false := by
  change (bit ^^ readBit threshold (value + if bit then threshold else 0)) = false
  rw [readBit_add threshold value bit below, Bool.xor_self]

/-- Reducing the updated coefficient modulo its threshold recovers its low part. -/
lemma consumeBit_low (threshold value : Nat) (bit : Bool) (below : value < threshold) :
    (consumeBit threshold (value, bit)).1 % threshold = value := by
  cases bit
  · change (value + 0) % threshold = value
    simpa only [Nat.add_zero] using Nat.mod_eq_of_lt below
  · change (value + threshold) % threshold = value
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt below]

/-- Bit consumption has an exact left inverse on every admissible low coefficient. -/
lemma recoverBit_consumeBit (threshold value : Nat) (bit : Bool)
    (below : value < threshold) :
    recoverBit threshold (consumeBit threshold (value, bit)) = (value, bit) := by
  apply Prod.ext
  · exact consumeBit_low threshold value bit below
  · exact readBit_add threshold value bit below

/-- No two valid coefficient/bit inputs are merged by the clearing transition. -/
lemma consumeBit_injective {threshold : Nat} {left right : Nat × Bool}
    (leftBelow : left.1 < threshold) (rightBelow : right.1 < threshold)
    (same : consumeBit threshold left = consumeBit threshold right) : left = right := by
  calc
    left = recoverBit threshold (consumeBit threshold left) :=
      (recoverBit_consumeBit threshold left.1 left.2 leftBelow).symm
    _ = recoverBit threshold (consumeBit threshold right) := congrArg (recoverBit threshold) same
    _ = right := recoverBit_consumeBit threshold right.1 right.2 rightBelow

/-- A consumed bit adds at most one threshold to a strictly smaller low coefficient. -/
lemma consumeBit_lt_double (threshold value : Nat) (bit : Bool)
    (below : value < threshold) :
    (consumeBit threshold (value, bit)).1 < 2 * threshold := by
  cases bit
  · change value + 0 < 2 * threshold
    omega
  · change value + threshold < 2 * threshold
    omega

/-- The source's previous coefficient and lower quotient bits fit below the next contribution. -/
lemma lowCoefficient_lt (previous coefficient low scale : Nat)
    (previousBound : previous < coefficient) (lowBound : low < scale) :
    previous + low * coefficient < scale * coefficient := by
  calc
    previous + low * coefficient < coefficient + low * coefficient :=
      Nat.add_lt_add_right previousBound _
    _ = (low + 1) * coefficient := by ring
    _ ≤ scale * coefficient := Nat.mul_le_mul_right coefficient lowBound

/-- The next quotient bit is recovered from the actual phase-three coefficient update. -/
lemma readBit_coefficientUpdate (previous coefficient low scale : Nat) (bit : Bool)
    (previousBound : previous < coefficient) (lowBound : low < scale) :
    readBit (scale * coefficient)
      (previous + low * coefficient + if bit then scale * coefficient else 0) = bit :=
  readBit_add _ _ bit (lowCoefficient_lt previous coefficient low scale previousBound lowBound)

/-- The coefficient/bit transition clears the bit and preserves enough data to reconstruct it. -/
lemma coefficientUpdate_reversible (previous coefficient low scale : Nat) (bit : Bool)
    (previousBound : previous < coefficient) (lowBound : low < scale) :
    (consumeBit (scale * coefficient) (previous + low * coefficient, bit)).2 = false ∧
      recoverBit (scale * coefficient)
          (consumeBit (scale * coefficient) (previous + low * coefficient, bit)) =
        (previous + low * coefficient, bit) := by
  have below := lowCoefficient_lt previous coefficient low scale previousBound lowBound
  exact ⟨consumeBit_clears _ _ bit below, recoverBit_consumeBit _ _ bit below⟩

/-- The binary place-value specialization used by the four-phase algorithm. -/
lemma coefficientUpdate_binaryPlace (previous coefficient low position : Nat) (bit : Bool)
    (previousBound : previous < coefficient) (lowBound : low < 2 ^ position) :
    recoverBit (2 ^ position * coefficient)
        (consumeBit (2 ^ position * coefficient) (previous + low * coefficient, bit)) =
      (previous + low * coefficient, bit) :=
  (coefficientUpdate_reversible previous coefficient low (2 ^ position) bit
    previousBound lowBound).2

/-- Equality is a reachable one-bit input even when the entire low coefficient is zero. -/
lemma zero_low_consumes_one (threshold : Nat) (positive : 0 < threshold) :
    consumeBit threshold (0, true) = (threshold, false) := by
  apply Prod.ext
  · change 0 + threshold = threshold
    exact Nat.zero_add threshold
  · exact consumeBit_clears threshold 0 true positive

/-- The smallest valid modulus reaches the equality boundary while consuming its quotient. -/
lemma smallest_input_equality_boundary :
    (IterationState.initial 2 1).quotient = 2 ∧
      consumeBit (2 ^ 1 * 1) (0 + 0 * 1, true) = (2, false) ∧
      decide (2 < (consumeBit (2 ^ 1 * 1) (0 + 0 * 1, true)).1) = false := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.QuotientBits

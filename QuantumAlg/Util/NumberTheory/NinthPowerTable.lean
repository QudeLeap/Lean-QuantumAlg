/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting
import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.CommonDivisorTail
import all QuantumAlg.Util.NumberTheory.Cyclic.Order

/-!
# Finite correction table for a ninth-power divisor bound

This module isolates the finite small-prime computation used by the general
divisor-function argument.  It deliberately uses the elementary wheel
`2 * 3 * 5 * 7 * 11`, rather than enumerating a trusted external prime table.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Monotone correction table for `(a+1)^9 / p^a`.  On prime inputs the
breakpoints encode the exact minimal correction values for the first thirteen
exponents. -/
def primePowerNineCorrectionBits (p : Nat) : Nat :=
  if p < 3 then 22
  else if p < 5 then 16
  else if p < 7 then 12
  else if p < 11 then 10
  else if p < 13 then 8
  else if p < 19 then 7
  else if p < 29 then 6
  else if p < 37 then 5
  else if p < 67 then 4
  else if p < 131 then 3
  else if p < 257 then 2
  else if p < 512 then 1
  else 0

/-- The elementary `2·3·5·7·11` wheel.  Every prime is either one
of its five prime factors or is coprime to the wheel. -/
def WheelCandidate (p : Nat) : Prop :=
  2 ≤ p ∧ (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨
    p.Coprime 2310)

instance (p : Nat) : Decidable (WheelCandidate p) := by
  unfold WheelCandidate
  infer_instance

/-- Prime numbers belong to the elementary wheel candidate set. -/
lemma prime_wheelCandidate {p : Nat} (hp : p.Prime) : WheelCandidate p := by
  unfold WheelCandidate
  refine ⟨hp.two_le, ?_⟩
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  right
  by_cases hp3 : p = 3
  · exact Or.inl hp3
  right
  by_cases hp5 : p = 5
  · exact Or.inl hp5
  right
  by_cases hp7 : p = 7
  · exact Or.inl hp7
  right
  by_cases hp11 : p = 11
  · exact Or.inl hp11
  right
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hdiv' : p ∣ 2 * (3 * (5 * (7 * 11))) := by
    exact hdiv
  rcases hp.dvd_or_dvd hdiv' with h2 | hrest
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  rcases hp.dvd_or_dvd hrest with h3 | hrest
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3)
  rcases hp.dvd_or_dvd hrest with h5 | hrest
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5)
  rcases hp.dvd_or_dvd hrest with h7 | h11
  · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h7)
  · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h11)

set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the 512 small wheel candidates and their gcds.
set_option maxRecDepth 100000 in
/-- The wheel superset below `512` consumes 276 correction bits.  This is an
intentional 16-bit overestimate of the exact prime sum, avoiding any trusted
prime-table enumeration. -/
lemma sum_wheelCandidate_nine_corrections :
    ∑ p ∈ (Finset.range 512).filter WheelCandidate,
      primePowerNineCorrectionBits p = 276 := by
  decide

end NumberTheory
end QuantumAlg

end

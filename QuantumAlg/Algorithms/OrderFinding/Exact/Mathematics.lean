/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Measure
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.SourceSupport
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Util.Order.Finding
import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# Exact dyadic phase recovery and accepted order-finding samples

These are the original inverse-QFT recovery equation and exact-grid output
predicate. Recovering the order itself additionally requires a coprime sampled
numerator; certainty of an exact-grid sample does not assert that extra event.
-/

namespace QuantumAlg.OrderFinding

open NormalizedVector

noncomputable section

/-- Inverse-QFT recovery for an exact dyadic phase. -/
theorem main_exact_dyadic {t s r : Nat} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) (j : Fin (2 ^ t))
    (hj : j.val = s * (2 ^ t / r)) :
    (invQFT t).applyVec (phaseState t ((s : Real) / r)) =
        (NormalizedVector.ket (R := Qubits t) j : HilbertVector (Qubits t)) ∧
      2 ^ t / Nat.gcd j.val (2 ^ t) = r := by
  refine ⟨?_, ?_⟩
  · have hphase : (s : Real) / r = (j.val : Real) / (2 : Real) ^ t := by
      rw [hj]
      have hr0 : (r : Real) ≠ 0 := by exact_mod_cast hr.ne'
      have h2t0 : (2 : Real) ^ t ≠ 0 := by positivity
      have hrr : (r : Real) * ((2 ^ t / r : Nat) : Real) = (2 : Real) ^ t := by
        exact_mod_cast Nat.mul_div_cancel' hrt
      rw [div_eq_div_iff hr0 h2t0]
      push_cast
      rw [← hrr]
      ring
    have hnormalized :=
      QuantumPhaseEstimation.main_exact_dyadic t j ((s : Real) / r) hphase
    exact congrArg (fun state : NormalizedVector (Qubits t) =>
      (state : HilbertVector (Qubits t))) hnormalized
  · rw [hj]
    exact main_recovery hr hrt hsr

/-! ## Canonical typed exact-dyadic endpoint -/

/-- Typed terminal output of the exact-dyadic endpoint. -/
abbrev Output (t : Nat) := CShape.Value (.unsignedWord t)

/-- The typed decoder output lies on the exact `r`-point dyadic grid. -/
def SuccessfulOutcome (r : Nat) {t : Nat} (output : Output t) : Prop :=
  match output with
  | .unsignedWord word =>
      ∃ s : Fin r, word.val = s.val * (2 ^ t / r)

/-- Canonical encoding of one actually measured phase-register outcome. -/
def encodedOutcome {t : Nat} (outcome : TerminalZMeasure.Outcome t) : Output t :=
  .unsignedWord
    (ClassicalAlgorithms.TerminalDecode.fullRegisterIndex outcome)

@[simp] theorem successful_encodedOutcome_iff {r t : Nat}
    (outcome : TerminalZMeasure.Outcome t) :
    SuccessfulOutcome r (encodedOutcome outcome) ↔ Native.ExactOutcome r t outcome := by
  rfl

end

end QuantumAlg.OrderFinding

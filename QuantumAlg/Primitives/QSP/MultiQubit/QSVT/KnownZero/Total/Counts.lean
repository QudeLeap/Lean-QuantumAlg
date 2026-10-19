/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Word

/-!
# Exact source and native counts of a known-projector word

The query budget retains ordinary and inverse calls separately. The native
budget includes the complete restored-work path on every register width.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (allowControlled : Bool)

private def eventPool
    (event : Resource.Event
      (.quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false))) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)) :=
  ResourcePool.singleton event

/-- Independent closed-form budget for L alternating source slots. -/
def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true false)) :=
  ((L + 1) / 2) • eventPool (m := m) (n := n) allowControlled (.oracle .ordinary) +
    (L / 2) • eventPool (m := m) (n := n) allowControlled (.oracle .inverse) +
    L • phaseBudget m n (UnitarySource.model (m + n) allowControlled true false)

private lemma budget_succ (L : Nat) :
    budget (m := m) (n := n) allowControlled (L + 1) =
      (budget (m := m) (n := n) allowControlled L + eventPool (m := m) (n := n) allowControlled
        (.oracle (if decide ((L + 1) % 2 = 0) then .inverse else .ordinary))) +
      phaseBudget m n (UnitarySource.model (m + n) allowControlled true false) := by
  by_cases even : (L + 1) % 2 = 0
  · have upper : (L + 1 + 1) / 2 = (L + 1) / 2 := by omega
    have lower : (L + 1) / 2 = L / 2 + 1 := by omega
    simp only [budget, upper, lower, even, decide_true, ↓reduceIte,
      add_nsmul, one_nsmul]
    ac_rfl
  · have upper : (L + 1 + 1) / 2 = (L + 1) / 2 + 1 := by omega
    have lower : (L + 1) / 2 = L / 2 := by omega
    simp only [budget, upper, lower, even, decide_false, Bool.false_eq_true, ↓reduceIte,
      add_nsmul, one_nsmul]
    ac_rfl

/-- Every source call and native phase event is derived from the same executed list. -/
lemma totalCircuit_events (phases : List ℝ) :
    (circuit (m := m) (n := n) allowControlled phases).eventCost =
      budget (m := m) (n := n) allowControlled phases.length := by
  induction phases with
  | nil => simp [circuit, budget]
  | cons φ phases ih =>
      simp only [circuit, UnitaryCircuit.seq_eventCost, ih, KnownZero.signal_events,
        totalPhase_events, List.length_cons]
      exact (budget_succ (m := m) (n := n) allowControlled phases.length).symm

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total

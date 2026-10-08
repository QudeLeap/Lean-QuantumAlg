/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Word

/-!
# Exact source and native counts of a known-projector word

The query budget retains ordinary and inverse calls separately. The native
budget includes both expanded flips and the rotation at every phase slot.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

private def eventPool
    (event : Resource.Event
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  ResourcePool.singleton event

/-- Independent per-slot native budget, with no source query or hidden projector cost. -/
def phaseBudget :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  2 • ZeroProjector.SourceWork.budget (UnitarySource.model U allowControlled true false) m +
    eventPool U allowControlled (.gate .singleQubit)

/-- Independent closed-form budget for L alternating source slots. -/
def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  ((L + 1) / 2) • eventPool U allowControlled (.oracle .ordinary) +
    (L / 2) • eventPool U allowControlled (.oracle .inverse) +
    L • phaseBudget U allowControlled

/-- One actual signal occurrence retains exactly its granted query coordinate. -/
theorem signal_events (inverse : Bool) :
    (signal U allowControlled inverse).eventCost =
      eventPool U allowControlled (.oracle (if inverse then .inverse else .ordinary)) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    UnitarySource.Binary.circuit_events]
  rfl

private theorem budget_succ (L : Nat) :
    budget U allowControlled (L + 1) =
      (budget U allowControlled L + eventPool U allowControlled
        (.oracle (if decide ((L + 1) % 2 = 0) then .inverse else .ordinary))) +
      phaseBudget U allowControlled := by
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
theorem circuit_events (phases : List ℝ) :
    (circuit U positive allowControlled phases).eventCost =
      budget U allowControlled phases.length := by
  induction phases with
  | nil => simp [circuit, budget]
  | cons φ phases ih =>
      simp only [circuit, UnitaryCircuit.seq_eventCost, ih, signal_events, phase_events,
        List.length_cons]
      exact (budget_succ U allowControlled phases.length).symm

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero

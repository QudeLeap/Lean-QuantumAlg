/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Resources

/-!
# Exact resources of one source sequence shared by two branches

The query budget retains ordinary and inverse calls separately. The native
budget includes both expanded flips and all four native selector gates.
Branch selection introduces no controlled source query.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
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
    2 • eventPool U allowControlled (.gate .singleQubit) +
    2 • eventPool U allowControlled (.gate .cnot)

/-- Independent closed-form budget for L alternating source slots. -/
def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  ((L + 1) / 2) • eventPool U allowControlled (.oracle .ordinary) +
    (L / 2) • eventPool U allowControlled (.oracle .inverse) +
    L • phaseBudget U allowControlled

private theorem selector_events (zero one : ℝ) :
    (Gate.Rotation.Multiplex.circuitAt (width := 1 + (1 + (m + n)))
      0 (Fin.natAdd 1 (0 : Fin (1 + (m + n)))) (by
        intro same
        have values := congrArg Fin.val same
        change 0 = 1 + 0 at values
        omega) (UnitarySource.model U allowControlled true false) zero one).eventCost =
      2 • eventPool U allowControlled (.gate .singleQubit) +
        2 • eventPool U allowControlled (.gate .cnot) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    Gate.Rotation.Multiplex.circuitAt_eventTrace]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, two_nsmul, eventPool]
  ac_rfl

/-- All native projector flips and selector gates are included, without a projector query. -/
theorem phase_events (zero one : ℝ) :
    (phase m n positive (UnitarySource.model U allowControlled true false) zero one).eventCost =
      phaseBudget U allowControlled := by
  simp only [phase, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost, KnownZero.flip_events,
    selector_events, phaseBudget, two_nsmul]
  ac_rfl

/-- One actual signal occurrence retains exactly its granted query coordinate. -/
theorem signal_events (inverse : Bool) :
    (signal U allowControlled inverse).eventCost =
      eventPool U allowControlled (.oracle (if inverse then .inverse else .ordinary)) := by
  rw [signal, UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    KnownZero.signal_events]
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
theorem circuit_events (phases : List (ℝ × ℝ)) :
    (circuit U positive allowControlled phases).eventCost =
      budget U allowControlled phases.length := by
  induction phases with
  | nil => simp [circuit, budget]
  | cons angles phases ih =>
      simp only [circuit, UnitaryCircuit.seq_eventCost, ih, signal_events, phase_events,
        List.length_cons]
      exact (budget_succ U allowControlled phases.length).symm

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared

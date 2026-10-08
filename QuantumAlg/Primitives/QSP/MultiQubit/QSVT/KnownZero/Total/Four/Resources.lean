/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Resources

/-!
# Exact resources of one source sequence shared by four branches

The query budget retains ordinary and inverse calls separately. The native
budget includes both expanded flips and all ten native selector gates.
Branch selection introduces no controlled source query.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (allowControlled : Bool)

private def eventPool
    (event : Resource.Event
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  ResourcePool.singleton event

private def nativePhaseBudget (m n : Nat) (oracles : OracleModel) :
    ResourcePool (.quantum AlgorithmGate.model oracles) :=
  let native := ZeroProjector.SourceWork.budget oracles
  let single := ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .singleQubit)
  let cnot := ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
    (.gate .cnot)
  match m, n with
  | 0, 0 => 4 • single + 6 • cnot
  | k + 1, 0 => 4 • native k + 24 • single + 32 • cnot
  | m, _ + 1 => 2 • native m + 4 • single + 6 • cnot

/-- Independent per-slot native budget, with no source query or hidden projector cost. -/
def phaseBudget :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  nativePhaseBudget m n (UnitarySource.model U allowControlled true false)

/-- Independent closed-form budget for L alternating source slots. -/
def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false)) :=
  ((L + 1) / 2) • eventPool U allowControlled (.oracle .ordinary) +
    (L / 2) • eventPool U allowControlled (.oracle .inverse) +
    L • phaseBudget U allowControlled

/-- The complete native phase budget applies also when the original signal width is zero. -/
theorem totalFourPhase_events (a b c d : ℝ) :
    (phase m n (UnitarySource.model U allowControlled true false) a b c d).eventCost =
      phaseBudget U allowControlled := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          exact SharedFour.selector_events U allowControlled (-2 * a) (-2 * b)
            (-2 * c) (-2 * d)
      | succ k => exact ControlWork.Four.controlWork_fourPhase_events k 0 _ a b c d
  | succ n =>
      cases m <;> exact SharedFour.fourPhase_events U (Nat.zero_lt_succ n)
        allowControlled a b c d

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
theorem totalFourWord_events (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    (circuit U allowControlled phases).eventCost =
      budget U allowControlled phases.length := by
  induction phases with
  | nil => simp [circuit, budget]
  | cons angles phases ih =>
      simp only [circuit, UnitaryCircuit.seq_eventCost, ih, SharedFour.fourSignal_events,
        totalFourPhase_events,
        List.length_cons]
      exact (budget_succ U allowControlled phases.length).symm

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four

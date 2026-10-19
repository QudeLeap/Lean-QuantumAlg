/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.NativeGates
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Bounds

/-!
# Independent linear native gate budget of the shared complex QSVT word

Native gates include both masks, all conjunctions, selector rotations and
boundary gates. Ordinary and controlled source queries are counted separately.
The width bound applies even when the source has no signal or ancilla qubits.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open Gate.Toffoli
noncomputable section

private lemma fourPhase_native_gate_bound {m n : Nat}
    (allowControlled : Bool) :
    nativeGateCount (phaseBudget (m := m) (n := n) allowControlled) ≤ 40 * m + 20 := by
  unfold phaseBudget
  cases n with
  | zero =>
      cases m with
      | zero => simp [nativePhaseBudget, nativeGateCount]
      | succ k =>
          have bound := KnownZero.sourceWork_native_gate_bound
           (UnitarySource.model (k + 1 + 0) allowControlled true false) k
          simp only [nativePhaseBudget, nativeGateCount_add, nativeGateCount_nsmul,
            nativeGateCount_singleton_gate, Nat.mul_one]
          omega
  | succ n =>
      have bound := KnownZero.sourceWork_native_gate_bound
       (UnitarySource.model (m + (n + 1)) allowControlled true false) m
      simp only [nativePhaseBudget, nativeGateCount_add, nativeGateCount_nsmul,
        nativeGateCount_singleton_gate, Nat.mul_one]
      omega

/-- The complete independent complex-QSVT budget has linear native gate growth. -/
lemma totalComplexBudget_native_gate_bound {m n : Nat}
    (L : Nat) :
    nativeGateCount (complexBudget (m := m) (n := n) L) ≤ (40 * m + 20) * (L + 1) + 19 := by
  have phaseBound := fourPhase_native_gate_bound (m := m) (n := n) true
  have repeated := Nat.mul_le_mul_left (L + 1) phaseBound
  unfold complexBudget unmatchedBudget budget
  split_ifs <;>
    simp only [nativeGateCount_add, nativeGateCount_nsmul, eventPool,
      nativeGateCount_singleton_gate, nativeGateCount_singleton_query, Nat.mul_one,
      Nat.mul_zero, zero_add, add_zero]
  all_goals nlinarith

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four

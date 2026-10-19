/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.NativeGates
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Counts

/-!
# Independent native gate bound for matching-parity execution

The per-slot bound covers the complete restored-work phase, including zero
signal width. Source queries are separate and the boundary Hadamards add two
native gates to the final Hermitian execution.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
open Gate.Toffoli
noncomputable section

private lemma phase_native_gate_bound (m n : Nat) (oracles : OracleModel) :
    nativeGateCount (phaseBudget m n oracles) ≤ 40 * m + 3 := by
  cases n with
  | zero =>
      cases m with
      | zero => simp [phaseBudget, nativeGateCount]
      | succ k =>
          have bound := KnownZero.sourceWork_native_gate_bound oracles k
          simp only [phaseBudget, nativeGateCount_add, nativeGateCount_nsmul,
            nativeGateCount_singleton_gate, Nat.mul_one]
          omega
  | succ n =>
      have bound := KnownZero.sourceWork_native_gate_bound oracles m
      simp only [phaseBudget, nativeGateCount_add, nativeGateCount_nsmul,
        nativeGateCount_singleton_gate]
      omega

/-- The independent matching-parity word budget has linear width-times-degree gate cost. -/
lemma totalRealBudget_native_gate_bound {m n : Nat}
    (allowControlled : Bool) (L : Nat) :
    nativeGateCount (budget (m := m) (n := n) allowControlled L) ≤ (40 * m + 3) * L := by
  have bound := phase_native_gate_bound m n (UnitarySource.model (m + n) allowControlled true false)
  simp only [budget, nativeGateCount_add, nativeGateCount_nsmul, eventPool,
    nativeGateCount_singleton_query, Nat.mul_zero, zero_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left L bound

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total

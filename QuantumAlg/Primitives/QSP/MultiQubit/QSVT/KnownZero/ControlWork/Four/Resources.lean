/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.ControlWork.Four

/-!
# Exact native resources for four control-work phases

All five multiplexed rotations and both final-control masks are counted.
The original control-work calls retain their complete native budgets.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.ControlWork.Four
noncomputable section

private theorem rotation_events (k n : Nat) (oracles : OracleModel) (a b c d : ℝ) :
    (rotation k n oracles a b c d).eventCost =
      4 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      6 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) := by
  rw [rotation, ← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    Gate.Rotation.Multiplex.Four.fourRotation_prefix_eventTrace]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero,
    show (4 : Nat) = 2 + 2 from rfl, show (6 : Nat) = 2 + 2 + 2 from rfl,
    add_nsmul, two_nsmul]
  ac_rfl

/-- The exact pool charges all actual native gates, with no source or projector queries. -/
theorem controlWork_fourPhase_events (k n : Nat) (oracles : OracleModel)
    (a b c d : ℝ) :
    (phase k n oracles a b c d).eventCost =
      4 • ZeroProjector.SourceWork.budget oracles k +
      24 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
      32 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) := by
  simp only [phase, intersectionRotation, firstRotation, lift, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost, rotation_events,
    KnownZero.flip_events, ControlWork.lastFlip_events]
  simp only [show (24 : Nat) = 4 + 4 + 4 + 4 + 4 + 2 + 2 from rfl,
    show (32 : Nat) = 6 + 6 + 6 + 6 + 6 + 1 + 1 from rfl,
    show (4 : Nat) = 2 + 2 from rfl, add_nsmul, one_nsmul, two_nsmul]
  ac_rfl

end
end QuantumAlg.QSP.MultiQubit.QSVT.ControlWork.Four

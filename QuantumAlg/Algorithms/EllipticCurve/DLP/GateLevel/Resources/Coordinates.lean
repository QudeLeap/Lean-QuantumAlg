/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Resources.Unitary

/-!
# Original literal ECDLP query and elementary gate coordinates

These are the original label counts of the pure unitary member, including
its one-term preparation branch. Actual allocation, reset, measurement and
checked recovery extend these same coordinates at their execution boundary.
No prepared-attempt or repeated-run wrapper belongs to this mathematical owner.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelResources

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local simp] ResourcePool.count_singleton_of_ne
attribute [local simp] Resource.GateLabel.mk.injEq

/-- Aggregate count of the three elementary one-qubit coordinates. -/
def singleQubitCount (pool : ResourcePool .quantum) : Nat :=
  ResourcePool.count (.gate (.builtin "hadamard")) pool +
    ResourcePool.count (.gate (.builtin "x")) pool +
      ResourcePool.count UniformSuperposition.rotationYEvent pool

/-- Literal CNOT count. -/
def cnotCount (pool : ResourcePool .quantum) : Nat :=
  ResourcePool.count UniformSuperposition.cnotEvent pool

@[simp]
theorem singleQubitCount_add (left right : ResourcePool .quantum) :
    singleQubitCount (left + right) =
      singleQubitCount left + singleQubitCount right := by
  simp [singleQubitCount]
  omega

@[simp]
theorem singleQubitCount_scale (multiplicity : Nat)
    (pool : ResourcePool .quantum) :
    singleQubitCount (ResourcePool.scale multiplicity pool) =
      multiplicity * singleQubitCount pool := by
  simp [singleQubitCount, Nat.mul_add]

@[simp]
theorem cnotCount_add (left right : ResourcePool .quantum) :
    cnotCount (left + right) = cnotCount left + cnotCount right := by
  simp [cnotCount]

@[simp]
theorem cnotCount_scale (multiplicity : Nat)
    (pool : ResourcePool .quantum) :
    cnotCount (ResourcePool.scale multiplicity pool) =
      multiplicity * cnotCount pool := by
  simp [cnotCount]

private theorem gateLabel_ne_of_name_ne
    {left right : Resource.GateLabel}
    (different : left.name ≠ right.name) : left ≠ right := by
  intro equality
  exact different (congrArg Resource.GateLabel.name equality)

private theorem gateEvent_not_elementary_of_name
    (label : Resource.GateLabel)
    (notHadamard : label.name ≠ "hadamard")
    (notX : label.name ≠ "x")
    (notRotationY : label.name ≠ "rotation-y")
    (notCnot : label.name ≠ "cnot") :
    ¬ UniformSuperposition.elementaryEvent (.gate label) := by
  intro elementary
  simp only [UniformSuperposition.elementaryEvent,
    UniformSuperposition.hadamardEvent_eq_gate,
    UniformSuperposition.xEvent_eq_gate,
    UniformSuperposition.rotationYEvent_eq_gate,
    UniformSuperposition.cnotEvent_eq_gate] at elementary
  rcases elementary with equality | equality | equality | equality
  · exact notHadamard (congrArg Resource.GateLabel.name
      (Resource.Event.gate.inj equality))
  · exact notX (congrArg Resource.GateLabel.name
      (Resource.Event.gate.inj equality))
  · exact notRotationY (congrArg Resource.GateLabel.name
      (Resource.Event.gate.inj equality))
  · exact notCnot (congrArg Resource.GateLabel.name
      (Resource.Event.gate.inj equality))

private theorem qftControlledPhaseEvent_not_elementary :
    ¬ UniformSuperposition.elementaryEvent
      (.gate qftControlledPhaseLabel) :=
  gateEvent_not_elementary_of_name qftControlledPhaseLabel
    (by change "phase-rotation" ≠ "hadamard"; simp)
    (by change "phase-rotation" ≠ "x"; simp)
    (by change "phase-rotation" ≠ "rotation-y"; simp)
    (by change "phase-rotation" ≠ "cnot"; simp)

private theorem swapEvent_not_elementary :
    ¬ UniformSuperposition.elementaryEvent (.gate (.builtin "swap")) :=
  gateEvent_not_elementary_of_name (.builtin "swap")
    (by change "swap" ≠ "hadamard"; simp)
    (by change "swap" ≠ "x"; simp)
    (by change "swap" ≠ "rotation-y"; simp)
    (by change "swap" ≠ "cnot"; simp)

private theorem quantumSubroutineEvent_not_elementary
    (label : Resource.QuantumSubroutineLabel) :
    ¬ UniformSuperposition.elementaryEvent (.quantumSubroutine label) := by
  intro elementary
  simp only [UniformSuperposition.elementaryEvent,
    UniformSuperposition.hadamardEvent_eq_gate,
    UniformSuperposition.xEvent_eq_gate,
    UniformSuperposition.rotationYEvent_eq_gate,
    UniformSuperposition.cnotEvent_eq_gate] at elementary
  rcases elementary with equality | equality | equality | equality <;>
    cases equality

private theorem qft_quantumSubroutine_count_zero (width : Nat)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
        (QFTCircuit width).eventCost = 0 := by
  rw [QFTCircuit_eventCost_eq]
  simp [ResourcePool.count, ResourcePool.singleton]

private theorem qft_cnot_count_zero (width : Nat) :
    ResourcePool.count UniformSuperposition.cnotEvent
        (QFTCircuit width).eventCost = 0 := by
  apply QFTCircuit_event_count_eq_zero_of_ne
  · apply gateLabel_ne_of_name_ne
    change "cnot" ≠ "hadamard"
    simp
  · apply gateLabel_ne_of_name_ne
    change "cnot" ≠ "phase-rotation"
    simp
  · apply gateLabel_ne_of_name_ne
    change "cnot" ≠ "swap"
    simp

private theorem qft_rotationY_count_zero (width : Nat) :
    ResourcePool.count UniformSuperposition.rotationYEvent
        (QFTCircuit width).eventCost = 0 := by
  apply QFTCircuit_event_count_eq_zero_of_ne
  · apply gateLabel_ne_of_name_ne
    change "rotation-y" ≠ "hadamard"
    simp
  · apply gateLabel_ne_of_name_ne
    change "rotation-y" ≠ "phase-rotation"
    simp
  · apply gateLabel_ne_of_name_ne
    change "rotation-y" ≠ "swap"
    simp

private theorem qft_x_count_zero (width : Nat) :
    ResourcePool.count (.gate (.builtin "x"))
        (QFTCircuit width).eventCost = 0 := by
  apply QFTCircuit_event_count_eq_zero_of_ne
  · apply gateLabel_ne_of_name_ne
    change "x" ≠ "hadamard"
    simp
  · apply gateLabel_ne_of_name_ne
    change "x" ≠ "phase-rotation"
    simp
  · apply gateLabel_ne_of_name_ne
    change "x" ≠ "swap"
    simp

/-- The literal circuit meets the locked aggregate one-qubit formula. -/
theorem quantumCircuit_singleQubitCount_le (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    singleQubitCount (GateLevelAttempt.quantumCircuit I B A).eventCost ≤
      2 * FiniteCyclicDLP.orderWidth (problem I) + 2 * B.singleQubitBound := by
  have preparationBound := B.paddedPreparation_singleQubitCost_le (problem I)
  unfold UniformSuperposition.singleQubitCost at preparationBound
  unfold singleQubitCount
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add]
  have queryHadamardZero : ResourcePool.count (.gate (.builtin "hadamard"))
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  have queryXZero : ResourcePool.count (.gate (.builtin "x"))
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  have queryRotationZero : ResourcePool.count UniformSuperposition.rotationYEvent
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  have qftHadamard :=
    (QFTCircuit_exact_event_gate_counts
      (FiniteCyclicDLP.orderWidth (problem I))).1
  rw [queryHadamardZero, queryXZero, queryRotationZero,
    qftHadamard, qft_x_count_zero, qft_rotationY_count_zero]
  omega

/-- The literal circuit's CNOTs come only from its two explicit preparations. -/
theorem quantumCircuit_cnotCount_le (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    cnotCount (GateLevelAttempt.quantumCircuit I B A).eventCost ≤
      2 * B.cnotBound := by
  have preparationBound := B.paddedPreparation_cnotCost_le (problem I)
  unfold UniformSuperposition.cnotCost at preparationBound
  unfold cnotCount
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add]
  have queryZero : ResourcePool.count UniformSuperposition.cnotEvent
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  rw [queryZero, qft_cnot_count_zero]
  omega

/-- The two inverse QFTs contain exactly the locked controlled-phase count. -/
theorem quantumCircuit_controlledPhase_count (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
        (GateLevelAttempt.quantumCircuit I B A).eventCost =
      FiniteCyclicDLP.orderWidth (problem I) *
        (FiniteCyclicDLP.orderWidth (problem I) - 1) := by
  have preparationZero := B.paddedPreparation_count_zero_of_not_elementary
    (problem I) (.gate qftControlledPhaseLabel)
    qftControlledPhaseEvent_not_elementary
  have qftCount :=
    (QFTCircuit_exact_event_gate_counts
      (FiniteCyclicDLP.orderWidth (problem I))).2.1
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, qftCount]
  have queryZero : ResourcePool.count (.gate qftControlledPhaseLabel)
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  rw [queryZero]
  simpa [two_mul] using Nat.two_mul_div_two_of_even
    (Nat.even_mul_pred_self (FiniteCyclicDLP.orderWidth (problem I)))

/-- The two inverse QFTs contain exactly two standard bit-reversal networks. -/
theorem quantumCircuit_swap_count (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    ResourcePool.count (.gate (.builtin "swap"))
        (GateLevelAttempt.quantumCircuit I B A).eventCost =
      2 * (FiniteCyclicDLP.orderWidth (problem I) / 2) := by
  have preparationZero := B.paddedPreparation_count_zero_of_not_elementary
    (problem I) (.gate (.builtin "swap")) swapEvent_not_elementary
  have qftCount :=
    (QFTCircuit_exact_event_gate_counts
      (FiniteCyclicDLP.orderWidth (problem I))).2.2
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, qftCount]
  have queryZero : ResourcePool.count (.gate (.builtin "swap"))
      (ResourcePool.singleton (uPQEvent I)) = 0 := by simp [uPQEvent]
  rw [queryZero]
  omega

/-- The literal circuit contains exactly one opaque `U_{P,Q}` query. -/
theorem quantumCircuit_uPQEvent_count (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    ResourcePool.count (uPQEvent I)
        (GateLevelAttempt.quantumCircuit I B A).eventCost = 1 := by
  have preparationZero := B.paddedPreparation_count_zero_of_not_elementary
    (problem I) (uPQEvent I) (by
      simpa only [uPQEvent] using
        quantumSubroutineEvent_not_elementary (uPQSubroutineLabel I).quantum)
  have qftZero : ResourcePool.count (uPQEvent I)
      (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost = 0 := by
    simpa only [uPQEvent] using qft_quantumSubroutine_count_zero
      (FiniteCyclicDLP.orderWidth (problem I)) (uPQSubroutineLabel I).quantum
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, qftZero,
    ResourcePool.count_singleton_self, Nat.zero_add, Nat.add_zero]

end

end GateLevelResources
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

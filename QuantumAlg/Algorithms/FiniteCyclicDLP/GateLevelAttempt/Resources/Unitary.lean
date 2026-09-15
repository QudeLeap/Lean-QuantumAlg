/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Unitary

/-!
# Original literal finite-cyclic unitary resources

The original preparation, encoded query and parallel inverse Fourier circuits
retain all original event coordinates and critical-path bounds. These exact
unitary resource statements introduce no allocation, repetition or measurement
wrapper. Actual runtime sampling and paid bank reuse consume them separately.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt

noncomputable section

universe u

variable {G : Type u} [Group G]

open UniformSuperposition

@[simp]
theorem paddedPreparation_eventCost (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (paddedPreparation P B).eventCost = B.algorithm1Circuit.eventCost := by
  simp [paddedPreparation]

@[simp]
theorem exponentPreparationCircuit_eventCost (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (exponentPreparationCircuit P B).eventCost =
      B.algorithm1Circuit.eventCost + B.algorithm1Circuit.eventCost := by
  rw [exponentPreparationCircuit, pairConsecutiveCircuit_eventCost]
  simp

@[simp]
theorem preparationCircuit_eventCost (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (preparationCircuit P B).eventCost =
      B.algorithm1Circuit.eventCost + B.algorithm1Circuit.eventCost := by
  rw [preparationCircuit, withGroupWorkspace_eventCost]
  exact exponentPreparationCircuit_eventCost P B

@[simp]
theorem quantumCircuit_eventCost (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (quantumCircuit P B ux).eventCost =
      (B.algorithm1Circuit.eventCost + B.algorithm1Circuit.eventCost) +
        (ResourcePool.singleton (uxEvent P) +
          (inverseQFTCircuit P).eventCost) := by
  simp [quantumCircuit]

@[simp]
theorem paddedPreparation_evaluatedEventDepth_one
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (paddedPreparation P B).evaluatedEventDepth (fun _ => 1) =
      B.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) := by
  exact B.algorithm1CircuitPadded_evaluatedEventDepth
    (binaryExpansion_width_le_orderWidth P B) (fun _ => 1)

@[simp]
theorem exponentPreparationCircuit_evaluatedEventDepth_one
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (exponentPreparationCircuit P B).evaluatedEventDepth (fun _ => 1) =
      B.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) := by
  unfold UnitaryCircuit.evaluatedEventDepth
  rw [exponentPreparationCircuit, pairConsecutiveCircuit_eventDepth,
    DepthExpr.depthEval_tensor, max_self]
  exact paddedPreparation_evaluatedEventDepth_one P B

@[simp]
theorem preparationCircuit_evaluatedEventDepth_one
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) :
    (preparationCircuit P B).evaluatedEventDepth (fun _ => 1) =
      B.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) := by
  unfold UnitaryCircuit.evaluatedEventDepth
  rw [preparationCircuit, withGroupWorkspace_eventDepth,
    DepthExpr.depthEval_tensor, DepthExpr.depthEval_id, Nat.max_zero]
  exact exponentPreparationCircuit_evaluatedEventDepth_one P B

private theorem inverseQFTCircuit_evaluatedEventDepth_one
    (P : KnownOrderProblem G) :
    (inverseQFTCircuit P).evaluatedEventDepth (fun _ => 1) =
      orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
        orderWidth P / 2 := by
  change DepthExpr.depthEval (fun _ => 1) (inverseQFTCircuit P).eventDepth = _
  rw [inverseQFTCircuit_eventDepth]
  simp only [DepthExpr.depthEval_tensor, DepthExpr.depthEval_id,
    UnitaryCircuit.dagger_eventDepth, DepthExpr.depthEval_inverse, max_self,
    Nat.max_zero]
  exact QFTCircuit_evaluatedEventDepth_of_one (orderWidth P)

/-- One actual quantum attempt has the locked circuit-depth envelope: one
Algorithm-1 preparation layer tree, one encoded group query, and two parallel
inverse Fourier readouts. -/
theorem quantumCircuit_evaluatedEventDepth_one_le
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    (quantumCircuit P B ux).evaluatedEventDepth (fun _ => 1) ≤
      B.depthBound + 1 +
        (orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
          orderWidth P / 2) := by
  rw [quantumCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq,
    preparationCircuit_evaluatedEventDepth_one,
    inverseQFTCircuit_evaluatedEventDepth_one]
  have preparationBound := B.algorithm1Circuit_depth_bound
  change B.algorithm1Circuit.evaluatedEventDepth (fun _ => 1) +
      (1 + (orderWidth P + orderWidth P * (orderWidth P - 1) / 2 +
        orderWidth P / 2)) ≤ _
  omega

private theorem inverseQFTCircuit_eventCost_eq_pair
    (P : KnownOrderProblem G) :
    (inverseQFTCircuit P).eventCost =
      (QFTCircuit (orderWidth P)).eventCost +
        (QFTCircuit (orderWidth P)).eventCost := by
  rw [inverseQFTCircuit, withGroupWorkspace_eventCost,
    pairConsecutiveCircuit_eventCost, UnitaryCircuit.dagger_eventCost]

private theorem algorithm1Circuit_count_zero_of_not_elementary {N : Nat}
    (B : UniformSuperposition.BinaryExpansion N)
    (event : Resource.Event .quantum)
    (notElementary : ¬ UniformSuperposition.elementaryEvent event) :
    ResourcePool.count event B.algorithm1Circuit.eventCost = 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ResourcePool.count_ofList,
    List.count_eq_zero]
  intro member
  exact notElementary
    ((List.forall_iff_forall_mem.mp B.algorithm1Circuit_elementary_trace)
      event member)

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

private theorem quantumSubroutineEvent_ne_gate
    (subroutineLabel : Resource.QuantumSubroutineLabel)
    (gateLabel : Resource.GateLabel) :
    (.quantumSubroutine subroutineLabel : Resource.Event .quantum) ≠
      .gate gateLabel := by
  intro equality
  cases equality

private theorem qft_quantumSubroutine_count_zero (width : Nat)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
        (QFTCircuit width).eventCost = 0 := by
  rw [QFTCircuit_eventCost_eq]
  simp [ResourcePool.count, ResourcePool.singleton,
    quantumSubroutineEvent_ne_gate]

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

/-- The actual preparation-query-readout circuit meets the locked aggregate
one-qubit-gate formula.  The three elementary preparation coordinates are
counted together; the two inverse QFTs contribute exactly `2t` Hadamards. -/
theorem quantumCircuit_singleQubitCost_le
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    UniformSuperposition.singleQubitCost (quantumCircuit P B ux) ≤
      2 * orderWidth P + 2 * B.singleQubitBound := by
  have preparationBound := B.algorithm1Circuit_single_qubit_bound
  rcases QFTCircuit_exact_event_gate_counts (orderWidth P) with
    ⟨qftHadamard, _qftPhase, _qftSwap⟩
  have uxHadamardZero :
      ResourcePool.count (.gate (.builtin "hadamard"))
          (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  have uxXZero :
      ResourcePool.count (.gate (.builtin "x"))
          (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  have uxRotationZero :
      ResourcePool.count UniformSuperposition.rotationYEvent
          (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  unfold UniformSuperposition.singleQubitCost at preparationBound ⊢
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add]
  rw [uxHadamardZero, uxXZero, uxRotationZero,
    qftHadamard, qft_x_count_zero, qft_rotationY_count_zero]
  omega

/-- The literal CNOT count comes only from the two Algorithm-1 preparations. -/
theorem quantumCircuit_cnotCost_le
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    UniformSuperposition.cnotCost (quantumCircuit P B ux) ≤
      2 * B.cnotBound := by
  have preparationBound := B.algorithm1Circuit_cnot_bound
  unfold UniformSuperposition.cnotCost at preparationBound ⊢
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add]
  have uxZero : ResourcePool.count UniformSuperposition.cnotEvent
      (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  rw [uxZero, qft_cnot_count_zero]
  omega

/-- The two parallel inverse QFTs contain exactly the locked number of
controlled-phase gates; Algorithm 1 and the group query contain none. -/
theorem quantumCircuit_controlledPhase_count
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
        (quantumCircuit P B ux).eventCost =
      orderWidth P * (orderWidth P - 1) := by
  have preparationZero :
      ResourcePool.count (.gate qftControlledPhaseLabel)
          B.algorithm1Circuit.eventCost = 0 :=
    algorithm1Circuit_count_zero_of_not_elementary B
      (.gate qftControlledPhaseLabel)
      qftControlledPhaseEvent_not_elementary
  have uxZero :
      ResourcePool.count (.gate qftControlledPhaseLabel)
          (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  have qftCount :=
    (QFTCircuit_exact_event_gate_counts (orderWidth P)).2.1
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, uxZero, qftCount,
    Nat.zero_add]
  simpa [two_mul] using Nat.two_mul_div_two_of_even
    (Nat.even_mul_pred_self (orderWidth P))

/-- The two parallel bit-reversal networks contain exactly two copies of the
standard `floor(t/2)` SWAP schedule. -/
theorem quantumCircuit_swap_count
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ResourcePool.count (.gate (.builtin "swap"))
        (quantumCircuit P B ux).eventCost = 2 * (orderWidth P / 2) := by
  have preparationZero :
      ResourcePool.count (.gate (.builtin "swap"))
          B.algorithm1Circuit.eventCost = 0 :=
    algorithm1Circuit_count_zero_of_not_elementary B
      (.gate (.builtin "swap"))
      swapEvent_not_elementary
  have uxZero :
      ResourcePool.count (.gate (.builtin "swap"))
          (ResourcePool.singleton (uxEvent P)) = 0 :=
    ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) 1
  have qftCount :=
    (QFTCircuit_exact_event_gate_counts (orderWidth P)).2.2
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, uxZero, qftCount,
    Nat.zero_add]
  omega

/-- The complete gate-level circuit contains exactly one encoded group query. -/
theorem quantumCircuit_ux_count
    (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ResourcePool.count (uxEvent P) (quantumCircuit P B ux).eventCost = 1 := by
  have preparationZero :
      ResourcePool.count (uxEvent P) B.algorithm1Circuit.eventCost = 0 :=
    algorithm1Circuit_count_zero_of_not_elementary B (uxEvent P) (by
      simpa only [uxEvent] using quantumSubroutineEvent_not_elementary
        (uxSubroutineLabel P).quantum)
  have qftZero : ResourcePool.count (uxEvent P)
      (QFTCircuit (orderWidth P)).eventCost = 0 := by
    simpa only [uxEvent] using qft_quantumSubroutine_count_zero
      (orderWidth P) (uxSubroutineLabel P).quantum
  rw [quantumCircuit_eventCost, inverseQFTCircuit_eventCost_eq_pair]
  simp only [ResourcePool.count_add, preparationZero, qftZero,
    ResourcePool.count_singleton_self, Nat.zero_add, Nat.add_zero]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Resources.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates

/-!
# Original coordinates on the complete actual ECDLP run

Each real round contributes exactly one opaque query and the original two
inverse Fourier transforms. Allocation, finite measurement, paid cyclic-shift
reset and complete native candidate checking retain their separate labels.
The elementary Hadamard, X, rotation-Y and CNOT coordinates therefore remain
those of the original literal member. This does not omit reset from the total
event or depth budgets, and makes no implementation assumption on the query.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

private theorem range_coordinate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (event : Resource.Event kind) (amount count : Nat)
    (body : Fin count → Circuit ctx ctx)
    (same : ∀ index path, ResourcePool.count event ((body index).resourcePool path) = amount)
    (path : (Circuit.forRange count body).Path) :
    ResourcePool.count event ((Circuit.forRange count body).resourcePool path) =
      count * amount := by
  induction count with
  | zero => simp [Circuit.forRange, Circuit.resourcePool, Circuit.eventTrace,
      ResourcePool.ofList, ResourcePool.count]
  | succ count ih =>
      change ResourcePool.count event (ResourcePool.ofList ((body 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2)) = _
      erw [ResourcePool.ofList_append, ResourcePool.count_add, same,
        ih (fun index => body index.succ) (fun index => same index.succ)]
      simp [Nat.add_mul, Nat.add_comm]

private theorem sampled_coordinate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (event : Resource.Event kind) (outside : ∀ label, event ≠ .classicalOperation label)
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (amount : Nat) (same : ∀ path, ResourcePool.count event (code.resourcePool path) = amount)
    (path : (sampledAttempt code supported curve modulus sample base target).Path) :
    ResourcePool.count event
      ((sampledAttempt code supported curve modulus sample base target).resourcePool path) =
        amount := by
  rw [Circuit.resourcePool, sampledAttempt_eventTrace, ResourcePool.ofList_append,
    ResourcePool.count_add]
  erw [same]
  have bounded := (ResourcePool.le_iff_count.mp
    (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2)) event
  rw [attemptEnvelope_count_eq_zero event outside] at bounded
  erw [Nat.eq_zero_of_le_zero bounded, add_zero]

private theorem tail_coordinate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (event : Resource.Event kind) (outside : ∀ label, event ≠ .classicalOperation label)
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (count amount : Nat)
    (same : ∀ path, ResourcePool.count event (code.resourcePool path) = amount)
    (path : (sampledRecoveryTail code supported count curve modulus sample base target).Path) :
    ResourcePool.count event
      ((sampledRecoveryTail code supported count curve modulus sample base target).resourcePool
        path) = count * amount := by
  rw [Circuit.resourcePool, sampledRecoveryTail_eventTrace, ResourcePool.ofList_append,
    ResourcePool.count_add]
  have loop := range_coordinate event amount count
    (fun _ => sampledAttempt code supported curve modulus sample base target)
    (fun _ => sampled_coordinate event outside code supported curve modulus sample base target
      amount same) path.1.2
  erw [loop]
  simp [ResourcePool.ofList, ResourcePool.count, outside]

private theorem reset_stage_coordinate (event : Resource.Event .quantum)
    (measured : ∀ dimension : ℕ+, event ≠ Circuit.zEvent dimension)
    (shifted : ∀ (dimension : ℕ+) (amount : Fin dimension),
      event ≠ .gate (QuditShift.gateLabel amount))
    (dimension : ℕ+) (value : Fin dimension) :
    ResourcePool.count event (resetStageEnvelope dimension value) = 0 := by
  simp [resetStageEnvelope, ResourcePool.ofList, ResourcePool.count,
    ResourcePool.singleton, measured, shifted, eq_comm]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem reset_coordinate (event : Resource.Event .quantum)
    (measured : ∀ dimension : ℕ+, event ≠ Circuit.zEvent dimension)
    (shifted : ∀ (dimension : ℕ+) (amount : Fin dimension),
      event ≠ .gate (QuditShift.gateLabel amount))
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (path : (reset base noQuantum I).Path) :
    ResourcePool.count event ((reset base noQuantum I).resourcePool path) = 0 := by
  have zeroCount : ResourcePool.count event (resetEnvelope I) = 0 := by
    unfold resetEnvelope
    induction (Finset.univ : Finset (Fin (Layout.totalQubits I))) using Finset.induction_on with
    | empty => simp
    | @insert index rest fresh ih =>
        erw [Finset.sum_insert fresh, ResourcePool.count_add,
          reset_stage_coordinate event measured shifted, ih, zero_add]
  have bounded := (ResourcePool.le_iff_count.mp
    (nativeECDLP_reset_pool_le base noQuantum I path)) event
  rw [zeroCount] at bounded
  exact Nat.eq_zero_of_le_zero bounded

private theorem sample_coordinate (event : Resource.Event .quantum)
    (measured : event ≠ Circuit.zEvent 2)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    ResourcePool.count event ((sample base noQuantum I B A).resourcePool path) =
      ResourcePool.count event (GateLevelAttempt.quantumCircuit I B A).eventCost := by
  rw [Circuit.resourcePool, nativeECDLP_sample_eventTrace, ResourcePool.ofList_append,
    ResourcePool.count_add, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  simp [ResourcePool.ofList_replicate, ResourcePool.count_scale,
    ResourcePool.count_singleton_of_ne measured]

attribute [local irreducible] underPersistent

private theorem recovery_coordinate (event : Resource.Event .quantum)
    (outside : ∀ label, event ≠ .classicalOperation label)
    (measured : ∀ dimension : ℕ+, event ≠ Circuit.zEvent dimension)
    (shifted : ∀ (dimension : ℕ+) (amount : Fin dimension),
      event ≠ .gate (QuditShift.gateLabel amount))
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (prepared : event ≠ (preparation I).event)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ResourcePool.count event
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * ResourcePool.count event (GateLevelAttempt.quantumCircuit I B A).eventCost := by
  have same : ∀ path, ResourcePool.count event
      ((reusedSample base noQuantum I B A).resourcePool path) =
        ResourcePool.count event (GateLevelAttempt.quantumCircuit I B A).eventCost := by
    intro iteration
    change ResourcePool.count event (ResourcePool.ofList
      ((reset base noQuantum I).eventTrace iteration.1 ++
        (sample base noQuantum I B A).eventTrace iteration.2)) = _
    erw [ResourcePool.ofList_append, ResourcePool.count_add,
      reset_coordinate event measured shifted, sample_coordinate event (measured 2), zero_add]
  change ResourcePool.count event (ResourcePool.ofList
    ((allocate base noQuantum I).eventTrace path.1 ++
      (sampledRecoveryTail (reusedSample base noQuantum I B A)
        (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
        (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
        (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)).eventTrace
          path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add, nativeECDLP_allocate_events]
  have tail := tail_coordinate event outside (reusedSample base noQuantum I B A)
    (nativeECDLP_reusedSample_isLocal base noQuantum I B A)
    (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
    (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint) count
    (ResourcePool.count event (GateLevelAttempt.quantumCircuit I B A).eventCost) same path.2
  erw [tail]
  simp [ResourcePool.ofList, ResourcePool.count, prepared]

private theorem gate_coordinate (label : Resource.GateLabel)
    (different : label.name ≠ "qudit-cyclic-shift")
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ResourcePool.count (.gate label)
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * ResourcePool.count (.gate label)
          (GateLevelAttempt.quantumCircuit I B A).eventCost := by
  apply recovery_coordinate (.gate label) (by intro other equality; cases equality)
    (by intro dimension; simp [Circuit.zEvent])
    (fun dimension amount equality => different
      (congrArg Resource.GateLabel.name (Resource.Event.gate.inj equality)))
    base noQuantum I (by intro equality; cases equality) B A count basePoint targetPoint path

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))

/-- Every actual round invokes the original opaque group-action member exactly once. -/
theorem nativeECDLP_recovery_query_count
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ResourcePool.count (uPQEvent I)
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count := by
  have same := recovery_coordinate (uPQEvent I)
    (by intro label; simp [uPQEvent]) (by intro dimension; simp [uPQEvent, Circuit.zEvent])
    (by intro dimension amount; simp [uPQEvent]) base noQuantum I
    (by intro equality; cases equality) B A count basePoint targetPoint path
  simpa only [GateLevelResources.quantumCircuit_uPQEvent_count, mul_one] using same

/-- The original two inverse QFTs contribute their controlled-phase coordinates in every round. -/
theorem nativeECDLP_recovery_controlledPhase_count
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * (FiniteCyclicDLP.orderWidth (problem I) *
          (FiniteCyclicDLP.orderWidth (problem I) - 1)) := by
  simpa only [GateLevelResources.quantumCircuit_controlledPhase_count] using
    gate_coordinate qftControlledPhaseLabel (by decide)
      base noQuantum I B A count basePoint targetPoint path

/-- Both actual bit-reversal networks retain their original SWAP labels. -/
theorem nativeECDLP_recovery_swap_count
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ResourcePool.count (.gate (.builtin "swap"))
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * (2 * (FiniteCyclicDLP.orderWidth (problem I) / 2)) := by
  simpa only [GateLevelResources.quantumCircuit_swap_count] using
    gate_coordinate (.builtin "swap") (by decide)
      base noQuantum I B A count basePoint targetPoint path

/-- The original elementary one-qubit classifier is preserved; reset shifts have separate labels. -/
theorem nativeECDLP_recovery_singleQubit_count_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    GateLevelResources.singleQubitCount
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) ≤
        count * (2 * FiniteCyclicDLP.orderWidth (problem I) + 2 * B.singleQubitBound) := by
  have hadamard := gate_coordinate (.builtin "hadamard") (by decide)
    base noQuantum I B A count basePoint targetPoint path
  have flip := gate_coordinate (.builtin "x") (by decide)
    base noQuantum I B A count basePoint targetPoint path
  have rotation := gate_coordinate (.declared "QuantumAlg.Components.Gate" "rotation-y") (by decide)
    base noQuantum I B A count basePoint targetPoint path
  unfold GateLevelResources.singleQubitCount
  rw [UniformSuperposition.rotationYEvent_eq_gate, hadamard, flip, rotation,
    ← Nat.mul_add, ← Nat.mul_add]
  exact Nat.mul_le_mul_left count (GateLevelResources.quantumCircuit_singleQubitCount_le I B A)

/-- The original literal CNOT allowance applies to the same full recovery execution. -/
theorem nativeECDLP_recovery_cnot_count_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    GateLevelResources.cnotCount
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) ≤
        count * (2 * B.cnotBound) := by
  unfold GateLevelResources.cnotCount
  rw [UniformSuperposition.cnotEvent_eq_gate,
    gate_coordinate (.builtin "cnot") (by decide)]
  exact Nat.mul_le_mul_left count (GateLevelResources.quantumCircuit_cnotCount_le I B A)

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

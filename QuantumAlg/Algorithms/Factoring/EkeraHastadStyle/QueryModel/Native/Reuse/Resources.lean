/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Resources

/-!
# Actual cost of a subsequent sample on the same original bank

Reset contributes its real measurement and correction events before the
original member. Its independent envelope contains both correction choices;
the actual path executes only one choice per wire. The member retains its
original tensor critical path. A gate-only clock charges one extra unit per
bank wire, even though it assigns zero duration to reset measurements.

The exact peak adds the one actual classical scratch to the existing context,
without a second bank. These statements concern one subsequent sample; they
do not identify its depth with a legacy retry contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

/-- Original member and actual result events, without a second quantum preparation. -/
def memberEventBudget (N : Nat) : ResourcePool .quantum :=
  ((ShortDLP.preparationCircuit (parameters N)).eventCost +
    (ResourcePool.singleton (ShortDLP.oracleEvent N (parameters N)) +
      (ShortDLP.readoutCircuit (parameters N)).eventCost)) +
    (measurementBits N • ResourcePool.singleton (Circuit.zEvent 2) +
      ResourcePool.singleton
        (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- The original tensor depth and actual terminal instructions of the in-place member. -/
def memberDuration (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  DepthExpr.depthEval duration
    (.seq (ShortDLP.preparationCircuit (parameters N)).eventDepth
      (.seq (.atom (ShortDLP.oracleEvent N (parameters N)))
        (ShortDLP.readoutCircuit (parameters N)).eventDepth)) +
    (measurementBits N * duration (Circuit.zEvent 2) +
      duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))))

/-- An independent envelope for a real reset followed by the original in-place member. -/
def reuseEventBudget (N : Nat) : ResourcePool .quantum :=
  ZReset.Bank.envelope (ShortDLP.totalQubits (parameters N)) + memberEventBudget N

/-- Arbitrary durations charge every reset before the member's original critical path. -/
def reuseDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  ShortDLP.totalQubits (parameters N) * ZReset.depthEnvelope 2 duration + memberDuration N duration

private theorem resetSequence_gateDepth {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) (duration : Resource.Event .quantum → Nat)
    (measurementZero : ∀ label, duration (.measurement label) = 0)
    (gateOne : ∀ label, duration (.gate label) = 1)
    (path : (ZReset.sequence readouts).Path) :
    (ZReset.sequence readouts).depth duration path = readouts.length := by
  induction readouts with
  | nil => rfl
  | cons head tail ih =>
      change (ZReset.circuit head.wire head.output).depth duration path.1 +
        (ZReset.sequence tail).depth duration path.2 = tail.length + 1
      rw [ZReset.zReset_depth, measurementZero, gateOne, ih]
      omega

private theorem resetScope_depth_le {ctx : RuntimeCtx .quantum}
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (duration : Resource.Event .quantum → Nat) (path : (ZReset.BankScope.code qubits).Path) :
    (ZReset.BankScope.code qubits).depth duration path ≤
      ctx.systemCount * ZReset.depthEnvelope 2 duration := by
  have bound := ZReset.zReset_sequence_depth_le
    (ZReset.Bank.readouts (ZReset.BankScope.zResetBankScope_work_qubits qubits)
      (ZReset.BankScope.scratch ctx)) duration path
  refine bound.trans_eq ?_
  unfold ZReset.sequenceDepthEnvelope ZReset.Bank.readouts
  rw [List.map_ofFn]
  change (List.ofFn (fun wire : Fin ctx.systemCount =>
    ZReset.depthEnvelope (ctx.quantumLayout.wire wire).dimension duration)).sum = _
  simp only [qubits, List.ofFn_const, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem context_width :
    (context base noQuantum N).systemCount = ShortDLP.totalQubits (parameters N) := by
  have count := congrArg List.length (nativeOracle_context_wires base noQuantum N)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using count

private theorem body_events (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).eventTrace path =
      (ShortDLP.circuit (encoding input) (parameterUnit path.1.1)
        (parameterTarget path.1.1)).eventTrace ++
        (List.replicate (measurementBits N) (Circuit.zEvent 2) ++
          [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]) := by
  change (member N (nativeOracle_context_wires base noQuantum N) input path.1.1).eventTrace ++
    ((Circuit.measurementSequence (readouts base noQuantum N)).eventTrace path.2.1 ++
      [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]) = _
  rw [readouts_events]
  simp only [member, UnitaryCircuit.reindex_eventTrace]

private theorem body_pool (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).resourcePool path = memberEventBudget N := by
  rw [Circuit.resourcePool, body_events]
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons,
    ResourcePool.ofList_nil, add_zero,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, ShortDLP.circuit_eventCost,
    ResourcePool.ofList_replicate, ResourcePool.scale, memberEventBudget]

private theorem body_depth (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event .quantum → Nat)
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).depth duration path = memberDuration N duration := by
  change DepthExpr.depthEval duration
    (member N (nativeOracle_context_wires base noQuantum N) input path.1.1).eventDepth +
      ((Circuit.measurementSequence (readouts base noQuantum N)).depth duration path.2.1 +
        duration (.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N))))) = _
  rw [readouts_duration]
  simp only [member, UnitaryCircuit.reindex_eventDepth, ShortDLP.circuit_eventDepth, memberDuration]

private theorem body_visited (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (body base noQuantum N input parameter).visitedContexts path) :
    frame = context base noQuantum N := by
  change frame ∈ [context base noQuantum N] ++
    ((Circuit.measurementSequence (readouts base noQuantum N)).visitedContexts path.2.1 ++
      [context base noQuantum N]) at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with same | measured | same
  · exact same
  · exact (List.mem_replicate.mp measured).2
  · exact same

private theorem body_resident (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).peakResidentSpace path =
      (context base noQuantum N).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N input parameter path frame present]
  · exact Circuit.output_residentSpace_le_peak _ path

private theorem body_auxiliary (input : Input N) (parameter : CInputRef base (ParameterShape N))
    (path : (body base noQuantum N input parameter).Path) :
    (body base noQuantum N input parameter).peakAuxiliarySpace path =
      (context base noQuantum N).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rw [body_visited base noQuantum N input parameter path frame present]
  · exact Circuit.output_auxiliarySpace_le_peak _ path

/-- The exact reset trace precedes the actual parameter-selected original sampler trace. -/
theorem nativeOracle_reuse_eventTrace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).eventTrace path =
      (resetBank base noQuantum N).eventTrace path.1 ++
        (ShortDLP.circuit (encoding input) (parameterUnit path.2.1.1)
          (parameterTarget path.2.1.1)).eventTrace ++
        (List.replicate (measurementBits N) (Circuit.zEvent 2) ++
          [.classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))]) := by
  change (resetBank base noQuantum N).eventTrace path.1 ++
    (body base noQuantum N input parameter).eventTrace path.2 = _
  rw [body_events, List.append_assoc]

/-- A reset executes two real events per existing original-bank qubit. -/
theorem nativeOracle_resetBank_eventTrace_length (path : (resetBank base noQuantum N).Path) :
    ((resetBank base noQuantum N).eventTrace path).length =
      2 * ShortDLP.totalQubits (parameters N) :=
  (ZReset.BankScope.zResetBankScope_eventTrace_length _ path).trans
    (congrArg (2 * ·) (context_width base noQuantum N))

/-- The independent reset alternatives bound the same actual path before the original member. -/
theorem nativeOracle_reuse_resourcePool_le (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).resourcePool path ≤ reuseEventBudget N := by
  change (resetBank base noQuantum N).resourcePool path.1 +
    (body base noQuantum N input parameter).resourcePool path.2 ≤ _
  rw [body_pool]
  have reset := ZReset.BankScope.zResetBankScope_resourcePool_le
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)) path.1
  rw [context_width] at reset
  exact add_le_add reset (le_refl (memberEventBudget N))

/-- Arbitrary durations retain the actual reset prefix and the original tensor member depth. -/
theorem nativeOracle_reuse_depth (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) (duration : Resource.Event .quantum → Nat)
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).depth duration path =
      (resetBank base noQuantum N).depth duration path.1 + memberDuration N duration := by
  change (resetBank base noQuantum N).depth duration path.1 +
    (body base noQuantum N input parameter).depth duration path.2 = _
  rw [body_depth]

/-- A duration-independent set of actual correction alternatives supplies a uniform bound. -/
theorem nativeOracle_reuse_depth_le (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) (duration : Resource.Event .quantum → Nat)
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).depth duration path ≤
      reuseDurationBudget N duration := by
  rw [nativeOracle_reuse_depth]
  have reset := resetScope_depth_le
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)) duration path.1
  rw [context_width] at reset
  exact Nat.add_le_add_right reset _

/-- Charging gates by one and measurements by zero still charges every reset correction. -/
theorem nativeOracle_reuse_gateDepth (input : Input N)
    (parameter : CInputRef base (ParameterShape N)) (duration : Resource.Event .quantum → Nat)
    (measurementZero : ∀ label, duration (.measurement label) = 0)
    (gateOne : ∀ label, duration (.gate label) = 1)
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).depth duration path =
      ShortDLP.totalQubits (parameters N) + memberDuration N duration := by
  rw [nativeOracle_reuse_depth]
  apply congrArg (fun value => value + memberDuration N duration)
  exact (resetSequence_gateDepth _ duration measurementZero gateOne path.1).trans
    ((ZReset.Bank.zResetBank_readouts_length _ _).trans (context_width base noQuantum N))

/-- The reset scope adds exactly one live finite cell to the unchanged resident bank. -/
theorem nativeOracle_reuse_peakResidentSpace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).peakResidentSpace path =
      SpacePool.ofShape (.finite 2) + (context base noQuantum N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq (resetBank base noQuantum N)
    (body base noQuantum N input parameter) path).trans ?_
  rw [body_resident]
  have reset := ZReset.BankScope.zResetBankScope_peakResidentSpace
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)) path.1
  refine (congrArg (fun value => SpacePool.max value
    (context base noQuantum N).residentSpace) reset).trans ?_
  apply SpacePool.ext
  intro axis
  exact max_eq_left (Nat.le_add_left _ _)

/-- The same actual scratch is counted once as auxiliary space and then popped. -/
theorem nativeOracle_reuse_peakAuxiliarySpace (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).peakAuxiliarySpace path =
      SpacePool.ofShape (.finite 2) + (context base noQuantum N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (resetBank base noQuantum N)
    (body base noQuantum N input parameter) path).trans ?_
  rw [body_auxiliary]
  have reset := ZReset.BankScope.zResetBankScope_peakAuxiliarySpace
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)) path.1
  refine (congrArg (fun value => SpacePool.max value
    (context base noQuantum N).auxiliarySpace) reset).trans ?_
  apply SpacePool.ext
  intro axis
  exact max_eq_left (Nat.le_add_left _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

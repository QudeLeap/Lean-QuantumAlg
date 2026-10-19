/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Resources
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf

/-!
# Exact quantum duration and retained work of the two reset batches

Only the selected X members contribute quantum duration. Each batch has
zero duration if every stored outcome is zero, and one otherwise. The
maximum over the actual circuit paths is two for a nonempty bank and zero
for an empty bank. Every one of the 2n measurements and each selected X
remains in the native event ledger.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

variable {allowAllocation : Bool} {oracles : OracleModel}

private lemma pure_time {width : Nat} {physical : QuantumLayout width}
    (body : UnitarySequence AlgorithmGate.model oracles physical) :
    DepthExpr.depthEval Resource.Event.quantumDuration (body.eventDepth BitWord.model .empty) =
      DepthExpr.depthEval (fun _ => 1) body.eventDepth := by
  induction body with
  | id => rfl
  | leaf value => cases value <;> rfl
  | seq left right leftIH rightIH => simp [UnitarySequence.eventDepth, leftIH, rightIH]
  | embed placement body bodyIH => exact bodyIH
  | parallel left right leftPlacement rightPlacement disjoint leftIH rightIH =>
      simp [UnitarySequence.eventDepth, leftIH, rightIH]
  | iterate repetitions body bodyIH => simp [UnitarySequence.eventDepth, bodyIH]
  | indexedProduct label steps start step startIH stepIH =>
      simp [UnitarySequence.eventDepth, startIH, stepIH]
  | macroCall name body bodyIH => exact bodyIH

private lemma last_depth (width : Nat) (selected : Bool) :
    (ZReset.BankParallel.Correction.last oracles width selected).evaluatedEventDepth
      (fun _ => 1) = if selected then 1 else 0 := by
  cases selected <;> rfl

private lemma layer_depth (width : Nat) (selected : Fin width → Bool) :
    (ZReset.BankParallel.Correction.layer oracles width selected).evaluatedEventDepth
      (fun _ => 1) =
        if ZReset.BankParallel.Correction.xCount width selected = 0 then 0 else 1 := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [ZReset.BankParallel.Correction.layer, UnitaryCircuit.castLayout_evaluatedEventDepth,
        UnitaryCircuit.tensor_native_evaluatedEventDepth, ih, last_depth,
        ZReset.BankParallel.Correction.xCount]
      cases selected (Fin.last width) <;>
        cases ZReset.BankParallel.Correction.xCount width
          (fun index => selected index.castSucc) <;> simp

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- A single stored outcome vector determines exactly zero or one actual quantum layer. -/
lemma batch_quantumTime
    (half : Fin 2) (path : (batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).Path) :
    (batch (allowAllocation := allowAllocation) base noQuantum n count half).quantumTime path =
      if ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.2.1) = 0 then 0 else 1 :=
        by
  have measured : (measure (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).quantumTime path.1 = 0 := by
    refine (Circuit.measurementSequence_depth (allowAllocation := allowAllocation)
      (readouts base noQuantum n count half) Resource.Event.quantumDuration path.1).trans ?_
    simp [Circuit.zEvent, Resource.Event.quantumDuration]
  change (measure (allowAllocation := allowAllocation) base noQuantum n count half).quantumTime
    path.1 + DepthExpr.depthEval Resource.Event.quantumDuration
      ((correction (oracles := oracles) base noQuantum n count half path.2.1).sequence.eventDepth
        BitWord.model .empty) = _
  rw [measured, Nat.zero_add, pure_time]
  change (correction (oracles := oracles) base noQuantum n count half path.2.1).evaluatedEventDepth
    (fun _ => 1) = _
  rw [correction, UnitaryCircuit.placeAt_evaluatedEventDepth, layer_depth]

/-- The two reused-cell batches add their actual selected parallel-layer durations. -/
lemma code_quantumTime
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).quantumTime path =
      (if ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.1.2.1) = 0
        then 0 else 1) +
      (if ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.2.2.1) = 0
        then 0 else 1) :=
        by
  change (batch (allowAllocation := allowAllocation) base noQuantum n count 0).quantumTime path.1 +
    (batch (allowAllocation := allowAllocation) base noQuantum n count 1).quantumTime path.2 = _
  rw [batch_quantumTime, batch_quantumTime]

private lemma all_selected_count (width : Nat) :
    ZReset.BankParallel.Correction.xCount width (fun _ => true) = width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [ZReset.BankParallel.Correction.xCount, ih]

/-- Every requested real quantum layer can occur on a path measuring both all-one registers. -/
lemma code_quantumTime_maximum :
    ∃ path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path,
      (code (allowAllocation := allowAllocation) base noQuantum n count).quantumTime path =
        if n = 0 then 0 else 2 := by
  let ones : (context base noQuantum n count).register.Index := fun wire =>
    Fin.cast (congrArg Subtype.val
      (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count) wire).symm)
      (1 : Fin 2)
  let value : CShape.Value (.fixedVector n (.finite 2)) := .fixedVector fun _ => .finite 1
  let measured (half : Fin 2) := Circuit.measurementBasisPath
    (allowAllocation := allowAllocation) (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := .empty)
    (readouts base noQuantum n count half) ones
  refine ⟨((measured 0, ⟨value, ()⟩), (measured 1, ⟨value, ()⟩)), ?_⟩
  rw [code_quantumTime]
  change (if ZReset.BankParallel.Correction.xCount n (fun _ => true) = 0 then 0 else 1) +
    (if ZReset.BankParallel.Correction.xCount n (fun _ => true) = 0 then 0 else 1) = _
  rw [all_selected_count]
  split_ifs <;> rfl

/-- The canonical maximum observes precisely the same implementation's complete path type. -/
lemma code_quantumTime_isGreatest :
    IsGreatest (Set.range (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).quantumTime) (if n = 0 then 0 else 2) := by
  constructor
  · exact code_quantumTime_maximum base noQuantum n count
  · rintro time ⟨path, rfl⟩
    exact code_quantumTime_le base noQuantum n count path

/-- Total native work retains the 2n measurements and exactly the selected X occurrences. -/
lemma code_eventCount
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    ((code (allowAllocation := allowAllocation) base noQuantum n count).eventTrace path).length =
      2 * n + ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.1.2.1) +
        ZReset.BankParallel.Correction.xCount n (QubitReadouts.mask path.2.2.1) := by
  have counted := congrArg (ResourcePool.weightedCount (fun _ => 1))
    (code_resourcePool (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count path)
  simpa [Circuit.resourcePool, Nat.add_assoc] using counted

/-- The original serial work allowance remains a valid bound on all retained native events. -/
lemma code_eventCount_le
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    ((code (allowAllocation := allowAllocation) base noQuantum n count).eventTrace path).length ≤
      4 * n := by
  rw [code_eventCount]
  have first := ZReset.BankParallel.Correction.xCount_le n (QubitReadouts.mask path.1.2.1)
  have second := ZReset.BankParallel.Correction.xCount_le n (QubitReadouts.mask path.2.2.1)
  omega

/-- A retained coarse unit-event bound charges the measured work without claiming exact duration.
-/
lemma code_unitDepth_le
    (path : (code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).Path) :
    (code (allowAllocation := allowAllocation) base noQuantum n count).depth (fun _ => 1) path ≤
      4 * n := by
  have bounded := Circuit.depth_le_weightedCount_of_pool_le
    (code (allowAllocation := allowAllocation) (oracles := oracles) base noQuantum n count)
    (fun _ => 1) _ path (code_resourcePool_le base noQuantum n count path)
  simp only [ZReset.Bank.envelope, ZReset.eventEnvelope, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton, Nat.mul_one] at bounded
  omega

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

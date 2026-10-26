/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Actual hybrid selector weighted ledger and quantum depth

Every real native fork contributes two X, two Toffoli and one CNOT events.
Classical callbacks retain their actual branch-dependent resource pools;
uniform callback bounds sum over the retained static leaves. Quantum time
uses the real callback depth, preserving its internal physical parallelism.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

/-- The paid actual five native events of one hybrid selector fork. -/
def hybridForkWeight
    (weight : Resource.Event (.quantum AlgorithmGate.model oracles operations services) → Nat) :
    Nat :=
  2 * weight (.gate .singleQubit) + 2 * weight (.gate .toffoli) + weight (.gate .cnot)

/-- Every actual retained hybrid callback contributes its own weighted native ledger. -/
lemma circuitAt_weight_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (weight : Resource.Event (.quantum AlgorithmGate.model oracles operations services) → Nat)
    (bound : Nat) (callbackBound : ∀ label path,
      ResourcePool.weightedCount weight ((callback label).resourcePool path) ≤ bound)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (path : (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path) :
    ResourcePool.weightedCount weight
      ((frame.circuitAt physical sameWires callback tree depth fits offset bounded).resourcePool
        path) ≤ tree.forks * hybridForkWeight weight + tree.leaves * bound := by
  induction tree generalizing depth offset with
  | skip remaining => simp [circuitAt, Circuit.resourcePool, Circuit.eventTrace,
      SelectorTrie.forks, SelectorTrie.leaves]
  | leaf => simpa only [circuitAt, SelectorTrie.forks, SelectorTrie.leaves,
      Nat.zero_mul, Nat.one_mul, Nat.zero_add] using callbackBound _ path
  | @fork remaining left right leftIH rightIH =>
      dsimp only [circuitAt, placedCircuit, Circuit.Path] at path
      have leftBound := leftIH (depth + 1) (by omega) offset (left_bound bounded) path.2.1
      have rightBound := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded) path.2.2.2.1
      change ResourcePool.weightedCount weight
        (ResourcePool.ofList (_ ++ (_ ++ (_ ++ (_ ++ _))))) ≤ _
      simp only [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
      have firstEvents : (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (GateSpec.programList physical oracles (frame.leftGates depth (by omega)))).eventTrace
            operations services = [.gate .singleQubit, .gate .toffoli, .gate .singleQubit] := rfl
      have nextEvents : (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.nextGate depth (by omega)).program physical oracles)).eventTrace
            operations services = [.gate .cnot] := rfl
      have clearEvents : (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.clearGate depth (by omega)).program physical oracles)).eventTrace
            operations services = [.gate .toffoli] := rfl
      simp only [placedCircuit, Circuit.eventTrace, firstEvents, nextEvents, clearEvents,
        ResourcePool.weightedCount_ofList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      dsimp only [SelectorTrie.forks, SelectorTrie.leaves]
      dsimp only [hybridForkWeight]
      dsimp only [hybridForkWeight, Circuit.resourcePool] at leftBound rightBound
      rw [ResourcePool.weightedCount_ofList] at leftBound rightBound
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- The actual quantum schedule charges the native forks and actual callback quantum depths. -/
lemma circuitAt_quantumTime_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (bound : Nat) (callbackBound : ∀ label path,
      (callback label).depth Resource.Event.quantumDuration path ≤ bound)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (path : (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path) :
    (frame.circuitAt physical sameWires callback tree depth fits offset bounded).depth
      Resource.Event.quantumDuration path ≤ 5 * tree.forks + tree.leaves * bound := by
  induction tree generalizing depth offset with
  | skip remaining => simp [circuitAt, Circuit.depth, Circuit.eventDepth,
      SelectorTrie.forks, SelectorTrie.leaves]
  | leaf => simpa only [circuitAt, SelectorTrie.forks, SelectorTrie.leaves,
      Nat.mul_zero, Nat.one_mul, Nat.zero_add] using callbackBound _ path
  | @fork remaining left right leftIH rightIH =>
      dsimp only [circuitAt, placedCircuit, Circuit.Path] at path
      have leftBound := leftIH (depth + 1) (by omega) offset (left_bound bounded) path.2.1
      have rightBound := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded) path.2.2.2.1
      change 3 + (_ + (1 + (_ + 1))) ≤ _
      dsimp only [SelectorTrie.forks, SelectorTrie.leaves]
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul]
      dsimp only [Circuit.depth] at leftBound rightBound
      omega

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

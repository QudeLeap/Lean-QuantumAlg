/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Pruning

/-!
# Resources derived from the actual pruned unitary selector

The native traversal charges exactly two Toffolis, one CNOT and two X gates
per retained fork, together with each actual retained callback. Callback
depth may include physical parallel layers; it is taken from that circuit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

namespace SelectorTrie

/-- Sum a cost over the actual full-width static leaves retained by this trie. -/
def leafSumAt (width : Nat) (cost : Fin (2 ^ width) → Nat) :
    {remaining : Nat} → SelectorTrie remaining → (offset : Nat) →
      offset + 2 ^ remaining ≤ 2 ^ width → Nat
  | _, .skip _, _, _ => 0
  | 0, .leaf, offset, bounded =>
      cost ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩
  | remaining + 1, .fork left right, offset, bounded =>
      leafSumAt width cost left offset (SelectorFrame.left_bound bounded) +
        leafSumAt width cost right (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded)

/-- Sum only the retained original labels; skipped labels incur no callback cost. -/
def leafSum {width : Nat} (tree : SelectorTrie width) (cost : Fin (2 ^ width) → Nat) : Nat :=
  leafSumAt width cost tree 0 (by omega)

/-- A uniform callback bound is charged once per retained static leaf. -/
lemma leafSumAt_le {width remaining : Nat} (tree : SelectorTrie remaining)
    (cost : Fin (2 ^ width) → Nat) (bound : Nat) (boundedCost : ∀ label, cost label ≤ bound)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    leafSumAt width cost tree offset bounded ≤ tree.leaves * bound := by
  induction tree generalizing offset with
  | skip remaining => simp only [leafSumAt, leaves, Nat.zero_mul, Nat.le_refl]
  | leaf => simpa only [leafSumAt, leaves, Nat.one_mul] using boundedCost _
  | @fork remaining left right leftIH rightIH =>
      dsimp only [leafSumAt, leaves]
      rw [Nat.add_mul]
      exact Nat.add_le_add (leftIH _ (SelectorFrame.left_bound bounded))
        (rightIH _ (SelectorFrame.right_bound bounded))

end SelectorTrie

/-- Literal selected-coordinate multiplicity of one actual five-gate fork. -/
def selectorForkCount (oracles : OracleModel)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles)) : Nat :=
  2 * (if (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model oracles)) = focus
    then 1 else 0) +
    2 * (if (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model oracles)) = focus
      then 1 else 0) +
    (if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model oracles)) = focus
      then 1 else 0)

namespace SelectorFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma fork_native_count (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    (depth : Nat) (present : depth < width) :
    ResourcePool.count focus (GateSpec.programList physical oracles
      (frame.leftGates depth present)).eventCost +
        ResourcePool.count focus
          ((frame.nextGate depth present).program physical oracles).eventCost +
        ResourcePool.count focus
          ((frame.clearGate depth present).program physical oracles).eventCost =
          selectorForkCount oracles focus := by
  have xEvent (bit : EncodedBit encoding) :
      GateSpec.event oracles (.x bit) = .gate .singleQubit := rfl
  have cnotEvent (first second : EncodedBit encoding) (different : first.wire ≠ second.wire) :
      GateSpec.event oracles (.cnot first second different) = .gate .cnot := rfl
  have toffoliEvent (first second target : EncodedBit encoding)
      (different : first.wire ≠ second.wire) (firstTarget : first.wire ≠ target.wire)
      (secondTarget : second.wire ≠ target.wire) :
      GateSpec.event oracles (.toffoli first second target different firstTarget secondTarget) =
        .gate .toffoli := rfl
  simp only [leftGates, nextGate, clearGate, GateSpec.programList_eventCost,
    GateSpec.program_eventCost, List.map_cons, List.map_nil, xEvent, cnotEvent, toffoliEvent,
    ResourcePool.ofList_cons, ResourcePool.ofList_nil, ResourcePool.count_add,
    ResourcePool.count_singleton, ResourcePool.count_zero, selectorForkCount]
  omega

/-- Every native count comes from the same actual selector and retained callback circuits. -/
lemma programAt_event_count (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    ResourcePool.count focus
      (frame.programAt physical oracles callback tree depth fits offset bounded).eventCost =
        tree.forks * selectorForkCount oracles focus +
          SelectorTrie.leafSumAt width (fun label =>
            ResourcePool.count focus (callback label).eventCost) tree offset bounded := by
  induction tree generalizing depth offset with
  | skip remaining =>
      simp only [programAt, SelectorTrie.forks, SelectorTrie.leafSumAt,
        UnitaryCircuit.identity_eventCost, ResourcePool.count_zero, zero_mul, zero_add]
  | leaf => simp only [programAt, SelectorTrie.forks, SelectorTrie.leafSumAt, zero_mul, zero_add]
  | @fork remaining left right leftIH rightIH =>
      dsimp only [programAt]
      simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
      rw [leftIH, rightIH]
      have native := frame.fork_native_count physical oracles focus depth (by omega)
      dsimp only [SelectorTrie.forks, SelectorTrie.leafSumAt]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

/-- The complete original address interval retains this exact coordinate count. -/
lemma program_event_count (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (tree : SelectorTrie width) (focus : Resource.Event (.quantum AlgorithmGate.model oracles)) :
    ResourcePool.count focus (frame.program physical oracles callback tree).eventCost =
      tree.forks * selectorForkCount oracles focus +
        tree.leafSum (fun label => ResourcePool.count focus (callback label).eventCost) :=
  frame.programAt_event_count physical oracles callback focus tree 0 (by omega) 0 (by omega)

/-- Quantum duration uses each actual callback's dependence depth, including parallel layers. -/
lemma programAt_quantumTime (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (frame.programAt physical oracles callback tree depth fits offset bounded) =
        5 * tree.forks + SelectorTrie.leafSumAt width (fun label =>
          (callback label).evaluatedEventDepth Resource.Event.quantumDuration)
            tree offset bounded := by
  induction tree generalizing depth offset with
  | skip remaining => rfl
  | leaf => simp only [programAt, SelectorTrie.forks, SelectorTrie.leafSumAt, mul_zero, zero_add]
  | @fork remaining left right leftIH rightIH =>
      have leftTime : (GateSpec.programList physical oracles
          (frame.leftGates depth (by omega))).evaluatedEventDepth Resource.Event.quantumDuration =
            3 := rfl
      have nextTime : UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
          ((frame.nextGate depth (by omega)).program physical oracles) = 1 := rfl
      have clearTime : UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
          ((frame.clearGate depth (by omega)).program physical oracles) = 1 := rfl
      dsimp only [programAt]
      simp only [UnitaryCircuit.evaluatedEventDepth_seq]
      rw [leftTime, nextTime, clearTime, leftIH, rightIH]
      dsimp only [SelectorTrie.forks, SelectorTrie.leafSumAt]
      omega

/-- The total native quantum time is the traversal plus the original physical callbacks. -/
lemma program_quantumTime (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (tree : SelectorTrie width) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (frame.program physical oracles callback tree) =
      5 * tree.forks + tree.leafSum (fun label =>
        (callback label).evaluatedEventDepth Resource.Event.quantumDuration) :=
  frame.programAt_quantumTime physical oracles callback tree 0 (by omega) 0 (by omega)

end SelectorFrame

end

end QuantumAlg.EncodedBit.WindowLookup

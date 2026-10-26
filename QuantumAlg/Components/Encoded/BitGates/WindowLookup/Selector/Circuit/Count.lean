/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Resources

/-!
# Literal gate coordinates of the actual hybrid selector

Indicator weights recover the strict native coordinate count of the same
actual resource pool. Each fork retains its two X, two Toffoli and one CNOT
occurrences, plus every original retained callback's proved gate bound.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

private lemma weightedIndicator {model : ExecutionModel} (focus : Resource.Event model)
    (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun event => if event = focus then 1 else 0) pool =
      ResourcePool.count focus pool := by
  classical
  induction pool using Multiset.induction_on with
  | empty => rfl
  | cons event rest ih =>
      simp only [ResourcePool.weightedCount, Multiset.map_cons, Multiset.sum_cons,
        ResourcePool.count, Multiset.count_cons]
      rw [show (rest.map (fun event => if event = focus then 1 else 0)).sum =
        Multiset.count focus rest from ih]
      by_cases same : event = focus
      · simp [same, Nat.add_comm]
      · simp [same, Ne.symm same]

/-- The exact literal coordinate multiplicity of one actual native selector fork. -/
def hybridGateForkCount (coordinate : AlgorithmGate.Coordinate) : Nat :=
  2 * (if AlgorithmGate.Coordinate.singleQubit = coordinate then 1 else 0) +
    2 * (if AlgorithmGate.Coordinate.toffoli = coordinate then 1 else 0) +
    (if AlgorithmGate.Coordinate.cnot = coordinate then 1 else 0)

/-- Actual gate coordinates are bounded by the real forks and every retained actual callback. -/
lemma circuitAt_gate_count_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (coordinate : AlgorithmGate.Coordinate) (bound : Nat)
    (callbackBound : ∀ label path, ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate coordinate)
      ((callback label).resourcePool path) ≤ bound)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (path : (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles operations services) (.gate coordinate)
      ((frame.circuitAt physical sameWires callback tree depth fits offset bounded).resourcePool
        path) ≤ tree.forks * hybridGateForkCount coordinate + tree.leaves * bound := by
  have actual := frame.circuitAt_weight_le physical sameWires callback
    (fun event => if event = .gate coordinate then 1 else 0) bound
    (fun label current => by rw [weightedIndicator]; exact callbackBound label current)
    tree depth fits offset bounded path
  simp only [weightedIndicator, hybridForkWeight] at actual
  have gateEq (first second : AlgorithmGate.Coordinate) :
      (Resource.Event.gate first :
        Resource.Event (.quantum AlgorithmGate.model oracles operations services)) =
          .gate second ↔ first = second :=
    ⟨Resource.Event.gate.inj, fun same => by cases same; rfl⟩
  simpa only [gateEq, hybridGateForkCount] using actual

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

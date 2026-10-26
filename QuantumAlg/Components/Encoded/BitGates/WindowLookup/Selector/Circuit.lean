/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Trace

/-!
# Allocation-free selectors with actual hybrid leaf programs

Every retained leaf is an actual circuit on the supplied existing context.
In particular, native classical parity instructions and stored-result branches
remain inside that circuit. The selector introduces only its original five
native gates per fork on the same ordered physical wire records.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

namespace SelectorFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Place an actual native word on exactly the same complete ordered physical wires. -/
def placedCircuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  .unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program)

/-- Retain each actual hybrid callback without permitting any child allocation. -/
def circuitAt (frame : SelectorFrame encoding width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false) :
    {remaining : Nat} → (tree : SelectorTrie remaining) →
      (depth : Nat) → depth + remaining = width →
      (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width →
        Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false
  | _, .skip _, _, _, _, _ =>
      .id (model := .quantum AlgorithmGate.model oracles operations services) ctx
  | 0, .leaf, _, _, offset, bounded =>
      callback ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩
  | remaining + 1, .fork left right, depth, fits, offset, bounded =>
      let present : depth < width := by omega
      (placedCircuit physical sameWires
        (GateSpec.programList physical oracles (frame.leftGates depth present))).seq
        ((frame.circuitAt physical sameWires callback left (depth + 1) (by omega)
          offset (left_bound bounded)).seq
          ((placedCircuit physical sameWires
            ((frame.nextGate depth present).program physical oracles)).seq
            ((frame.circuitAt physical sameWires callback right (depth + 1) (by omega)
              (offset + 2 ^ remaining) (right_bound bounded)).seq
                (placedCircuit physical sameWires
                  ((frame.clearGate depth present).program physical oracles)))))

/-- The original complete address interval selects actual allocation-free hybrid leaves. -/
def circuit (frame : SelectorFrame encoding width) (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (tree : SelectorTrie width) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false :=
  frame.circuitAt physical sameWires callback tree 0 (by omega) 0 (by omega)

private lemma fork_trace_lengths (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (depth : Nat) (present : depth < width) :
    ((placedCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires (GateSpec.programList physical oracles
        (frame.leftGates depth present))).eventTrace ()).length = 3 ∧
    ((placedCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires ((frame.nextGate depth present).program physical oracles)).eventTrace
        ()).length = 1 ∧
    ((placedCircuit (oracles := oracles) (operations := operations) (services := services)
      physical sameWires ((frame.clearGate depth present).program physical oracles)).eventTrace
        ()).length = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Every actual path pays for all native forks and all retained hybrid callbacks. -/
lemma circuitAt_trace_length_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (bound : Nat) (callbackBound : ∀ label path, ((callback label).eventTrace path).length ≤ bound)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (path : (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path) :
    ((frame.circuitAt physical sameWires callback tree depth fits offset bounded).eventTrace
      path).length ≤ 5 * tree.forks + tree.leaves * bound := by
  induction tree generalizing depth offset with
  | skip remaining =>
      simp only [circuitAt, Circuit.eventTrace, List.length_nil, SelectorTrie.forks,
        SelectorTrie.leaves, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.le_refl]
  | leaf => simpa only [circuitAt, SelectorTrie.forks, SelectorTrie.leaves,
      Nat.mul_zero, Nat.one_mul, Nat.zero_add] using callbackBound _ path
  | @fork remaining left right leftIH rightIH =>
      have native := frame.fork_trace_lengths (oracles := oracles) (operations := operations)
        (services := services) physical sameWires depth (by omega)
      dsimp only [circuitAt, placedCircuit, Circuit.Path] at path
      have leftBound := leftIH (depth + 1) (by omega) offset (left_bound bounded) path.2.1
      have rightBound := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded) path.2.2.2.1
      change List.length (_ ++ (_ ++ (_ ++ (_ ++ _)))) ≤ _
      simp only [List.length_append]
      have firstPath : path.1 = () := Subsingleton.elim _ _
      have nextPath : path.2.2.1 = () := Subsingleton.elim _ _
      have clearPath : path.2.2.2.2 = () := Subsingleton.elim _ _
      simp only [firstPath, nextPath, clearPath, native.1, native.2.1, native.2.2]
      dsimp only [SelectorTrie.forks, SelectorTrie.leaves]
      rw [Nat.add_mul]
      omega

end SelectorFrame

end

end QuantumAlg.EncodedBit.WindowLookup

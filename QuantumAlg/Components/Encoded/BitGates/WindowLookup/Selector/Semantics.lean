/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.FrameLaws

/-!
# Exact operator bridge for the actual pruned selector word

The complete operational action is derived from the actual finite native
syntax and the actual leaf programs. Clean-prefix selection is a separate
semantic law; no dirty input is silently identified with a clean one.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Complete all-input action in the same order as the actual subtree program. -/
def stepAt (frame : SelectorFrame encoding width)
    (callbackStep : Fin (2 ^ width) → Data → Data) :
    {remaining : Nat} → (tree : SelectorTrie remaining) →
      (depth : Nat) → depth + remaining = width →
      (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width → Data → Data
  | _, .skip _, _, _, _, _, state => state
  | 0, .leaf, _, _, offset, bounded, state =>
      callbackStep ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ state
  | remaining + 1, .fork left right, depth, fits, offset, bounded, state =>
      let present : depth < width := by omega
      (frame.clearGate depth present).step
        (frame.stepAt callbackStep right (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded)
          ((frame.nextGate depth present).step
            (frame.stepAt callbackStep left (depth + 1) (by omega) offset (left_bound bounded)
              (GateSpec.stepList (frame.leftGates depth present) state))))

/-- Every actual native subtree has this exact full encoded action, with no phase quotient. -/
lemma programAt_realizes (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (callbackStep : Fin (2 ^ width) → Data → Data) (environment : oracles.Interpretation)
    (callbacks : ∀ label, UnitaryCircuit.Realizes encoding (callback label) environment
      (callbackStep label)) {remaining : Nat} (tree : SelectorTrie remaining)
    (depth : Nat) (fits : depth + remaining = width)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    UnitaryCircuit.Realizes encoding
      (frame.programAt physical oracles callback tree depth fits offset bounded) environment
      (frame.stepAt callbackStep tree depth fits offset bounded) := by
  induction tree generalizing depth offset with
  | skip remaining =>
      refine ⟨fun state => ?_⟩
      exact (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model oracles
        encoding physical environment).apply_encoded_ket state
  | leaf => exact callbacks _
  | @fork remaining left right leftIH rightIH =>
      refine ⟨fun state => ?_⟩
      simp only [programAt, UnitaryCircuit.applyNormalized_seq]
      rw [(GateSpec.realizesList physical oracles (frame.leftGates depth (by omega))
        environment).apply_encoded_ket]
      rw [(leftIH (depth + 1) (by omega) offset (left_bound bounded)).apply_encoded_ket]
      rw [(GateSpec.realizes physical oracles (frame.nextGate depth (by omega))
        environment).apply_encoded_ket]
      rw [(rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded)).apply_encoded_ket]
      rw [(GateSpec.realizes physical oracles (frame.clearGate depth (by omega))
        environment).apply_encoded_ket]
      rfl

/-- The actual whole static traversal is tied to the complete all-input native semantics. -/
lemma program_realizes (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (callbackStep : Fin (2 ^ width) → Data → Data) (environment : oracles.Interpretation)
    (callbacks : ∀ label, UnitaryCircuit.Realizes encoding (callback label) environment
      (callbackStep label)) (tree : SelectorTrie width) :
    UnitaryCircuit.Realizes encoding (frame.program physical oracles callback tree) environment
      (frame.stepAt callbackStep tree 0 (by omega) 0 (by omega)) :=
  frame.programAt_realizes physical oracles callback callbackStep environment callbacks tree _ _ _ _

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

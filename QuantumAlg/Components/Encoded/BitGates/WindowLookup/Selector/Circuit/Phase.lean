/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Semantics
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Clean
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Exact phase selection on the actual clean-prefix traversal

The selected phase reads the original complete address. Temporary prefix
flips do not change a protected payload phase. Native placement below uses
complete ordered physical-wire equality and the same original gate matrix.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel}

/-- The scalar belonging to the original selected leaf, or identity for a skipped subtree. -/
def selectedPhaseAt (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ) :
    {remaining : Nat} → (tree : SelectorTrie remaining) → (depth : Nat) →
      depth + remaining = width → (offset : Nat) →
        offset + 2 ^ remaining ≤ 2 ^ width → Data → ℂ
  | _, .skip _, _, _, _, _, _ => 1
  | 0, .leaf, _, _, offset, bounded, state =>
      phase ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ state
  | remaining + 1, .fork left right, depth, fits, offset, bounded, state =>
      if (frame.address ⟨depth, by omega⟩).get state then
        frame.selectedPhaseAt phase right (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded) state
      else frame.selectedPhaseAt phase left (depth + 1) (by omega)
        offset (left_bound bounded) state

/-- An original selected payload phase is unaffected by any supplied temporary prefix flip. -/
lemma selectedPhaseAt_flip_stack (frame : SelectorFrame encoding width)
    (phase : Fin (2 ^ width) → Data → ℂ)
    (independent : ∀ label index state,
      phase label ((frame.stack index).flip state) = phase label state)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (index : Fin (width + 1)) (state : Data) :
    frame.selectedPhaseAt phase tree depth fits offset bounded ((frame.stack index).flip state) =
      frame.selectedPhaseAt phase tree depth fits offset bounded state := by
  induction tree generalizing depth offset with
  | skip remaining => rfl
  | leaf => exact independent _ index state
  | @fork remaining left right leftIH rightIH =>
      simp only [selectedPhaseAt, EncodedBit.get_flip_of_wire_ne _ _
        (Ne.symm (frame.separate _ _))]
      split
      · exact rightIH (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
      · exact leftIH (depth + 1) (by omega) offset (left_bound bounded)

/-- The native fork restores its original data on the actual clean-prefix subspace. -/
lemma nativeFork_step_clean (frame : SelectorFrame encoding width)
    (remaining depth : Nat) (fits : depth + (remaining + 1) = width) (offset : Nat)
    (bounded : offset + 2 ^ (remaining + 1) ≤ 2 ^ width)
    (state : Data) (clean : frame.CleanFrom depth state) :
    (frame.clearGate depth (by omega)).step
      ((frame.nextGate depth (by omega)).step
        (GateSpec.stepList (frame.leftGates depth (by omega)) state)) = state := by
  have law := frame.stepAt_clean (fun _ state => state)
    (fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩) (fun _ _ _ => rfl)
    (.fork (.skip remaining) (.skip remaining)) depth fits offset bounded state clean
  simpa only [stepAt, selectedActionAt, conditionalAction, ite_self] using law

/-- A realized actual native program retains its exact encoded image on the same physical wires. -/
lemma placedProgram_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (step : Data → Data) (environment : oracles.Interpretation)
    (realizes : UnitaryCircuit.Realizes encoding program environment step) (state : Data) :
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires program).matrix
      environment).applyVec
        (NormalizedVector.ket (R := ctx.register)
          (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
            (physical.basisEquiv.symm (encoding.encode state)))).vec =
      (NormalizedVector.ket (R := ctx.register)
        (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (physical.basisEquiv.symm (encoding.encode (step state))))).vec := by
  rw [unitaryOfEqualWires_matrix]
  have vector := congrArg NormalizedVector.vec (realizes.apply_encoded_ket state)
  change UnitaryOperator.applyVec (program.matrix environment)
    (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode state))).vec = _ at vector
  have transported := congrArg
    (HilbertVector.reindex (R := physical.toQuantum.register) (S := ctx.register)
      (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires)) vector
  rw [← UnitaryOperator.reindex_applyVec, HilbertVector.reindex_ket,
    HilbertVector.reindex_ket] at transported
  exact transported

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

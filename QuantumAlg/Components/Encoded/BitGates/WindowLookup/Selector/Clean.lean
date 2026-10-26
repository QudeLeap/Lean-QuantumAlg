/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Semantics
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.SelectedAction

/-!
# Clean-prefix selection by the actual pruned unitary traversal

Each actual leaf program is controlled by the final computed prefix. Its ideal
payload protects every address/stack field and does not inspect temporary
prefixes. The traversal then performs exactly the originally selected payload
and restores all initially clean prefix systems.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- An actual clean prefix traversal performs exactly the original enabled selected action. -/
lemma stepAt_clean (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data)
    (preserves : ∀ label, frame.Preserves (action label))
    (independent : ∀ label, frame.IndependentPrefixes (action label))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data)
    (clean : frame.CleanFrom depth state) :
    frame.stepAt (fun label => conditionalAction (frame.stack ⟨width, by omega⟩) (action label))
      tree depth fits offset bounded state =
      conditionalAction (frame.stack ⟨depth, by omega⟩)
        (frame.selectedActionAt action tree depth fits offset bounded) state := by
  induction tree generalizing depth offset state with
  | skip remaining =>
      simp only [stepAt, selectedActionAt, conditionalAction, ite_self]
  | leaf =>
      have current : depth = width := by omega
      subst depth
      rfl
  | @fork remaining left right leftIH rightIH =>
      let present : depth < width := by omega
      let leftAction := frame.selectedActionAt action left (depth + 1) (by omega)
        offset (left_bound bounded)
      let rightAction := frame.selectedActionAt action right (depth + 1) (by omega)
        (offset + 2 ^ remaining) (right_bound bounded)
      let prepared := zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) state
      have preparedClean : frame.CleanFrom (depth + 1) prepared :=
        frame.cleanFrom_zeroChild depth present state clean
      have leftProtected : frame.Preserves leftAction :=
        frame.selectedActionAt_preserves action preserves left _ _ _ _
      have rightProtected : frame.Preserves rightAction :=
        frame.selectedActionAt_preserves action preserves right _ _ _ _
      have leftIndependent : frame.IndependentPrefixes leftAction :=
        frame.selectedActionAt_independent action independent left _ _ _ _
      have rightIndependent : frame.IndependentPrefixes rightAction :=
        frame.selectedActionAt_independent action independent right _ _ _ _
      have leftClean := frame.cleanFrom_preserved
        (conditionalAction (frame.prefixAt depth present) leftAction)
        (frame.conditionalAction_preserves _ _ leftProtected) (depth + 1) prepared preparedClean
      have rightClean := frame.cleanFrom_next depth present
        (conditionalAction (frame.prefixAt depth present) leftAction prepared) leftClean
      have leftCorrect := leftIH (depth + 1) (by omega) offset (left_bound bounded)
        prepared preparedClean
      have rightCorrect := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded)
        ((frame.nextGate depth present).step
          (conditionalAction (frame.prefixAt depth present) leftAction prepared)) rightClean
      change _ = conditionalAction (frame.prefixAt depth present) leftAction prepared at leftCorrect
      dsimp only [stepAt]
      rw [frame.leftGates_step, leftCorrect, rightCorrect]
      change forkStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) (conditionalAction (frame.prefixAt depth present) leftAction)
        (conditionalAction (frame.prefixAt depth present) rightAction) state = _
      rw [scopedFork_correct _ _ _ (Ne.symm (frame.enable_prefix depth present))
        (Ne.symm (frame.address_prefix depth present)) leftAction rightAction
        (frame.forkAction_of_frame depth present _ leftProtected leftIndependent)
        (frame.forkAction_of_frame depth present _ rightProtected rightIndependent)
        state (clean ⟨depth, present⟩ (Nat.le_refl _))]
      rfl

/-- The same actual program has this exact normalized-ket behavior on its clean input subspace. -/
lemma program_apply_encoded_ket_clean (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (action : Fin (2 ^ width) → Data → Data) (environment : oracles.Interpretation)
    (callbacks : ∀ label, UnitaryCircuit.Realizes encoding (callback label) environment
      (conditionalAction (frame.stack ⟨width, by omega⟩) (action label)))
    (preserves : ∀ label, frame.Preserves (action label))
    (independent : ∀ label, frame.IndependentPrefixes (action label))
    (tree : SelectorTrie width) (state : Data) (clean : frame.CleanFrom 0 state) :
    (frame.program physical oracles callback tree).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
      NormalizedVector.ket (physical.basisEquiv.symm
        (encoding.encode (conditionalAction (frame.stack ⟨0, by omega⟩)
          (frame.selectedActionAt action tree 0 (by omega) 0 (by omega)) state))) := by
  rw [(frame.program_realizes physical oracles callback _
    environment callbacks tree).apply_encoded_ket]
  rw [frame.stepAt_clean action preserves independent tree _ _ _ _ state clean]

/-- The selected payload retains every prefix's original zero value. -/
lemma selected_clean_restored (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Data → Data)
    (preserves : ∀ label, frame.Preserves (action label)) (tree : SelectorTrie width)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    frame.CleanFrom 0 (conditionalAction (frame.stack ⟨0, by omega⟩)
      (frame.selectedActionAt action tree 0 (by omega) 0 (by omega)) state) :=
  frame.cleanFrom_preserved _ (frame.conditionalAction_preserves _ _
    (frame.selectedActionAt_preserves action preserves tree _ _ _ _)) 0 state clean

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

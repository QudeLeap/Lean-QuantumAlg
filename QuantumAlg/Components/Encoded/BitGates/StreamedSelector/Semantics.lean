/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Fold
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Clean
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.SelectedAction

/-! # Actual coherent selector execution as an ordered stream of Boolean leaf visits -/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- A clean traversal visits every retained leaf, including its explicit false-selection action. -/
lemma streamedStepAt_clean (frame : SelectorFrame encoding width)
    (action : Fin (2 ^ width) → Bool → Data → Data)
    (preserves : ∀ label selected, frame.Preserves (action label selected))
    (independent : ∀ label selected, frame.IndependentPrefixes (action label selected))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (state : Data)
    (clean : frame.CleanFrom depth state) :
    frame.stepAt (fun label value =>
      action label ((frame.stack ⟨width, by omega⟩).get value) value)
      tree depth fits offset bounded state =
      foldAt frame action tree depth fits offset bounded
        ((frame.stack ⟨depth, by omega⟩).get state) state := by
  induction tree generalizing depth offset state with
  | skip remaining => rfl
  | leaf =>
      have current : depth = width := by omega
      subst depth
      rfl
  | @fork remaining left right leftIH rightIH =>
      let present : depth < width := by omega
      let leftAction (selected : Bool) := foldAt frame action left (depth + 1) (by omega)
        offset (SelectorFrame.left_bound bounded) selected
      let rightAction (selected : Bool) := foldAt frame action right (depth + 1) (by omega)
        (offset + 2 ^ remaining) (SelectorFrame.right_bound bounded) selected
      let leftVisit := fun value => leftAction ((frame.prefixAt depth present).get value) value
      let rightVisit := fun value => rightAction ((frame.prefixAt depth present).get value) value
      let prepared := zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) state
      have preparedClean := frame.cleanFrom_zeroChild depth present state clean
      have leftProtected : ∀ selected, frame.Preserves (leftAction selected) :=
        fun selected => foldAt_preserves frame action preserves left _ _ _ _ selected
      have rightProtected : ∀ selected, frame.Preserves (rightAction selected) :=
        fun selected => foldAt_preserves frame action preserves right _ _ _ _ selected
      have leftIndependent : ∀ selected, frame.IndependentPrefixes (leftAction selected) :=
        fun selected => foldAt_independent frame action independent left _ _ _ _ selected
      have rightIndependent : ∀ selected, frame.IndependentPrefixes (rightAction selected) :=
        fun selected => foldAt_independent frame action independent right _ _ _ _ selected
      have leftVisitProtected : frame.Preserves leftVisit := by
        constructor
        · intro index value
          exact (leftProtected _).1 index value
        · intro index value
          exact (leftProtected _).2 index value
      have leftClean := frame.cleanFrom_preserved leftVisit leftVisitProtected
        (depth + 1) prepared preparedClean
      have rightClean := frame.cleanFrom_next depth present (leftVisit prepared) leftClean
      have leftCorrect := leftIH (depth + 1) (by omega) offset
        (SelectorFrame.left_bound bounded) prepared preparedClean
      have rightCorrect := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (SelectorFrame.right_bound bounded)
        ((frame.nextGate depth present).step (leftVisit prepared)) rightClean
      change _ = leftVisit prepared at leftCorrect
      change _ = rightVisit ((frame.nextGate depth present).step (leftVisit prepared))
        at rightCorrect
      dsimp only [SelectorFrame.stepAt]
      rw [frame.leftGates_step, leftCorrect, rightCorrect]
      change forkStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present)
        (fun value => leftAction ((frame.prefixAt depth present).get value) value)
        (fun value => rightAction ((frame.prefixAt depth present).get value) value) state = _
      rw [streamedFork_correct _ _ _ (frame.enable_prefix depth present).symm
        (frame.address_prefix depth present).symm leftAction rightAction
        (fun selected => frame.forkAction_of_frame depth present _
          (leftProtected selected) (leftIndependent selected))
        (fun selected => frame.forkAction_of_frame depth present _
          (rightProtected selected) (rightIndependent selected))
        state (clean ⟨depth, present⟩ (Nat.le_refl _))]
      rfl

/-- The ordered streaming fold is the normalized-ket action of the same actual native program. -/
lemma program_apply_encoded_ket_streamed_clean (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (action : Fin (2 ^ width) → Bool → Data → Data) (environment : oracles.Interpretation)
    (callbacks : ∀ label, UnitaryCircuit.Realizes encoding (callback label) environment
      (fun value => action label ((frame.stack ⟨width, by omega⟩).get value) value))
    (preserves : ∀ label selected, frame.Preserves (action label selected))
    (independent : ∀ label selected, frame.IndependentPrefixes (action label selected))
    (tree : SelectorTrie width) (state : Data) (clean : frame.CleanFrom 0 state) :
    (frame.program physical oracles callback tree).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
      NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode
        (foldAt frame action tree 0 (by omega) 0 (by omega)
          ((frame.stack ⟨0, by omega⟩).get state) state))) := by
  have actual := frame.program_realizes physical oracles callback _ environment callbacks tree
  rw [actual.apply_encoded_ket state]
  rw [streamedStepAt_clean frame action preserves independent tree 0 (by omega) 0
    (by omega) state clean]

end

end QuantumAlg.EncodedBit.StreamedSelector

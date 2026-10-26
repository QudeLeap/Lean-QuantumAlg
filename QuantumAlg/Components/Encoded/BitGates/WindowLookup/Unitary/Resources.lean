/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources

/-!
# Actual native ledger of the unitary table XOR

Every selected constant uses its own emitted masked-X circuit. Selector
forks and retained callbacks are counted from the same actual program;
the callback depth bound uses its physical parallel CNOT layers.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {addressWidth wordWidth : Nat}

/-- Number of actual native CNOTs in a nonempty constant mask, with zero for the empty mask. -/
def wordMaskCnotCount {width : Nat} (constant : Fin (2 ^ width)) : Nat :=
  if (Word.constantOneIndices constant).length = 0 then 0
  else 2 * (Word.constantOneIndices constant).length - 1

private lemma leafSumAt_zero {width remaining : Nat} (tree : SelectorTrie remaining)
    (offset : Nat) (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    SelectorTrie.leafSumAt width (fun _ => 0) tree offset bounded = 0 := by
  induction tree generalizing offset with
  | skip remaining => rfl
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      dsimp only [SelectorTrie.leafSumAt]
      rw [leftIH, rightIH]

private lemma wordMaskProgram_count (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Word encoding wordWidth)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ wordWidth)) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles)) :
    ResourcePool.count focus
      (wordMaskProgram physical oracles target distinct selector outside
        constant height).eventCost =
      if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model oracles)) = focus then
        wordMaskCnotCount constant else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    wordMaskProgram_eventTrace _ _ _ _ _ _ _ _ covered]
  simp only [ResourcePool.count_ofList, List.count_replicate, beq_iff_eq, wordMaskCnotCount]

/-- The actual table lookup has exactly two Toffolis per retained unitary selector fork. -/
lemma enabledLookupProgram_toffoli_count (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (enabledLookupProgram frame physical oracles target table active height).eventCost =
        2 * (SelectorTrie.prune addressWidth active).forks := by
  unfold enabledLookupProgram
  rw [frame.program_event_count]
  have callbacks : (fun label : Fin (2 ^ addressWidth) =>
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
        (wordMaskProgram physical oracles target.word target.distinct
          (frame.stack ⟨addressWidth, by omega⟩)
          (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height).eventCost) =
      (fun _ => 0) := by
    funext label
    rw [wordMaskProgram_count _ _ _ _ _ _ _ _ covered]
    rfl
  rw [callbacks]
  simp [SelectorTrie.leafSum, leafSumAt_zero, selectorForkCount, Nat.mul_comm]

/-- Only the selector's two X gates per retained fork contribute a single-qubit native event. -/
lemma enabledLookupProgram_singleQubit_count (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (enabledLookupProgram frame physical oracles target table active height).eventCost =
        2 * (SelectorTrie.prune addressWidth active).forks := by
  unfold enabledLookupProgram
  rw [frame.program_event_count]
  have callbacks : (fun label : Fin (2 ^ addressWidth) =>
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (wordMaskProgram physical oracles target.word target.distinct
          (frame.stack ⟨addressWidth, by omega⟩)
          (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height).eventCost) =
      (fun _ => 0) := by
    funext label
    rw [wordMaskProgram_count _ _ _ _ _ _ _ _ covered]
    rfl
  rw [callbacks]
  simp [SelectorTrie.leafSum, leafSumAt_zero, selectorForkCount, Nat.mul_comm]

/-- Every actual retained mask contributes its own exact CNOT multiplicity. -/
lemma enabledLookupProgram_cnot_count (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (enabledLookupProgram frame physical oracles target table active height).eventCost =
        (SelectorTrie.prune addressWidth active).forks +
          (SelectorTrie.prune addressWidth active).leafSum (fun label =>
            wordMaskCnotCount (table label)) := by
  unfold enabledLookupProgram
  rw [frame.program_event_count]
  have callbacks : (fun label : Fin (2 ^ addressWidth) =>
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (wordMaskProgram physical oracles target.word target.distinct
          (frame.stack ⟨addressWidth, by omega⟩)
          (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height).eventCost) =
      (fun label => wordMaskCnotCount (table label)) := by
    funext label
    rw [wordMaskProgram_count _ _ _ _ _ _ _ _ covered]
    rfl
  rw [callbacks]
  simp [selectorForkCount]

/-- Actual parallel masked-X callbacks give a logarithmic contribution per retained row. -/
lemma enabledLookupProgram_quantumTime_le (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (enabledLookupProgram frame physical oracles target table active height) ≤
        5 * (SelectorTrie.prune addressWidth active).forks +
          (SelectorTrie.prune addressWidth active).leaves * (2 * height + 1) := by
  unfold enabledLookupProgram
  rw [frame.program_quantumTime]
  apply Nat.add_le_add_left
  exact SelectorTrie.leafSumAt_le _ _ _
    (fun label => wordMaskProgram_quantumTime_le _ _ _ _ _ _ _ _) _ _

end

end QuantumAlg.EncodedBit.WindowLookup

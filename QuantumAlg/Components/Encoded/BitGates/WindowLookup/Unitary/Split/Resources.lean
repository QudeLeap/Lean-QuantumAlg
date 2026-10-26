/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Full

/-!
# Native resources of the actual top-bit table lookup

The two original half-table programs and two actual X gates give the native
ledger. Both halves preserve their original masked-X parallel schedules.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width wordWidth : Nat}

private lemma xProgram_count (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (bit : EncodedBit encoding) (focus : Resource.Event (.quantum AlgorithmGate.model oracles)) :
    ResourcePool.count focus ((GateSpec.x bit).program physical oracles).eventCost =
      if (.gate .singleQubit : Resource.Event (.quantum AlgorithmGate.model oracles)) = focus
        then 1 else 0 := by
  rw [GateSpec.program_eventCost, ResourcePool.count_singleton]
  rfl

/-- The same actual program uses two Toffolis per fork of its two half-table trees. -/
lemma splitLookupProgram_toffoli_count (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (splitLookupProgram frame physical oracles target table height).eventCost =
        2 * 2 ^ (width + 1) - 4 := by
  have topCount : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      ((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles).eventCost = 0 := by
    rw [xProgram_count]
    rfl
  unfold splitLookupProgram
  simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  rw [topCount,
    enabledLookupProgram_toffoli_count _ _ _ _ _ _ _ covered,
    enabledLookupProgram_toffoli_count _ _ _ _ _ _ _ covered,
    SelectorTrie.prune_true, SelectorTrie.full_forks]
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  simp only [zero_add, pow_succ]
  omega

/-- Every emitted single-qubit occurrence is one of the original selector X gates. -/
lemma splitLookupProgram_singleQubit_count (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (splitLookupProgram frame physical oracles target table height).eventCost =
        2 * 2 ^ (width + 1) - 2 := by
  have topCount : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      ((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles).eventCost = 1 := by
    rw [xProgram_count]
    rfl
  unfold splitLookupProgram
  simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  rw [topCount,
    enabledLookupProgram_singleQubit_count _ _ _ _ _ _ _ covered,
    enabledLookupProgram_singleQubit_count _ _ _ _ _ _ _ covered,
    SelectorTrie.prune_true, SelectorTrie.full_forks]
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  simp only [pow_succ]
  omega

private lemma wordMaskCnotCount_le {count : Nat} (constant : Fin (2 ^ count)) :
    wordMaskCnotCount constant ≤ 2 * count - 1 := by
  have bound := Word.constantOneIndices_length_le constant
  unfold wordMaskCnotCount
  split <;> omega

private lemma enabled_cnot_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (enabledLookupProgram frame physical oracles target table (fun _ => true) height).eventCost ≤
        (2 ^ width - 1) + 2 ^ width * (2 * wordWidth - 1) := by
  rw [enabledLookupProgram_cnot_count _ _ _ _ _ _ _ covered,
    SelectorTrie.prune_true, SelectorTrie.full_forks]
  apply Nat.add_le_add_left
  have bounded := SelectorTrie.leafSumAt_le (SelectorTrie.full width)
    (fun label => wordMaskCnotCount (table label)) (2 * wordWidth - 1)
    (fun label => wordMaskCnotCount_le (table label)) 0 (by omega)
  simpa only [SelectorTrie.leafSum, SelectorTrie.full_leaves] using bounded

/-- Actual dirty-target masked-X words give this uniform CNOT bound for the complete table. -/
lemma splitLookupProgram_cnot_count_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (splitLookupProgram frame physical oracles target table height).eventCost ≤
        2 * (2 ^ width - 1) + 2 * 2 ^ width * (2 * wordWidth - 1) := by
  have left := enabled_cnot_le frame physical oracles target (table false) height covered
  have right := enabled_cnot_le frame physical oracles target (table true) height covered
  have topCount : ResourcePool.count
      (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      ((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles).eventCost = 0 := by
    rw [xProgram_count]
    rfl
  unfold splitLookupProgram
  simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  rw [topCount]
  simp only [zero_add]
  rw [Nat.mul_assoc]
  omega

/-- The depth includes the actual original parallel mask schedules and both top X gates. -/
lemma splitLookupProgram_quantumTime_le (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth)) (height : Nat) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (splitLookupProgram frame physical oracles target table height) ≤
        2 + 10 * (2 ^ width - 1) + 2 * 2 ^ width * (2 * height + 1) := by
  have left := enabledLookupProgram_quantumTime_le frame physical oracles target
    (table false) (fun _ => true) height
  have right := enabledLookupProgram_quantumTime_le frame physical oracles target
    (table true) (fun _ => true) height
  rw [SelectorTrie.prune_true, SelectorTrie.full_forks, SelectorTrie.full_leaves] at left right
  have topTime : UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      ((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles) = 1 := rfl
  unfold splitLookupProgram
  simp only [UnitaryCircuit.evaluatedEventDepth_seq]
  rw [topTime, Nat.mul_assoc]
  omega

end

end QuantumAlg.EncodedBit.WindowLookup

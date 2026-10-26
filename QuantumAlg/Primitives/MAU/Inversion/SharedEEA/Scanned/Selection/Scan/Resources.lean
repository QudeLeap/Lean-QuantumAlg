/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin

/-! # Native counts and dependence depth of the actual pruned EEA scan -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- One callback is charged exactly at each valid complete original address. -/
def leafIndicator (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) : Nat :=
  if label.val < width + 3 then 1 else 0

private lemma callback_trace (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    (callback width label).eventTrace =
      if label.val < width + 3 then [.gate .cnot, .gate .toffoli, .gate .cnot] else [] := by
  unfold callback
  split <;> rfl

private lemma callback_toffoli_count (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (callback width label).eventCost =
      leafIndicator width label := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, callback_trace]
  unfold leafIndicator
  split <;> simp [ResourcePool.ofList_cons, ResourcePool.ofList_nil]

private lemma callback_cnot_count (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (callback width label).eventCost =
      2 * leafIndicator width label := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, callback_trace]
  unfold leafIndicator
  split <;> simp [ResourcePool.ofList_cons, ResourcePool.ofList_nil]

private lemma callback_quantumTime (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    (callback width label).evaluatedEventDepth Resource.Event.quantumDuration =
      3 * leafIndicator width label := by
  unfold callback leafIndicator
  split <;> rfl

private lemma leafSumAt_mul {width remaining : Nat} (trie : SelectorTrie remaining)
    (cost : Fin (2 ^ width) → Nat) (factor offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    SelectorTrie.leafSumAt width (fun label => factor * cost label) trie offset bounded =
      factor * SelectorTrie.leafSumAt width cost trie offset bounded := by
  induction trie generalizing offset with
  | skip remaining => simp only [SelectorTrie.leafSumAt, Nat.mul_zero]
  | leaf => rfl
  | @fork remaining left right leftIH rightIH =>
      simp only [SelectorTrie.leafSumAt, leftIH, rightIH, Nat.mul_add]

private lemma leafSum_mul {width : Nat} (trie : SelectorTrie width)
    (cost : Fin (2 ^ width) → Nat) (factor : Nat) :
    trie.leafSum (fun label => factor * cost label) = factor * trie.leafSum cost :=
  leafSumAt_mul trie cost factor 0 (by omega)

/-- Every Toffoli belongs to an actual fork or an actually retained Fredkin callback. -/
lemma program_toffoli_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program width).eventCost =
      2 * (tree width).forks + (tree width).leafSum (leafIndicator width) := by
  rw [program, SelectorFrame.program_event_count]
  have forkCount : selectorForkCount .empty (.gate .toffoli) = 2 := by
    simp [selectorForkCount]
  rw [forkCount]
  simp only [callback_toffoli_count]
  change (tree width).forks * 2 + (tree width).leafSum (leafIndicator width) = _
  omega

/-- Each actual callback adds two CNOTs to the traversal's single CNOT per fork. -/
lemma program_cnot_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program width).eventCost =
      (tree width).forks + 2 * (tree width).leafSum (leafIndicator width) := by
  rw [program, SelectorFrame.program_event_count]
  have forkCount : selectorForkCount .empty (.gate .cnot) = 1 := by
    simp [selectorForkCount]
  rw [forkCount]
  simp only [callback_cnot_count, leafSum_mul]
  omega

/-- Shared selector controls impose their actual sequential traversal dependencies. -/
lemma program_quantumTime (width : Nat) :
    (program width).evaluatedEventDepth Resource.Event.quantumDuration =
      5 * (tree width).forks + 3 * (tree width).leafSum (leafIndicator width) := by
  rw [program, SelectorFrame.program_quantumTime]
  simp only [callback_quantumTime, leafSum_mul]

/-- The full ten-bit domain retains 259 valid leaves and 266 necessary fork nodes. -/
lemma p256_tree_counts : (tree 256).forks = 266 ∧
    (tree 256).leafSum (leafIndicator 256) = 259 := by decide

/-- The actual P-256 pruned scan executes 791 Toffolis. -/
lemma p256_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 791 := by
  rw [program_toffoli_count, p256_tree_counts.1, p256_tree_counts.2]

/-- The same original scan has 784 CNOT occurrences. -/
lemma p256_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 784 := by
  rw [program_cnot_count, p256_tree_counts.1, p256_tree_counts.2]

/-- The scan's actual default quantum dependence depth is 2107. -/
lemma p256_quantumTime :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration = 2107 := by
  rw [program_quantumTime, p256_tree_counts.1, p256_tree_counts.2]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

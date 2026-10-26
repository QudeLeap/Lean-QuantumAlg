/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Enumeration
import all QuantumAlg.Util.ThresholdStream.Indices

/-! # Increasing original indices of a finite pruned streaming template -/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

/-- A below-limit trie visits precisely the original finite prefix, in its original order. -/
lemma labels_pruneBelow {width : Nat} (limit : Nat) (bounded : limit ≤ 2 ^ width) :
    (labelsAt (width := width) (SelectorTrie.prune width (fun label => decide (label.val < limit)))
      0 (by omega)).map Fin.val = List.range limit := by
  rw [SelectorTrie.prune, labelsAt_pruneBelow]
  rw [← List.range_eq_range', ThresholdStream.filter_range_below,
    Nat.min_eq_right bounded]

/-- Replacing a typed label by its original index changes neither action nor boundary flag. -/
lemma fold_pruneBelow {Data : Type*} {width : Nat} (limit : Nat)
    (bounded : limit ≤ 2 ^ width) (action : Nat → Bool → Data → Data)
    (enabled : Bool) (last : Nat) (state : Data) :
    (labelsAt (width := width) (SelectorTrie.prune width (fun label => decide (label.val < limit)))
      0 (by omega)).foldl (fun value label =>
        action label.val (enabled && decide (label.val = last)) value) state =
      (List.range limit).foldl (fun value index =>
        action index (enabled && decide (index = last)) value) state := by
  rw [← labels_pruneBelow limit bounded]
  simp only [List.foldl_map]

end

end QuantumAlg.EncodedBit.StreamedSelector

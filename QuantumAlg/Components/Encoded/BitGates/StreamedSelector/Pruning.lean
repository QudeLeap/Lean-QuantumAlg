/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Pruning

/-! # Empty actual selector trees from a proved full-domain leaf predicate -/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup

private lemma pruneAt_of_false (width : Nat) (active : Fin (2 ^ width) → Bool)
    (empty : ∀ label, active label = false) (remaining offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) :
    SelectorTrie.pruneAt width active remaining offset bounded = .skip remaining := by
  induction remaining generalizing offset with
  | zero => simp only [SelectorTrie.pruneAt, empty, Bool.false_eq_true, if_false]
  | succ remaining ih =>
      rw [SelectorTrie.pruneAt, ih, ih]
      rfl

/-- An empty static tree requires a false predicate on every original full-width label. -/
lemma prune_of_false (width : Nat) (active : Fin (2 ^ width) → Bool)
    (empty : ∀ label, active label = false) : SelectorTrie.prune width active = .skip width :=
  pruneAt_of_false width active empty width 0 (by omega)

end

end QuantumAlg.EncodedBit.StreamedSelector

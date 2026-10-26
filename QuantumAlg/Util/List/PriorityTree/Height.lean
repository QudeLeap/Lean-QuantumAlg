/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.PriorityTree

/-! # Static prefix depth of an ordered priority tree -/

namespace QuantumAlg.ListPriority.Tree

variable {Label : Type*}

/-- Maximum number of real forks on a root-to-leaf path. -/
def height : Tree Label → Nat
  | .empty => 0
  | .leaf _ => 0
  | .fork higher lower => max higher.height lower.height + 1

/-- A real fork leaves enough prefix positions for either actual child. -/
lemma child_heights_le (higher lower : Tree Label) :
    higher.height + 1 ≤ (Tree.fork higher lower).height ∧
      lower.height + 1 ≤ (Tree.fork higher lower).height :=
  ⟨Nat.add_le_add_right (Nat.le_max_left _ _) _,
    Nat.add_le_add_right (Nat.le_max_right _ _) _⟩

end QuantumAlg.ListPriority.Tree

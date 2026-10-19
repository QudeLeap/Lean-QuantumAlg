/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.WordArithmetic
import all QuantumAlg.Primitives.MAU.Addition.HRS.Split

/-!
# Reassemble the exact HRS recursive arithmetic result

The proven carry-first half-addition identity is transported through the
actual ceiling/floor word split. This establishes the arithmetic step
needed when composing the recursive circuits [HRS16, paper.tex:232-245].
-/

namespace QuantumAlg.MAU.Addition.HRS

/-- Rejoining the two recursive additions yields constant addition at the original width. -/
lemma hrsJoin_recursive_addition (width : Nat) (constant input : Fin (2 ^ width)) :
    joinWord width
        (addWord ((splitWord width) constant).1 ((splitWord width) input).1,
          addWord ((splitWord width) constant).2
            (if decide (2 ^ lowWidth width ≤ ((splitWord width) input).1.val +
                ((splitWord width) constant).1.val)
              then incrementWord ((splitWord width) input).2
              else ((splitWord width) input).2)) = addWord constant input := by
  have hin : ((splitWord width) input).1.val +
      2 ^ lowWidth width * ((splitWord width) input).2.val = input.val := by
    simpa only [hrsJoin_value] using congrArg Fin.val (hrsJoin_split width input)
  have hconst : ((splitWord width) constant).1.val +
      2 ^ lowWidth width * ((splitWord width) constant).2.val = constant.val := by
    simpa only [hrsJoin_value] using congrArg Fin.val (hrsJoin_split width constant)
  have hwidth : 2 ^ (highWidth width + lowWidth width) = 2 ^ width := by
    congr 1
    have := hrsSplit_width_sum width
    omega
  have h := congrArg Fin.val (hrsAddWord_halves (lowWidth width) (highWidth width)
    ((splitWord width) input).1 ((splitWord width) constant).1
    ((splitWord width) input).2 ((splitWord width) constant).2)
  change ((((splitWord width) input).1.val +
      2 ^ lowWidth width * ((splitWord width) input).2.val) +
      (((splitWord width) constant).1.val +
        2 ^ lowWidth width * ((splitWord width) constant).2.val)) %
        2 ^ (highWidth width + lowWidth width) =
    (addWord ((splitWord width) constant).1 ((splitWord width) input).1).val +
      2 ^ lowWidth width *
        (addWord ((splitWord width) constant).2
          (if decide (2 ^ lowWidth width ≤ ((splitWord width) input).1.val +
              ((splitWord width) constant).1.val)
            then incrementWord ((splitWord width) input).2
            else ((splitWord width) input).2)).val at h
  rw [hin, hconst, hwidth] at h
  apply Fin.ext
  rw [hrsJoin_value]
  exact h.symm

end QuantumAlg.MAU.Addition.HRS

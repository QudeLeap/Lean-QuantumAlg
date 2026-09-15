/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.VariableWord.Accumulate
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv

/-!
# Independent permutation of two variable inputs and an accumulator

The complete variable-product action preserves the first input and applies
the independently defined modular accumulation permutation to the other
two words. This finite arithmetic construction refers to no circuit,
native event, space layout or compilation strategy
[VBE95, 9511018.tex:333-367; G17, paper.tex:319-334].
-/

namespace QuantumAlg.Nat.FixedWidth

/-- The two binary scans agree with the mathematical product coefficient on all labels. -/
theorem variableWordPrefix_eq_accumulate {width : Nat} (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) :
    variableWordPrefix modulus first second target width =
      accumulateWordPrefix modulus first.val second target width := by
  by_cases valid : target.val < modulus.val
  · apply Fin.ext
    exact (variableWordPrefix_full modulus first second target valid).trans
      (accumulateWordPrefix_full modulus first.val second target valid).symm
  · have outside : modulus.val ≤ target.val := Nat.le_of_not_gt valid
    rw [variableWordPrefix_outside modulus first second target width outside,
      accumulateWordPrefix_outside modulus first.val second target outside width]

/-- Independent total reversible variable-product accumulation, including noncanonical labels. -/
def variableTripleEquiv {width : Nat} (modulus : Fin (2 ^ width + 1)) :
    Equiv.Perm (Fin (2 ^ width) × (Fin (2 ^ width) × Fin (2 ^ width))) where
  toFun state := (state.1, accumulatePairEquiv modulus state.1.val width state.2)
  invFun state := (state.1, (accumulatePairEquiv modulus state.1.val width).symm state.2)
  left_inv := by
    rintro ⟨first, second, target⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨first, second, target⟩
    simp only [Equiv.apply_symm_apply]

/-- The independent permutation agrees with the proved bit-pair arithmetic recurrence. -/
theorem variableTripleEquiv_apply {width : Nat} (modulus : Fin (2 ^ width + 1))
    (state : Fin (2 ^ width) × (Fin (2 ^ width) × Fin (2 ^ width))) :
    variableTripleEquiv modulus state =
      (state.1, state.2.1, variableWordPrefix modulus state.1 state.2.1 state.2.2 width) := by
  change (state.1, accumulatePairEquiv modulus state.1.val width state.2) = _
  rw [accumulatePairEquiv_apply, variableWordPrefix_eq_accumulate]

end QuantumAlg.Nat.FixedWidth

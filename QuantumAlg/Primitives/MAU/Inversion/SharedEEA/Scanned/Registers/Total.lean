/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers

/-! # Complete computational-basis coverage of the scanned EEA frame -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned

noncomputable section

private lemma product_total {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (leftOnto : Function.Surjective left.encode)
    (rightOnto : Function.Surjective right.encode) :
    Function.Surjective (BinaryLabelEncoding.prod left right).encode := by
  intro label
  obtain ⟨⟨first, second⟩, rfl⟩ :=
    (prodEquiv (m := left.width) (n := right.width)).surjective label
  obtain ⟨leftValue, rfl⟩ := leftOnto first
  obtain ⟨rightValue, rfl⟩ := rightOnto second
  exact ⟨(leftValue, rightValue), rfl⟩

private lemma bool_total : Function.Surjective BinaryLabelEncoding.bool.encode := by
  intro label
  obtain ⟨value, rfl⟩ := finTwoEquiv.symm.surjective label
  refine ⟨value, ?_⟩
  cases value <;> rfl

/-- Every complete register and pool label is retained, including all unreachable metadata. -/
lemma encoding_surjective (width : Nat) : Function.Surjective (encoding width).encode :=
  product_total _ _ (SharedEEA.encoding_surjective width)
    (product_total _ _ BitVec.equivFin.toEquiv.surjective
      (product_total _ _ BitVec.equivFin.toEquiv.surjective bool_total))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned

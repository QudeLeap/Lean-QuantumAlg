/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement

/-!
# Native arithmetic on a public ordered subword

The same static selection of positions restricts both operands. Their
complete physical complement is retained by the actual placed TTK body.
The selection is independent of every quantum input value.
-/

namespace QuantumAlg.MAU.Addition.TTK.WordPlacement

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width selected : Nat}

/-- Restrict both declared operands to the same injective public ordered positions. -/
def subword (placement : WordPlacement encoding width) (positions : Fin selected → Fin width)
    (distinct : Function.Injective positions) : WordPlacement encoding selected where
  addend := ⟨fun index => placement.addend.bit (positions index)⟩
  target := ⟨fun index => placement.target.bit (positions index)⟩
  addendDistinct := placement.addendDistinct.comp distinct
  targetDistinct := placement.targetDistinct.comp distinct
  separate left right := placement.separate (positions left) (positions right)
  onto := placement.onto

/-- The actual source lens is the declared selected source position. -/
lemma subword_addend (placement : WordPlacement encoding width)
    (positions : Fin selected → Fin width) (distinct : Function.Injective positions)
    (index : Fin selected) :
    ((placement.subword positions distinct).addend.bit index) =
      placement.addend.bit (positions index) := rfl

/-- The actual target lens is the declared selected target position. -/
lemma subword_target (placement : WordPlacement encoding width)
    (positions : Fin selected → Fin width) (distinct : Function.Injective positions)
    (index : Fin selected) :
    ((placement.subword positions distinct).target.bit index) =
      placement.target.bit (positions index) := rfl

end

end QuantumAlg.MAU.Addition.TTK.WordPlacement

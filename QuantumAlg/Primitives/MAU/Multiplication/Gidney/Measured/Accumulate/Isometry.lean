/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Isometry

/-!
# Clean-helper full-label injectivity of the actual source-order MAC

Each chronological row has its accepted full-label injectivity on the
helper-clean input subspace. Earlier rows physically restore those helpers.
The proof inverts label equalities only; no inverse circuit is assigned to
any measured program [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Equal actual prefix outputs identify equal original complete clean-helper inputs. -/
lemma accumulatePrefixWord_label_injective_clean (layout : Layout encoding width)
    (wide : 2 ≤ width) (modulus : BitVec width) (constants : Fin width → BitVec width)
    (count : Nat) (bounded : count ≤ width) :
    ∀ (first second : Data), (∀ helper, (layout.clean helper).get first = false) →
      (∀ helper, (layout.clean helper).get second = false) →
      wordLabel (layout.accumulatePrefixWord wide modulus constants count bounded) first =
        wordLabel (layout.accumulatePrefixWord wide modulus constants count bounded) second →
          first = second := by
  induction count with
  | zero => intro first second _ _ same; exact same
  | succ count ih =>
      intro first second firstClean secondClean same
      rw [accumulatePrefixWord, wordLabel_append, wordLabel_append] at same
      have firstFrame := accumulatePrefixWord_frame layout wide modulus constants count
        (by omega) first firstClean
      have secondFrame := accumulatePrefixWord_frame layout wide modulus constants count
        (by omega) second secondClean
      have earlierSame :=
        Addition.Gidney.Measured.Reduction.Layout.modularWord_label_injective_clean
          (layout.reductionLayout ⟨count, by omega⟩) wide modulus _ _ _
            firstFrame.clean secondFrame.clean same
      exact ih (by omega) first second firstClean secondClean earlierSame

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

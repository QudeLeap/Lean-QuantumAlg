/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Half.Prefix00
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Half.Prefix01
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Half.Prefix10
import all QuantumAlg.Analysis.QNN.Designs.QubitTwoDesign.Core.Algebra.Facts.Closed.Half.Prefix11

/-! # Half-left binary-octahedral numerator closure -/

section

namespace QuantumAlg.QubitTwoDesign.OctNumeratorClosed

/-- Multiplication by a half-family numerator stays in the doubled numerator set. -/
lemma half :
    ∀ negative b, ∃ c,
      octNumerator (.half negative) * octNumerator b = octNumerator c + octNumerator c := by
  intro negative b
  have hnegative :
      negative = ![negative 0, negative 1, negative 2, negative 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hnegative]
  cases h0 : negative 0 <;> cases h1 : negative 1
  · simpa [h0, h1] using Half.prefix00 (negative 2) (negative 3) b
  · simpa [h0, h1] using Half.prefix01 (negative 2) (negative 3) b
  · simpa [h0, h1] using Half.prefix10 (negative 2) (negative 3) b
  · simpa [h0, h1] using Half.prefix11 (negative 2) (negative 3) b

end QuantumAlg.QubitTwoDesign.OctNumeratorClosed

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Index
import all QuantumAlg.Util.Nat.FixedWidth.Window.Chronology.Widths

/-!
# Exact active-reset width of the two chronological source streams

The generic symbolic width-sum theorem is specialized at260 bits and16
bits per full window. Both streams contain exactly260 active positions;
their real pre-H resets therefore have520 selected wire invocations.
No circuit or gate list is unfolded to establish this arithmetic identity.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

open scoped BigOperators

/-- The physical active width equals the width of its original logical unsigned digit. -/
lemma windowIndex_activeWidth (index : WindowIndex) :
    index.lowerWidth + 1 =
      Nat.FixedWidth.Window.Chronology.activeWidth 260 16 index.logical.val := by
  by_cases full : index.full
  · have before : index.logical.val < 260 / 16 := full
    rw [WindowIndex.lowerWidth, if_pos full,
      Nat.FixedWidth.Window.Chronology.activeWidth_full before]
  · have last : index.logical.val = 16 := by
      have bound := index.logical.isLt
      change ¬index.logical.val < 16 at full
      omega
    rw [WindowIndex.lowerWidth, if_neg full, last]
    rfl

/-- One stream uses every one of its original260 exponent positions once in total width. -/
lemma chronological_stream_activeWidth (stream : Fin 2) :
    (∑ position : Fin 17, ((WindowIndex.mk stream position.rev).lowerWidth + 1)) = 260 := by
  calc
    _ = ∑ position : Fin 17,
        Nat.FixedWidth.Window.Chronology.activeWidth 260 16
          (Nat.FixedWidth.Window.Chronology.logical 17 position).val := by
      apply Finset.sum_congr rfl
      intro position _
      exact windowIndex_activeWidth _
    _ = 260 :=
      Nat.FixedWidth.Window.Chronology.chronological_activeWidth_sum 260 16 (by decide)

/-- Both actual chronological streams together require exactly520 active pre-H reset steps. -/
lemma chronological_paired_activeWidth :
    (∑ position : Fin 34, ((chronologicalIndex position).lowerWidth + 1)) = 520 := by
  rw [Fin.sum_univ_add (a := 17) (b := 17)]
  simp only [chronologicalIndex_first, chronologicalIndex_second]
  exact congrArg₂ (fun first second : Nat => first + second)
    (chronological_stream_activeWidth 0) (chronological_stream_activeWidth 1)

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

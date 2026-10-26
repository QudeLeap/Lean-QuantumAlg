/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Chronology
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.WindowCoordinates

/-!
# The actual chronological Fourier widths and original result positions

Each original stream executes its high four-bit block followed by sixteen
full sixteen-bit blocks. The symbolic prefix length equals the real native
feedback start, and every symbolic window coordinate is its original result
cell position. The physical wires and bit order are unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

/-- The original high-first widths of either complete 260-bit stream. -/
abbrev fourierWidths : List Nat := 4 :: List.replicate 16 16

/-- Each original stream has the same seventeen actual windows. -/
lemma fourierWidths_length : fourierWidths.length = 17 := rfl

/-- The symbolic width is the full original source width. -/
lemma fourierWidths_total : Partner.windowWidth fourierWidths = 260 := by
  rw [Partner.qftPartner_windowWidth_sum]
  simp [fourierWidths]

private lemma get_cons_replicate (head width count : Nat) (position : Fin count) :
    (head :: List.replicate count width).get
      ⟨position.val + 1, by
        simp only [List.length_cons, List.length_replicate]
        exact Nat.succ_lt_succ position.isLt⟩ = width := by
  simp only [List.get_eq_getElem, List.getElem_cons_succ, List.getElem_replicate]

/-- Each chronological symbolic block has exactly the actual active bank width. -/
lemma fourierWidths_get (stream : Fin 2) (position : Fin 17) :
    fourierWidths.get position = (WindowIndex.mk stream position.rev).lowerWidth + 1 := by
  rw [stream_width]
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      exact (get_cons_replicate 4 16 16 position).trans
        (if_neg (Nat.succ_ne_zero position.val)).symm

/-- The accumulated symbolic prefix is exactly the native feedback start. -/
lemma fourierWidths_prefix (stream : Fin 2) (position : Fin 17) :
    Partner.windowWidth (fourierWidths.take position.val) =
      (WindowIndex.mk stream position.rev).start := by
  rw [Partner.qftPartner_windowWidth_sum, stream_start]
  cases position using Fin.cases with
  | zero => rfl
  | succ position =>
      have bounded : position.val ≤ 16 := position.isLt.le
      change (4 :: (List.replicate 16 16).take position.val).sum =
        4 + 16 * position.val
      rw [List.sum_cons, List.take_replicate, Nat.min_eq_left bounded, List.sum_replicate,
        nsmul_eq_mul, Nat.mul_comm]
      rfl

/-- Every symbolic window bit is the same original output position of the actual sampler. -/
lemma fourierWidths_position {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
    (stream : Fin 2) (position : Fin 17) (bit : Fin (fourierWidths.get position)) :
    Fin.cast fourierWidths_total (Partner.windowPosition fourierWidths position bit) =
      (parameters.ports (WindowIndex.mk stream position.rev)).position
        (Fin.cast (fourierWidths_get stream position) bit) := by
  apply Fin.ext
  change (Partner.windowPosition fourierWidths position bit).val =
    (WindowIndex.mk stream position.rev).start + bit.val
  rw [Partner.windowPosition_val]
  have samePrefix := fourierWidths_prefix stream position
  rw [Partner.qftPartner_windowWidth_sum] at samePrefix
  rw [samePrefix]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

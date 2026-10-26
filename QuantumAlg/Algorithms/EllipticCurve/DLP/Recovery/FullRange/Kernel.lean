/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.CyclicFourier
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Support
import all QuantumAlg.Algorithms.QPE.Analysis

/-!
# Exact full-range cyclic-character Fourier mixture

The source is uniform on both complete physical exponent registers.  Point
evaluation uses the affine cyclic label `seed + left - secret * right`.
Parseval on the arbitrary subgroup order gives the exact uniform character
mixture of two full-grid geometric kernels.  The right frequency has the
negative secret sign consumed by candidate recovery.  No power-of-two group
order or divisibility assumption is used.
-/

namespace QuantumAlg.EllipticCurve.FullRange

open scoped BigOperators

noncomputable section

variable {order : Nat} [NeZero order]

/-- A full-range prepared amplitude followed by the certified inverse-Fourier row. -/
def rawFourierCoefficient (width : Nat) (raw source : Fin (2 ^ width)) : ℂ :=
  invQFT width raw source * exponentState width source

private lemma character_nat_mul (frequency : ZMod order) (source : Nat) :
    ZMod.stdAddChar (frequency * (source : ZMod order)) =
      Complex.exp (2 * Real.pi * ((frequency.val : ℝ) / order) * source * Complex.I) := by
  have represented : frequency * (source : ZMod order) =
      (((frequency.val * source : Nat) : Int) : ZMod order) := by
    calc
      _ = (frequency.val : ZMod order) * (source : ZMod order) := by
        rw [ZMod.natCast_zmod_val]
      _ = ((frequency.val * source : Nat) : ZMod order) := (Nat.cast_mul _ _).symm
      _ = _ := by simp only [Int.cast_natCast]
  rw [represented, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private lemma character_uniform (width : Nat) (frequency : ZMod order)
    (source : Fin (2 ^ width)) :
    ZMod.stdAddChar (frequency * (source.val : ZMod order)) * exponentState width source =
      phaseState width ((frequency.val : ℝ) / order) source := by
  rw [character_nat_mul, exponentState_apply, phaseState_apply]
  have normalizer : FiniteCyclicDLP.invSqrtOrder (2 ^ width) = invSqrtN width := by
    simp only [FiniteCyclicDLP.invSqrtOrder, invSqrtN, Nat.cast_pow, Nat.cast_ofNat]
  rw [normalizer]
  rw [mul_comm _ (invSqrtN width)]
  congr 2
  push_cast
  ring

/-- The exact character-weighted full-range inverse-Fourier sum is the
geometric amplitude used by the strict-window tail analysis. -/
lemma characterFourierSum_eq_geometric (width : Nat) (frequency : ZMod order)
    (raw : Fin (2 ^ width)) :
    (∑ source : Fin (2 ^ width), ZMod.stdAddChar (frequency * (source.val : ZMod order)) *
      rawFourierCoefficient width raw source) =
      phaseRegisterGeometricAmplitude width ((frequency.val : ℝ) / order) raw := by
  calc
    _ = ∑ source : Fin (2 ^ width), invQFT width raw source *
        (ZMod.stdAddChar (frequency * (source.val : ZMod order)) *
          exponentState width source) := by
      apply Finset.sum_congr rfl
      intro source _
      unfold rawFourierCoefficient
      ring
    _ = ∑ source : Fin (2 ^ width), invQFT width raw source *
        phaseState width ((frequency.val : ℝ) / order) source := by
      simp_rw [character_uniform]
    _ = _ := invQFT_phaseState_apply_geometricSum width ((frequency.val : ℝ) / order) raw

/-- The full physical two-register Fourier amplitude on one cyclic evaluation fiber. -/
def idealKernel (width : Nat) (seed secret : ZMod order)
    (leftRaw rightRaw : Fin (2 ^ width)) (output : ZMod order) : ℂ :=
  CyclicFourier.fiberAmplitude
    (fun branch : Branch width => seed + (branch.1.val : ZMod order) +
      (-secret * (branch.2.val : ZMod order)))
    (fun branch => rawFourierCoefficient width leftRaw branch.1 *
      rawFourierCoefficient width rightRaw branch.2) output

/-- Exact full-range Born mass is the uniform cyclic-character mixture with
the left/right sign convention required by nearest candidate recovery. -/
lemma idealKernel_square_sum_eq_mixture (width : Nat) (seed secret : ZMod order)
    (leftRaw rightRaw : Fin (2 ^ width)) :
    (∑ output : ZMod order, ‖idealKernel width seed secret leftRaw rightRaw output‖ ^ 2) =
      (order : ℝ)⁻¹ * ∑ frequency : ZMod order,
        ‖phaseRegisterGeometricAmplitude width ((frequency.val : ℝ) / order) leftRaw‖ ^ 2 *
        ‖phaseRegisterGeometricAmplitude width
          (((-secret * frequency).val : ℝ) / order) rightRaw‖ ^ 2 := by
  have factor := CyclicFourier.pair_fiberAmplitude_square_sum seed
    (fun source : Fin (2 ^ width) => (source.val : ZMod order))
    (fun source : Fin (2 ^ width) => -secret * (source.val : ZMod order))
    (rawFourierCoefficient width leftRaw) (rawFourierCoefficient width rightRaw)
  refine factor.trans ?_
  congr 1
  apply Finset.sum_congr rfl
  intro frequency _
  rw [characterFourierSum_eq_geometric]
  have rightFactor :
      (∑ source : Fin (2 ^ width),
        ZMod.stdAddChar (frequency * (-secret * (source.val : ZMod order))) *
        rawFourierCoefficient width rightRaw source) =
      phaseRegisterGeometricAmplitude width (((-secret * frequency).val : ℝ) / order)
        rightRaw := by
    convert characterFourierSum_eq_geometric width (-secret * frequency) rightRaw using 1
    apply Finset.sum_congr rfl
    intro source _
    congr 2
    ring
  rw [rightFactor]

end

end QuantumAlg.EllipticCurve.FullRange

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Util.NearestResidue

/-!
# Strict cyclic phase windows imply nearest-residue recovery

The periodic distance is the same principal-error distance used by the Fourier
tail analysis.  Its integer lift handles either sign and both ends of the
physical Fourier grid.  The strict radius excludes half-residue ties.
-/

namespace QuantumAlg.EllipticCurve.FullRange

/-- The physical Fourier modulus is even for every nonempty exponent register. -/
lemma physicalModulus_even (width : Nat) (positive : 0 < width) :
    2 * (2 ^ width / 2) = 2 ^ width := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simp only [pow_succ]
  omega

/-- Nearest rescaling recovers the intended residue on the actual strict cyclic
window, including the wrap at either end of the Fourier register. -/
lemma nearest_mod_eq_of_phase_window (width order residue : Nat)
    (widthPositive : 0 < width) (orderPositive : 0 < order) (belowOrder : residue < order)
    (raw : Fin (2 ^ width))
    (window : qpePhaseDistance width ((residue : ℝ) / order) raw <
      1 / (2 * order)) :
    NearestResidue.quotient (raw.val * order) (2 ^ width) % order = residue := by
  apply NearestResidue.quotient_mod_eq_of_strict_window raw.val (2 ^ width) order residue
    orderPositive (Nat.two_pow_pos width) (physicalModulus_even width widthPositive) belowOrder
    (round ((residue : ℝ) / order - (raw.val : ℝ) / (2 : ℝ) ^ width))
  simpa only [qpePhaseDistance_eq_abs_principalError, qpePrincipalError,
    Nat.cast_pow, Nat.cast_ofNat] using window

end QuantumAlg.EllipticCurve.FullRange

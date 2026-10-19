/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.GroupTheory.OrderOfElement

/-!
# Collision-free integer powers below the element order

The lemmas here are purely group-theoretic.  They are used to replace equality
of encoded cyclic-group values by equality of bounded integer exponents.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- Two integer powers of the same group element cannot collide when the
absolute exponent difference is strictly smaller than the element order. -/
lemma zpow_eq_zpow_iff_of_abs_sub_lt_orderOf
    {G : Type*} [Group G] (g : G) (left right : Int)
    (hsmall : |left - right| < (orderOf g : Int)) :
    g ^ left = g ^ right ↔ left = right := by
  constructor
  · intro hpowers
    have hdvd : (orderOf g : Int) ∣ left - right :=
      orderOf_dvd_sub_iff_zpow_eq_zpow.mpr hpowers
    exact Int.sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hsmall)
  · intro h
    rw [h]

end NumberTheory
end QuantumAlg

end

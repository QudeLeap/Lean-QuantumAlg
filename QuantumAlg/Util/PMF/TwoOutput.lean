/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.PMF
import all QuantumAlg.Util.PMF

/-! # Exact success mass when only failure and one answer can occur -/

namespace QuantumAlg.PMF

noncomputable section

/-- Two distinct outputs carry all mass when every other output has zero mass. -/
public lemma two_output_mass {Value : Type} [Finite Value]
    (distribution : PMF Value) (left right : Value) (distinct : left ≠ right)
    (zero : ∀ value, value ≠ left → value ≠ right → distribution value = 0) :
    distribution left + distribution right = 1 := by
  classical
  let := Fintype.ofFinite Value
  have restricted : (∑ value ∈ ({left, right} : Finset Value), distribution value) =
      ∑ value, distribution value := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro value _ excluded
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at excluded
    exact zero value excluded.1 excluded.2
  have total : (∑ value ∈ ({left, right} : Finset Value), distribution value) = 1 :=
    restricted.trans (by simpa only [tsum_fintype] using distribution.tsum_coe)
  simpa [distinct] using total

/-- An upper bound on the sole failure atom gives the complementary success floor. -/
public lemma success_ge_of_failure_le {Value : Type} [Finite Value]
    (distribution : PMF Value) (failure success : Value) (distinct : failure ≠ success)
    (zero : ∀ value, value ≠ failure → value ≠ success → distribution value = 0)
    (upper : ENNReal) (bound : distribution failure ≤ upper) :
    1 - upper ≤ distribution success := by
  have total := two_output_mass distribution failure success distinct zero
  have complement : 1 - distribution failure ≤ distribution success := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using total.symm.le
  exact (tsub_le_tsub_left bound 1).trans complement

end

end QuantumAlg.PMF

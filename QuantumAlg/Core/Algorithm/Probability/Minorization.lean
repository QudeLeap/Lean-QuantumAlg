/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.PMF
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite probability-mass minorization

A pointwise lower bound on a finite collection of atoms can be split from a
probability mass function as an explicit Boolean-marked coupling.  Forgetting
the mark recovers the original distribution exactly; the marked branch has the
constant mass prescribed by the lower bound.  This is a proof-side coupling,
not a replacement distribution supplied by an algorithm caller.
-/

section

namespace QuantumAlg
namespace PMF

noncomputable section

variable {Sample : Type} [DecidableEq Sample]

/-- Weight of one atom in the Boolean-marked minorization coupling. -/
def fractionalMarkingWeight (distribution : PMF Sample)
    (core : Finset Sample) (floor : ENNReal) (sample : Sample × Bool) :
    ENNReal :=
  if sample.2 then
    if sample.1 ∈ core then floor else 0
  else
    distribution sample.1 - if sample.1 ∈ core then floor else 0

/-- Split a constant pointwise floor from every atom in `core`.  The proof
argument guarantees that the residual branch is nonnegative and that the two
branches still sum to the original probability mass. -/
def fractionalMarking (distribution : PMF Sample) (core : Finset Sample)
    (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample) :
    PMF (Sample × Bool) :=
  ⟨fractionalMarkingWeight distribution core floor, by
    have hsum :
        (∑' sample : Sample × Bool,
          fractionalMarkingWeight distribution core floor sample) = 1 := by
      rw [ENNReal.tsum_prod']
      simp only [tsum_fintype, Fintype.sum_bool]
      calc
        (∑' sample : Sample,
            (fractionalMarkingWeight distribution core floor (sample, true) +
              fractionalMarkingWeight distribution core floor (sample, false))) =
            ∑' sample : Sample, distribution sample := by
          apply tsum_congr
          intro sample
          by_cases hcore : sample ∈ core
          · simpa [fractionalMarkingWeight, hcore] using
              add_tsub_cancel_of_le (hfloor sample hcore)
          · simp [fractionalMarkingWeight, hcore]
        _ = 1 := distribution.tsum_coe
    rw [← hsum]
    exact ENNReal.summable.hasSum⟩

@[simp] lemma fractionalMarking_apply_true
    (distribution : PMF Sample) (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample)
    (sample : Sample) :
    fractionalMarking distribution core floor hfloor (sample, true) =
      if sample ∈ core then floor else 0 :=
  rfl

@[simp] lemma fractionalMarking_apply_false
    (distribution : PMF Sample) (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample)
    (sample : Sample) :
    fractionalMarking distribution core floor hfloor (sample, false) =
      distribution sample - if sample ∈ core then floor else 0 :=
  rfl

/-- Forgetting the proof-only mark recovers the original PMF exactly. -/
lemma fractionalMarking_map_fst (distribution : PMF Sample)
    (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample) :
    (fractionalMarking distribution core floor hfloor).map Prod.fst =
      distribution := by
  apply PMF.ext
  intro sample
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp only [tsum_fintype, Fintype.sum_bool]
  rw [tsum_eq_single sample]
  · by_cases hcore : sample ∈ core
    · simpa [fractionalMarkingWeight, hcore] using
        add_tsub_cancel_of_le (hfloor sample hcore)
    · simp [hcore]
  · intro other hne
    simp [hne.symm]

/-- The total marked mass is exactly the number of selected atoms multiplied
by their common pointwise floor. -/
lemma fractionalMarking_markedMass (distribution : PMF Sample)
    (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample) :
    (fractionalMarking distribution core floor hfloor).toOuterMeasure
        {sample | sample.2} =
      core.card * floor := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_prod']
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  simp only [tsum_fintype, Fintype.sum_bool, fractionalMarking_apply_true,
    fractionalMarking_apply_false]
  rw [tsum_eq_sum (s := core)]
  · simp [nsmul_eq_mul]
  · intro sample hsample
    simp [hsample]

/-- The marked branch restricted to the selected core has the same exact
mass.  Carrying core membership in the event makes later transcript arguments
purely set-theoretic, including on zero-mass atoms. -/
lemma fractionalMarking_markedCoreMass (distribution : PMF Sample)
    (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample) :
    (fractionalMarking distribution core floor hfloor).toOuterMeasure
        {sample | sample.2 ∧ sample.1 ∈ core} =
      core.card * floor := by
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_prod']
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, tsum_fintype,
    Fintype.sum_bool, fractionalMarking_apply_true,
    fractionalMarking_apply_false]
  rw [tsum_eq_sum (s := core)]
  · simp [nsmul_eq_mul]
  · intro sample hsample
    simp [hsample]

/-- Lift a finite relation carrier to pairs whose two proof-side marks are
both true. -/
def markedPairCarrier (bad : Finset (Sample × Sample)) :
    Finset ((Sample × Bool) × (Sample × Bool)) :=
  bad.map ((Function.Embedding.sectL Sample true).prodMap
    (Function.Embedding.sectL Sample true))

omit [DecidableEq Sample] in
@[simp] lemma mem_markedPairCarrier_iff
    (bad : Finset (Sample × Sample))
    (pair : (Sample × Bool) × (Sample × Bool)) :
    pair ∈ markedPairCarrier bad ↔
      pair.1.2 = true ∧ pair.2.2 = true ∧
        (pair.1.1, pair.2.1) ∈ bad := by
  classical
  constructor
  · intro hpair
    rw [markedPairCarrier, Finset.mem_map] at hpair
    rcases hpair with ⟨underlying, hunderlying, rfl⟩
    exact ⟨rfl, rfl, hunderlying⟩
  · rcases pair with ⟨⟨first, firstMark⟩, ⟨second, secondMark⟩⟩
    rintro ⟨rfl, rfl, hunderlying⟩
    rw [markedPairCarrier, Finset.mem_map]
    exact ⟨(first, second), hunderlying, rfl⟩

/-- Exact mass of a finite marked relation under two independent coupling
draws.  No probability is normalized or conditioned here: every marked core
atom has the same literal mass `floor`. -/
lemma independentPair_fractionalMarking_markedBadMass
    (distribution : PMF Sample) (core : Finset Sample) (floor : ENNReal)
    (hfloor : ∀ sample ∈ core, floor ≤ distribution sample)
    (bad : Finset (Sample × Sample))
    (hbad : ∀ pair ∈ bad, pair.1 ∈ core ∧ pair.2 ∈ core) :
    (PMF.independentPair (fractionalMarking distribution core floor hfloor)).toOuterMeasure
        (markedPairCarrier bad) =
      bad.card * floor ^ 2 := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [markedPairCarrier, Finset.sum_map,
    Function.Embedding.coe_prodMap]
  calc
    (∑ pair ∈ bad,
        PMF.independentPair (fractionalMarking distribution core floor hfloor)
          ((pair.1, true), (pair.2, true))) =
        ∑ _pair ∈ bad, floor ^ 2 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [PMF.independentPair_apply]
      have hcore := hbad pair hpair
      simp [hcore.1, hcore.2, pow_two]
    _ = bad.card * floor ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]

end

end PMF
end QuantumAlg

end

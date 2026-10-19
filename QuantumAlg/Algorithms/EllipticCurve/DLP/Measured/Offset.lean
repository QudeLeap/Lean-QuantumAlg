/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.PreparedSupport
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Logic.Equiv.Fintype

/-!
# A fixed original subgroup offset with the original exceptional-mass bound

Finite averaging over all nonidentity elements of the original generated
subgroup chooses one affine seed. The prepared support has exactly order-squared
branches and keeps its original reciprocal-square amplitudes. Consequently the
original two-exceptions-per-step count yields the original mass bound, with no
caller-supplied candidate family and no stricter denominator domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Exactly the nonidentity elements of the original cyclic subgroup are candidate offsets. -/
def candidateOffsets (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) :
    Finset (GroupPoint E) := by
  classical
  have generatorFiniteOrder : IsOfFinOrder problem.generator := by
    rw [← orderOf_pos_iff, ← problem.order_eq_orderOf]
    exact problem.order_pos
  have subgroupFinite : (Subgroup.zpowers problem.generator : Set (GroupPoint E)).Finite :=
    generatorFiniteOrder.finite_zpowers
  let _ : Fintype (Subgroup.zpowers problem.generator) := subgroupFinite.fintype
  exact (Subgroup.zpowers problem.generator : Set (GroupPoint E)).toFinset.erase 1

/-- Candidate membership records the original subgroup and the explicit nonidentity condition. -/
lemma mem_candidateOffsets (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (offset : GroupPoint E) :
    offset ∈ candidateOffsets problem ↔
      offset ∈ Subgroup.zpowers problem.generator ∧ offset ≠ 1 := by
  classical
  unfold candidateOffsets
  simp only [Finset.mem_erase, Set.mem_toFinset, SetLike.mem_coe]
  tauto

/-- Removing the identity leaves exactly the original order minus one candidates. -/
lemma candidateOffsets_card (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) :
    (candidateOffsets problem).card = problem.order - 1 := by
  classical
  have generatorFiniteOrder : IsOfFinOrder problem.generator := by
    rw [← orderOf_pos_iff, ← problem.order_eq_orderOf]
    exact problem.order_pos
  have subgroupFinite : (Subgroup.zpowers problem.generator : Set (GroupPoint E)).Finite :=
    generatorFiniteOrder.finite_zpowers
  let _ : Fintype (Subgroup.zpowers problem.generator) := subgroupFinite.fintype
  have identityMember : (1 : GroupPoint E) ∈
      (Subgroup.zpowers problem.generator : Set (GroupPoint E)).toFinset := by
    simpa only [Set.mem_toFinset, SetLike.mem_coe] using
      (Subgroup.zpowers problem.generator).one_mem
  unfold candidateOffsets
  rw [Finset.card_erase_of_mem identityMember, Set.toFinset_card, ← Nat.card_eq_fintype_card]
  change Nat.card (Subgroup.zpowers problem.generator) - 1 = problem.order - 1
  rw [Nat.card_zpowers, ← problem.order_eq_orderOf]

/-- Every original problem of order at least two supplies a nonidentity offset candidate. -/
lemma candidateOffsets_nonempty
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (orderAtLeastTwo : 2 ≤ problem.order) : (candidateOffsets problem).Nonempty := by
  rw [← Finset.card_pos, candidateOffsets_card]
  omega

/-- A nonidentity group point has its exact finite affine representative. -/
lemma exists_affineRepresentative (point : GroupPoint E) (nonidentity : point ≠ 1) :
    ∃ representative : AffinePoint E, representative.toGroupPoint = point := by
  rcases point with ⟨point⟩
  cases point with
  | zero => exact False.elim (nonidentity rfl)
  | some x y nonsingular => exact ⟨⟨x, y, nonsingular⟩, rfl⟩

/-- One fixed affine seed obeys the original two-exceptions-per-step count on prepared branches. -/
lemma exists_fixedOffset_exceptional_card_bound
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (orderAtLeastTwo : 2 ≤ problem.order)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ candidateOffsets problem ∧
        (problem.order - 1) * (preparedExceptionalBranches problem points seed).card ≤
          (problem.order * problem.order) * (2 * (2 * FiniteCyclicDLP.orderWidth problem)) := by
  classical
  obtain ⟨offset, member, bound⟩ := ExceptionalOffsetAveraging.exists_fixed_offset
    (candidateOffsets problem) (preparedSourceBranches problem)
    (candidateOffsets_nonempty problem orderAtLeastTwo)
    (2 * FiniteCyclicDLP.orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (FiniteCyclicDLP.orderWidth problem))
    (fun index => (points index).toGroupPoint)
  obtain ⟨seed, seedGroup⟩ := exists_affineRepresentative offset
    ((mem_candidateOffsets problem offset).mp member).2
  refine ⟨seed, ?_, ?_⟩
  · simpa only [seedGroup] using member
  · rw [candidateOffsets_card, preparedSourceBranches_card] at bound
    simpa only [preparedExceptionalBranches, seedGroup] using bound

/-- An original exceptional count bound gives the exact corresponding Born-mass bound. -/
lemma preparedExceptionalMass_le_of_card_bound
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) (budget : Nat) (orderAtLeastTwo : 2 ≤ problem.order)
    (cardBound : (problem.order - 1) * (preparedExceptionalBranches problem points seed).card ≤
      (problem.order * problem.order) * budget) :
    preparedExceptionalMass problem points seed ≤
      (budget : ℝ) / ((problem.order - 1 : Nat) : ℝ) := by
  have orderPositive : 0 < (problem.order : ℝ) := by
    exact_mod_cast problem.order_pos
  have predecessorPositive : 0 < ((problem.order - 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le Nat.one_lt_two orderAtLeastTwo)
  have cardBoundReal :
      ((((problem.order - 1) * (preparedExceptionalBranches problem points seed).card : Nat) : ℝ) ≤
        (((problem.order * problem.order) * budget : Nat) : ℝ)) := by
    exact_mod_cast cardBound
  rw [preparedExceptionalMass_eq_card_mul_inv_sq]
  have massForm : ((preparedExceptionalBranches problem points seed).card : ℝ) *
      ((problem.order : ℝ)⁻¹ * (problem.order : ℝ)⁻¹) =
      ((preparedExceptionalBranches problem points seed).card : ℝ) /
        ((problem.order : ℝ) * (problem.order : ℝ)) := by
    field_simp
  rw [massForm]
  refine (div_le_div_iff₀ (mul_pos orderPositive orderPositive) predecessorPositive).2 ?_
  simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using cardBoundReal

/-- One original nonidentity subgroup seed has the original exceptional-mass constant. -/
lemma exists_fixedOffset_exceptionalMass_bound
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (orderAtLeastTwo : 2 ≤ problem.order)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧ seed.toGroupPoint ≠ 1 ∧
        preparedExceptionalMass problem points seed ≤
          (2 * (2 * FiniteCyclicDLP.orderWidth problem) : Nat) /
            ((problem.order - 1 : Nat) : ℝ) := by
  obtain ⟨seed, member, bound⟩ :=
    exists_fixedOffset_exceptional_card_bound problem orderAtLeastTwo points
  exact ⟨seed, ((mem_candidateOffsets problem seed.toGroupPoint).mp member).1,
    ((mem_candidateOffsets problem seed.toGroupPoint).mp member).2,
    preparedExceptionalMass_le_of_card_bound problem points seed _ orderAtLeastTwo bound⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

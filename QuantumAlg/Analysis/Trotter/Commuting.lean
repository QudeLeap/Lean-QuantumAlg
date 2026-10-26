/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Noncommutative
public import QuantumAlg.Analysis.Trotter.Evolution
public import QuantumAlg.Analysis.Trotter.Family

/-!
# Exact product formulas for commuting Hamiltonians

The first-order product formula is exact for commuting summands, both for two
terms and finite ordered families [CMN+18, simalg.tex:21; pfappendix.tex:191].
The finite-family result admits every real time, nonzero step count, empty
families and empty register index spaces.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

/-- Exact one-step finite-family first-order product formula for pairwise
commuting Hamiltonian terms. -/
lemma timeEvolution_eq_finiteTrotterStep_of_pairwise_commute
    {R : Register} {L : ℕ} (terms : HamiltonianFamily R L)
    (hcomm : PairwiseCommute terms) (t : ℝ) :
    timeEvolution (Hamiltonian.sum terms) t = finiteFirstOrderTrotterStep terms t := by
  apply Subtype.ext
  change timeEvolutionOp (Hamiltonian.sum terms : HilbertOperator R) t =
    ((finiteFirstOrderTrotterStep terms t : UnitaryOperator R) : HilbertOperator R)
  classical
  let c : ℂ := -(Complex.I * (t : ℂ))
  have hscaled : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun Commute fun j : Fin L => c • (terms j : HilbertOperator R)) := by
    intro i _ j _ _
    exact (hcomm i j).smul_left c |>.smul_right c
  have hstepCommUniv : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun Commute fun j : Fin L =>
        timeEvolutionOp (terms j : HilbertOperator R) t) := by
    intro i _ j _ _
    exact ((hcomm i j).smul_left c |>.smul_right c).exp
  rw [timeEvolutionOp, Hamiltonian.coe_sum, coe_finiteFirstOrderTrotterStep]
  change NormedSpace.exp (c • ∑ j : Fin L, (terms j : HilbertOperator R))
    = (List.ofFn fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) t).prod
  rw [Finset.smul_sum]
  rw [Matrix.exp_sum_of_commute Finset.univ
    (fun j : Fin L => c • (terms j : HilbertOperator R)) hscaled]
  have hstepCommRange :
      (((List.finRange L).toFinset : Finset (Fin L)) : Set (Fin L)).Pairwise
        (Function.onFun Commute fun j : Fin L =>
          timeEvolutionOp (terms j : HilbertOperator R) t) := by
    simpa [List.toFinset_finRange] using hstepCommUniv
  have hnoncomm := Finset.noncommProd_toFinset (List.finRange L)
      (fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) t)
      hstepCommRange
      (List.nodup_finRange L)
  simpa [timeEvolutionOp, c, List.ofFn_eq_map,
    List.toFinset_finRange] using hnoncomm

/-- Exact one-step product formula for commuting Hamiltonian operators. -/
lemma timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute {R : Register}
    {H₁ H₂ : HilbertOperator R} (hcomm : Commute H₁ H₂) (t : ℝ) :
    timeEvolutionOp (H₁ + H₂) t = firstOrderTrotterStepOp H₁ H₂ t := by
  rw [timeEvolutionOp, firstOrderTrotterStepOp, timeEvolutionOp, timeEvolutionOp, smul_add]
  apply Matrix.exp_add_of_commute
  exact hcomm.smul_left _ |>.smul_right _

/-- Exact repeated finite-family first-order product formula for pairwise
commuting Hamiltonian terms. -/
public theorem timeEvolution_eq_finiteTrotterProduct_of_pairwise_commute
    {R : Register} {L : ℕ} (terms : HamiltonianFamily R L)
    (hcomm : PairwiseCommute terms) {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    timeEvolution (Hamiltonian.sum terms) t = finiteFirstOrderTrotterProduct terms t r := by
  rw [finiteFirstOrderTrotterProduct]
  rw [← timeEvolution_eq_finiteTrotterStep_of_pairwise_commute terms hcomm (t / (r : ℝ))]
  apply Subtype.ext
  change timeEvolutionOp (Hamiltonian.sum terms : HilbertOperator R) t =
    (timeEvolutionOp (Hamiltonian.sum terms : HilbertOperator R) (t / (r : ℝ))) ^ r
  exact (timeEvolutionOp_pow_div (Hamiltonian.sum terms : HilbertOperator R) hr t).symm

namespace TrotterProductFormula

/-- Exact repeated first-order Trotter product formula for commuting Hamiltonian
summands.  This is the zero-error boundary of the product-formula method; the
noncommuting approximation bound is intentionally not claimed here. -/
lemma commuting_exact {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
      = firstOrderTrotterProductOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r := by
  rw [firstOrderTrotterProductOp]
  rw [← timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute hcomm (t / (r : ℝ))]
  exact (timeEvolutionOp_pow_div
    ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) hr t).symm

/-- The explicit Trotter error operator vanishes for commuting Hamiltonian
summands and nonzero step count. -/
lemma error_eq_zero_of_commute {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    firstOrderTrotterErrorOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r = 0 := by
  rw [firstOrderTrotterErrorOp, commuting_exact H₁ H₂ hcomm hr t, sub_self]

end TrotterProductFormula

end

end QuantumAlg

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.SelectionAll

/-!
# A pure basis promise from exact matrix support

The reset endpoint uses exact zero rows of its observed density operator to
establish a pure basis-state promise. Positivity supplies Hermitian symmetry;
the remaining diagonal coefficient is the original probability mass.
The target is the pure-state outer product [dW19, qcnotes.tex:5381], with no
division or normalization of an impossible observation.
-/

namespace QuantumAlg.StatePromise

noncomputable section

open scoped ComplexOrder

/-- A probability-bearing density operator supported on one basis label has
exactly that pure-state promise at its original mass. -/
public lemma statePromise_pureKet_of_row_support {R : Register}
    (state : DensityOperator R) (basis : R.Index)
    (support : ∀ row, row ≠ basis → ∀ column, state.matrix row column = 0) :
    (StatePromise.pure (NormalizedVector.ket basis)).Holds state := by
  have traceEq : state.matrix.trace = state.matrix basis basis := by
    change (∑ row : R.Index, state.matrix row row) = state.matrix basis basis
    apply Finset.sum_eq_single basis
    · intro row _ different
      exact support row different row
    · intro absent
      exact False.elim (absent (Finset.mem_univ basis))
  have diagonal : state.matrix basis basis = (state.mass : ℂ) := by
    apply Complex.ext
    · change (state.matrix basis basis).re = state.matrix.trace.re
      exact congrArg Complex.re traceEq.symm
    · exact (congrArg Complex.im traceEq.symm).trans state.trace_im_eq_zero
  have otherColumn (column : R.Index) (different : column ≠ basis) :
      state.matrix basis column = 0 := by
    rw [← state.positive.isHermitian.apply basis column, support column different basis]
    exact star_zero ℂ
  change state.matrix = (state.mass : ℝ) •
    (DensityOperator.ofPure (NormalizedVector.ket basis)).matrix
  ext row column
  change state.matrix row column = state.mass •
    (DensityOperator.ofPure (NormalizedVector.ket basis)).matrix row column
  rw [DensityOperator.ofPure_matrix]
  by_cases sameRow : row = basis <;> by_cases sameColumn : column = basis
  · subst row
    subst column
    simpa only [NormalizedVector.ket_apply, if_true, star_one, mul_one,
      Complex.real_smul] using diagonal
  · subst row
    simp only [otherColumn column sameColumn, NormalizedVector.ket_apply,
      if_neg sameColumn, star_zero, mul_zero, smul_zero]
  · simp only [support row sameRow column, NormalizedVector.ket_apply,
      if_neg sameRow, zero_mul, smul_zero]
  · simp only [support row sameRow column, NormalizedVector.ket_apply,
      if_neg sameRow, zero_mul, smul_zero]

/-- A full joint-coordinate relabeling that preserves the local basis value
also preserves a fixed pure local ket, even when the reference coordinates
depend on the local value. No assumption of a product reference state is needed. -/
lemma pureKet_marginal_of_reindex_first {R Reference EncodedReference : Register}
    (state : DensityOperator (Register.prod R Reference))
    (basis : (Register.prod R Reference).Index ≃
      (Register.prod R EncodedReference).Index)
    (first : ∀ input, (basis input).1 = input.1) (seed : R.Index)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (state.reindex basis).marginalLeft) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds state.marginalLeft := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  let input : (Register.prod R Reference).Index := (row, reference)
  have encodedDifferent : (basis input).1 ≠ seed := by
    simpa only [first input] using different
  have zeroDiagonal :
      ((state.reindex basis).marginalLeft).matrix
        (basis input).1 (basis input).1 = 0 := by
    have diagonal := congrArg (fun matrix : HilbertOperator R =>
      matrix (basis input).1 (basis input).1) promised
    change ((state.reindex basis).marginalLeft).matrix
      (basis input).1 (basis input).1 =
        ((state.reindex basis).marginalLeft).mass •
          (DensityOperator.ofPure (NormalizedVector.ket seed)).matrix
            (basis input).1 (basis input).1 at diagonal
    rw [DensityOperator.ofPure_matrix] at diagonal
    simpa only [NormalizedVector.ket_apply, if_neg encodedDifferent,
      star_zero, zero_mul, mul_zero, smul_zero] using diagonal
  have zeroRow := DensityOperator.joint_row_zero_of_marginal_diagonal_zero
    (state.reindex basis) (basis input).1 zeroDiagonal (basis input).2
      (basis (column, reference))
  have transferred :
      (state.reindex basis).matrix (basis input) (basis (column, reference)) =
        state.matrix input (column, reference) := by
    rw [DensityOperator.reindex_entry]
    simp only [Equiv.symm_apply_apply]
  exact transferred.symm.trans (by simpa only [Prod.mk.eta] using zeroRow)

/-- The same full-coordinate transport applies to the physical observation of
every quantum wire. It keeps the actual probability mass and arbitrary
external-reference correlations. -/
lemma pureKet_fullSelection_of_reindex_first {count : Nat}
    (layout : QuantumLayout count) {Reference EncodedReference : Register}
    (state : DensityOperator (Register.prod layout.register Reference))
    (basis : (Register.prod layout.register Reference).Index ≃
      (Register.prod layout.register EncodedReference).Index)
    (first : ∀ input, (basis input).1 = input.1)
    (seed : (layout.selectedRegister Finset.univ).Index)
    (promised : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout Finset.univ EncodedReference
        (state.reindex basis))) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (DensityOperator.observeSelection layout Finset.univ Reference state) := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.observeSelection_all, DensityOperator.reindex_entry,
    DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  let localRow := layout.allSelectedBasisEquiv.symm row
  let localColumn := layout.allSelectedBasisEquiv.symm column
  let input : (Register.prod layout.register Reference).Index := (localRow, reference)
  have encodedDifferent : layout.allSelectedBasisEquiv (basis input).1 ≠ seed := by
    intro same
    apply different
    rw [first input] at same
    exact (layout.allSelectedBasisEquiv.apply_symm_apply row).symm.trans same
  have sourceDiagonal :
      ((state.reindex basis).marginalLeft).matrix
        (basis input).1 (basis input).1 = 0 := by
    have selectedDiagonal :
        (DensityOperator.observeSelection layout Finset.univ EncodedReference
          (state.reindex basis)).matrix
            (layout.allSelectedBasisEquiv (basis input).1)
            (layout.allSelectedBasisEquiv (basis input).1) = 0 := by
      have coefficient := congrArg
        (fun matrix : HilbertOperator (layout.selectedRegister Finset.univ) =>
          matrix (layout.allSelectedBasisEquiv (basis input).1)
            (layout.allSelectedBasisEquiv (basis input).1)) promised
      change _ =
        (DensityOperator.observeSelection layout Finset.univ EncodedReference
          (state.reindex basis)).mass •
          (DensityOperator.ofPure (NormalizedVector.ket seed)).matrix
            (layout.allSelectedBasisEquiv (basis input).1)
            (layout.allSelectedBasisEquiv (basis input).1) at coefficient
      rw [DensityOperator.ofPure_matrix] at coefficient
      simpa only [NormalizedVector.ket_apply, if_neg encodedDifferent,
        star_zero, zero_mul, mul_zero, smul_zero] using coefficient
    rw [DensityOperator.observeSelection_all,
      DensityOperator.reindex_entry] at selectedDiagonal
    simpa only [Equiv.symm_apply_apply] using selectedDiagonal
  have zeroRow := DensityOperator.joint_row_zero_of_marginal_diagonal_zero
    (state.reindex basis) (basis input).1 sourceDiagonal (basis input).2
      (basis (localColumn, reference))
  have transferred :
      (state.reindex basis).matrix (basis input) (basis (localColumn, reference)) =
        state.matrix input (localColumn, reference) := by
    rw [DensityOperator.reindex_entry]
    simp only [Equiv.symm_apply_apply]
  exact transferred.symm.trans (by simpa only [Prod.mk.eta] using zeroRow)

end

end QuantumAlg.StatePromise

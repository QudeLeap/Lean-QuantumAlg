/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
public import QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Source singular invariant sectors

The projected-unitary singular decomposition and its unit, interior, kernel and
complement sectors are mathematical statements about certified operators
[GSLW19, BlockHam.tex:583-735]. Executable oracle access is specified separately.
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Select the alternating projector used at slot `k`. -/
def alternatingProjector {N : Nat} (left right : OrthogonalProjector N) (k : ℕ) :
    OrthogonalProjector N :=
  if k % 2 = 0 then left else right

/-- The parity-selected output projector `Π_L` in the projected-QSVT statement
[GSLW19, BlockHam.tex:883-887].  We use `left = \widetilde Π` and
`right = Π`, so odd `L` selects `left` and even `L` selects `right`. -/
public def projectedOutputProjector {N : Nat} (left right : OrthogonalProjector N) (L : ℕ) :
    OrthogonalProjector N :=
  if L % 2 = 0 then right else left

theorem projectedOutputProjector_eq_alternatingProjector {N : Nat}
    (left right : OrthogonalProjector N) (L : ℕ) :
    projectedOutputProjector left right L = alternatingProjector right left L := by
  by_cases hL : L % 2 = 0 <;> simp [projectedOutputProjector, alternatingProjector, hL]

@[simp]
theorem projectedOutputProjector_of_even {N : Nat}
    (left right : OrthogonalProjector N) {L : ℕ} (hL : L % 2 = 0) :
    projectedOutputProjector left right L = right := by
  simp [projectedOutputProjector, hL]

@[simp]
theorem projectedOutputProjector_of_odd {N : Nat}
    (left right : OrthogonalProjector N) {L : ℕ} (hL : L % 2 ≠ 0) :
    projectedOutputProjector left right L = left := by
  simp [projectedOutputProjector, hL]

/-- Source-level alternating phase modulation over a projected-unitary
encoding.  The current slot is chosen from the remaining phase-list length:
odd remaining length uses `\widetilde\Pi` followed by `U`, while even
remaining length uses `\Pi` followed by `U†`, matching
[GSLW19, BlockHam.tex:738-745]. -/
def sourcePhaseProjector {N : Nat} (left right : OrthogonalProjector N) (remaining : ℕ) :
    OrthogonalProjector N :=
  projectedOutputProjector left right remaining

/-- Source-aligned signal oracle in the projected-QSVT phase sequence:
odd remaining length uses `U`, even remaining length uses `U†`
[GSLW19, BlockHam.tex:738-745]. -/
def sourcePhaseSignal {N : Nat} (U : UnitaryOperator (Qubits N)) (remaining : ℕ) :
    UnitaryOperator (Qubits N) :=
  if remaining % 2 = 0 then U.dagger else U

/-- Left-complement vector candidate for the `0 < σ < 1` source sector in
`lemma:singInvDec`.  It is the normalized component of `U |v⟩` outside
`img \widetildeΠ` [GSLW19, BlockHam.tex:655-716]. -/
noncomputable def projectedUnitaryBlockLeftPerpCandidate {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertVector (Qubits N) :=
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)⁻¹ •
    HilbertOperator.applyVec (OrthogonalProjector.complement left) (U.applyVec pair.rightVec)

/-- Right-complement vector candidate for the `0 < σ < 1` source sector in
`lemma:singInvDec`.  It is the normalized component of `U† |w⟩` outside
`img Π` [GSLW19, BlockHam.tex:655-716]. -/
noncomputable def projectedUnitaryBlockRightPerpCandidate {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertVector (Qubits N) :=
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)⁻¹ •
    HilbertOperator.applyVec (OrthogonalProjector.complement right)
      (U.dagger.applyVec pair.leftVec)

/-- The left-complement candidate is supported on `I - \widetildeΠ`. -/
theorem projectedUnitaryBlockLeftPerpCandidate_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda) =
      projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
  unfold projectedUnitaryBlockLeftPerpCandidate
  rw [HilbertOperator.applyVec_smul]
  congr 1
  rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq]

/-- The right-complement candidate is supported on `I - Π`. -/
theorem projectedUnitaryBlockRightPerpCandidate_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec (OrthogonalProjector.complement right)
        (projectedUnitaryBlockRightPerpCandidate left right U i hlambda) =
      projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
  unfold projectedUnitaryBlockRightPerpCandidate
  rw [HilbertOperator.applyVec_smul]
  congr 1
  rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq]

/-- Under the genuine two-dimensional-sector hypothesis, the left-complement
candidate is a unit vector. -/
theorem projectedUnitaryBlockLeftPerpCandidate_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    ‖projectedUnitaryBlockLeftPerpCandidate left right U i hlambda‖ = 1 := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hprojected :
      HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (pair.σ : ℂ) • pair.leftVec := by
    have hA := pair.A_right
    change HilbertOperator.applyVec
        (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
      (pair.σ : ℂ) • pair.leftVec at hA
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
      pair.right_support] at hA
    exact hA
  have hprojected_norm :
      ‖HilbertOperator.applyVec left.op (U.applyVec pair.rightVec)‖ = pair.σ := by
    rw [hprojected, norm_smul, pair.leftVec.norm_eq_one, mul_one,
      Complex.norm_of_nonneg (le_of_lt pair.sigma_pos)]
  have hcomplement_norm :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement left)
          (U.applyVec pair.rightVec)‖ = Real.sqrt (1 - pair.σ ^ 2) := by
    simpa using orthogonalProjector_complement_norm_eq_sqrt left
      (U.apply pair.rightVec) pair.σ hprojected_norm
  have hsqrt_ne : Real.sqrt (1 - pair.σ ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [pair.sigma_pos, hsigma_lt_one])
  change
    ‖((Real.sqrt (1 - pair.σ ^ 2) : ℂ)⁻¹ •
      HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (U.applyVec pair.rightVec))‖ = 1
  rw [norm_smul, hcomplement_norm, norm_inv,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), inv_mul_cancel₀ hsqrt_ne]

/-- Under the genuine two-dimensional-sector hypothesis, the right-complement
candidate is a unit vector. -/
theorem projectedUnitaryBlockRightPerpCandidate_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    ‖projectedUnitaryBlockRightPerpCandidate left right U i hlambda‖ = 1 := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hprojected :
      HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
        (pair.σ : ℂ) • pair.rightVec := by
    have hA := pair.Astar_left
    change HilbertOperator.applyVec
        (Matrix.conjTranspose
          (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
      (pair.σ : ℂ) • pair.rightVec at hA
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
      HilbertOperator.mul_applyVec, pair.left_support] at hA
    exact hA
  have hprojected_norm :
      ‖HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec)‖ = pair.σ := by
    rw [hprojected, norm_smul, pair.rightVec.norm_eq_one, mul_one,
      Complex.norm_of_nonneg (le_of_lt pair.sigma_pos)]
  have hcomplement_norm :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement right)
          (U.dagger.applyVec pair.leftVec)‖ = Real.sqrt (1 - pair.σ ^ 2) := by
    simpa using orthogonalProjector_complement_norm_eq_sqrt right
      (U.dagger.apply pair.leftVec) pair.σ hprojected_norm
  have hsqrt_ne : Real.sqrt (1 - pair.σ ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [pair.sigma_pos, hsigma_lt_one])
  change
    ‖((Real.sqrt (1 - pair.σ ^ 2) : ℂ)⁻¹ •
      HilbertOperator.applyVec (OrthogonalProjector.complement right)
        (U.dagger.applyVec pair.leftVec))‖ = 1
  rw [norm_smul, hcomplement_norm, norm_inv,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), inv_mul_cancel₀ hsqrt_ne]

/-- Certified left-complement vector for a genuine two-dimensional singular
sector. -/
noncomputable def projectedUnitaryBlockLeftPerp {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    NormalizedVector (Qubits N) :=
  NormalizedVector.ofVector
    (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda)
    (projectedUnitaryBlockLeftPerpCandidate_norm_eq_one
      left right U i hlambda hsigma_lt_one)

/-- Certified right-complement vector for a genuine two-dimensional singular
sector. -/
noncomputable def projectedUnitaryBlockRightPerp {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    NormalizedVector (Qubits N) :=
  NormalizedVector.ofVector
    (projectedUnitaryBlockRightPerpCandidate left right U i hlambda)
    (projectedUnitaryBlockRightPerpCandidate_norm_eq_one
      left right U i hlambda hsigma_lt_one)

/-- In the `0 < σ < 1` sector, `U |v⟩` splits into its projected singular
component and normalized left-complement component [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_U_rightVec_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    U.applyVec (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec =
      ((projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ : ℂ) •
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec +
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).σ ^ 2) :
          ℝ) : ℂ) •
        projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hproj :
      HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (pair.σ : ℂ) • pair.leftVec := by
    have hA := pair.A_right
    change HilbertOperator.applyVec
        (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
      (pair.σ : ℂ) • pair.leftVec at hA
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
      pair.right_support] at hA
    change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
      (pair.σ : ℂ) • pair.leftVec at hA
    change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
      (pair.σ : ℂ) • pair.leftVec
    exact hA
  have hgamma_ne :
      ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < 1 - pair.σ ^ 2 := by
      nlinarith [pair.sigma_pos, hsigma_lt_one]
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hcomp :
      HilbertOperator.applyVec (OrthogonalProjector.complement left) (U.applyVec pair.rightVec) =
        ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) •
          projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
    let γ : ℂ := ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)
    have hgamma_ne' : γ ≠ 0 := hgamma_ne
    unfold projectedUnitaryBlockLeftPerpCandidate
    dsimp [pair]
    change
      HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (U.applyVec pair.rightVec) =
      γ • (γ⁻¹ •
        HilbertOperator.applyVec (OrthogonalProjector.complement left) (U.applyVec pair.rightVec))
    rw [smul_smul, mul_inv_cancel₀ hgamma_ne']
    simp
  have hsum : left.op + OrthogonalProjector.complement left =
      (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  calc
    U.applyVec pair.rightVec =
        HilbertOperator.applyVec (1 : HilbertOperator (Qubits N)) (U.applyVec pair.rightVec) := by
      rw [HilbertOperator.one_applyVec]
    _ = HilbertOperator.applyVec (left.op + OrthogonalProjector.complement left)
          (U.applyVec pair.rightVec) := by
      rw [hsum]
    _ = HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) +
          HilbertOperator.applyVec (OrthogonalProjector.complement left)
            (U.applyVec pair.rightVec) := by
      rw [HilbertOperator.add_applyVec]
    _ = (pair.σ : ℂ) • pair.leftVec +
          ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) •
            projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
      rw [hproj, hcomp]

/-- In the `0 < σ < 1` sector, `U† |w⟩` splits into its projected singular
component and normalized right-complement component [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_Udag_leftVec_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    U.dagger.applyVec
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec =
      ((projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ : ℂ) •
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec +
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).σ ^ 2) :
          ℝ) : ℂ) •
        projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hproj :
      HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
        (pair.σ : ℂ) • pair.rightVec := by
    have hA := pair.Astar_left
    change HilbertOperator.applyVec
        (Matrix.conjTranspose
          (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
      (pair.σ : ℂ) • pair.rightVec at hA
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
      HilbertOperator.mul_applyVec, pair.left_support] at hA
    change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
      (pair.σ : ℂ) • pair.rightVec at hA
    change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
      (pair.σ : ℂ) • pair.rightVec
    exact hA
  have hgamma_ne :
      ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < 1 - pair.σ ^ 2 := by
      nlinarith [pair.sigma_pos, hsigma_lt_one]
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hcomp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right)
          (U.dagger.applyVec pair.leftVec) =
        ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) •
          projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
    let γ : ℂ := ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)
    have hgamma_ne' : γ ≠ 0 := hgamma_ne
    unfold projectedUnitaryBlockRightPerpCandidate
    dsimp [pair]
    change HilbertOperator.applyVec (OrthogonalProjector.complement right)
        (U.dagger.applyVec pair.leftVec) =
      γ • (γ⁻¹ •
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
          (U.dagger.applyVec pair.leftVec))
    rw [smul_smul, mul_inv_cancel₀ hgamma_ne']
    simp
  have hsum : right.op + OrthogonalProjector.complement right =
      (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  calc
    U.dagger.applyVec pair.leftVec =
        HilbertOperator.applyVec (1 : HilbertOperator (Qubits N))
          (U.dagger.applyVec pair.leftVec) := by
      rw [HilbertOperator.one_applyVec]
    _ = HilbertOperator.applyVec (right.op + OrthogonalProjector.complement right)
          (U.dagger.applyVec pair.leftVec) := by
      rw [hsum]
    _ = HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) +
          HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (U.dagger.applyVec pair.leftVec) := by
      rw [HilbertOperator.add_applyVec]
    _ = (pair.σ : ℂ) • pair.rightVec +
          ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ) •
            projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
      rw [hproj, hcomp]

/-- In the `0 < σ < 1` sector, `U` maps the right-complement vector to the
second row of the source two-by-two singular block [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_U_rightPerp_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    U.applyVec (projectedUnitaryBlockRightPerpCandidate left right U i hlambda) =
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).σ ^ 2) :
          ℝ) : ℂ) •
          (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec +
        (-(projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ : ℂ) •
          projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  let γ : ℂ := ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)
  have hgamma_pos : 0 < 1 - pair.σ ^ 2 := by
    nlinarith [pair.sigma_pos, hsigma_lt_one]
  have hgamma_ne : γ ≠ 0 := by
    dsimp [γ]
    exact_mod_cast (Real.sqrt_pos.2 hgamma_pos).ne'
  have hgamma_sq : γ * γ = 1 - (pair.σ : ℂ) ^ 2 := by
    dsimp [γ]
    have hsqrt_sq :
        Real.sqrt (1 - pair.σ ^ 2) * Real.sqrt (1 - pair.σ ^ 2) =
          1 - pair.σ ^ 2 := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hgamma_pos)]
    rw [← Complex.ofReal_mul, hsqrt_sq]
    norm_num [pow_two]
  have hproj :
      HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
        (pair.σ : ℂ) • pair.rightVec := by
    have hA := pair.Astar_left
    change HilbertOperator.applyVec
        (Matrix.conjTranspose
          (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
      (pair.σ : ℂ) • pair.rightVec at hA
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
      HilbertOperator.mul_applyVec, pair.left_support] at hA
    change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
      (pair.σ : ℂ) • pair.rightVec at hA
    change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
      (pair.σ : ℂ) • pair.rightVec
    exact hA
  have hrightPerp :
      projectedUnitaryBlockRightPerpCandidate left right U i hlambda =
        γ⁻¹ •
          (U.dagger.applyVec pair.leftVec -
            (pair.σ : ℂ) • pair.rightVec) := by
    unfold projectedUnitaryBlockRightPerpCandidate
    dsimp [pair, γ]
    rw [orthogonalProjector_complement_applyVec, hproj]
    rfl
  have hUright :=
    projectedUnitaryBlock_U_rightVec_decomposition left right U i hlambda hsigma_lt_one
  have hUinv := gate_applyVec_conjTranspose_applyVec U pair.leftVec
  have hUinv_gate : U.applyVec (U.dagger.applyVec pair.leftVec) = pair.leftVec := by
    exact hUinv
  have hscale_left : γ⁻¹ * (1 - (pair.σ : ℂ) ^ 2) = γ := by
    rw [← hgamma_sq]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hscale_perp : γ⁻¹ * ((pair.σ : ℂ) * γ) = (pair.σ : ℂ) := by
    rw [mul_comm (pair.σ : ℂ) γ]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hcoeff_left :
      γ⁻¹ + -(γ⁻¹ * ((pair.σ : ℂ) * (pair.σ : ℂ))) = γ := by
    have h := hscale_left
    rw [sub_eq_add_neg, mul_add, mul_one, mul_neg, pow_two] at h
    simpa [mul_assoc] using h
  have hcoeff_perp :
      -(γ⁻¹ * ((pair.σ : ℂ) * γ)) = -(pair.σ : ℂ) := by
    rw [hscale_perp]
  calc
    U.applyVec (projectedUnitaryBlockRightPerpCandidate left right U i hlambda) =
        U.applyVec (γ⁻¹ •
          (U.dagger.applyVec pair.leftVec -
            (pair.σ : ℂ) • pair.rightVec)) := by
      rw [hrightPerp]
    _ = γ⁻¹ •
          (U.applyVec (U.dagger.applyVec pair.leftVec) -
            (pair.σ : ℂ) • U.applyVec pair.rightVec) := by
      rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_sub,
        UnitaryOperator.applyVec_smul]
    _ = γ⁻¹ •
          (pair.leftVec -
            (pair.σ : ℂ) •
              (((pair.σ : ℂ) • pair.leftVec) +
                γ • projectedUnitaryBlockLeftPerpCandidate left right U i hlambda)) := by
      rw [hUinv_gate, hUright]
    _ = γ • pair.leftVec +
          (-(pair.σ : ℂ)) •
            projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
      calc
        γ⁻¹ •
            (pair.leftVec -
              (pair.σ : ℂ) •
                (((pair.σ : ℂ) • pair.leftVec) +
                  γ • projectedUnitaryBlockLeftPerpCandidate left right U i hlambda)) =
            (γ⁻¹ + -(γ⁻¹ * ((pair.σ : ℂ) * (pair.σ : ℂ)))) •
                pair.leftVec +
              (-(γ⁻¹ * ((pair.σ : ℂ) * γ))) •
                projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
          module
        _ = γ • pair.leftVec +
              (-(pair.σ : ℂ)) •
                projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
          rw [hcoeff_left, hcoeff_perp]

/-- In the `0 < σ < 1` sector, `U†` maps the left-complement vector to the
second column of the source two-by-two singular block [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_Udag_leftPerp_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    U.dagger.applyVec (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda) =
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).σ ^ 2) :
          ℝ) : ℂ) •
          (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec +
        (-(projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ : ℂ) •
          projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  let γ : ℂ := ((Real.sqrt (1 - pair.σ ^ 2) : ℝ) : ℂ)
  have hgamma_pos : 0 < 1 - pair.σ ^ 2 := by
    nlinarith [pair.sigma_pos, hsigma_lt_one]
  have hgamma_ne : γ ≠ 0 := by
    dsimp [γ]
    exact_mod_cast (Real.sqrt_pos.2 hgamma_pos).ne'
  have hgamma_sq : γ * γ = 1 - (pair.σ : ℂ) ^ 2 := by
    dsimp [γ]
    have hsqrt_sq :
        Real.sqrt (1 - pair.σ ^ 2) * Real.sqrt (1 - pair.σ ^ 2) =
          1 - pair.σ ^ 2 := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hgamma_pos)]
    rw [← Complex.ofReal_mul, hsqrt_sq]
    norm_num [pow_two]
  have hproj :
      HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (pair.σ : ℂ) • pair.leftVec := by
    have hA := pair.A_right
    change HilbertOperator.applyVec
        (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
      (pair.σ : ℂ) • pair.leftVec at hA
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
      pair.right_support] at hA
    change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
      (pair.σ : ℂ) • pair.leftVec at hA
    change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
      (pair.σ : ℂ) • pair.leftVec
    exact hA
  have hleftPerp :
      projectedUnitaryBlockLeftPerpCandidate left right U i hlambda =
        γ⁻¹ •
          (U.applyVec pair.rightVec -
            (pair.σ : ℂ) • pair.leftVec) := by
    unfold projectedUnitaryBlockLeftPerpCandidate
    dsimp [pair, γ]
    rw [orthogonalProjector_complement_applyVec, hproj]
    rfl
  have hUdagLeft :=
    projectedUnitaryBlock_Udag_leftVec_decomposition left right U i hlambda hsigma_lt_one
  have hUinv := gate_conjTranspose_applyVec_applyVec U pair.rightVec
  have hUinv_gate : U.dagger.applyVec (U.applyVec pair.rightVec) = pair.rightVec := by
    exact hUinv
  have hscale_left : γ⁻¹ * (1 - (pair.σ : ℂ) ^ 2) = γ := by
    rw [← hgamma_sq]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hscale_perp : γ⁻¹ * ((pair.σ : ℂ) * γ) = (pair.σ : ℂ) := by
    rw [mul_comm (pair.σ : ℂ) γ]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hcoeff_left :
      γ⁻¹ + -(γ⁻¹ * ((pair.σ : ℂ) * (pair.σ : ℂ))) = γ := by
    have h := hscale_left
    rw [sub_eq_add_neg, mul_add, mul_one, mul_neg, pow_two] at h
    simpa [mul_assoc] using h
  have hcoeff_perp :
      -(γ⁻¹ * ((pair.σ : ℂ) * γ)) = -(pair.σ : ℂ) := by
    rw [hscale_perp]
  calc
    U.dagger.applyVec
        (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda) =
        U.dagger.applyVec (γ⁻¹ •
          (U.applyVec pair.rightVec -
            (pair.σ : ℂ) • pair.leftVec)) := by
      rw [hleftPerp]
    _ = γ⁻¹ •
          (U.dagger.applyVec (U.applyVec pair.rightVec) -
            (pair.σ : ℂ) • U.dagger.applyVec pair.leftVec) := by
      rw [UnitaryOperator.applyVec_smul, UnitaryOperator.applyVec_sub,
        UnitaryOperator.applyVec_smul]
    _ = γ⁻¹ •
          (pair.rightVec -
            (pair.σ : ℂ) •
              (((pair.σ : ℂ) • pair.rightVec) +
                γ • projectedUnitaryBlockRightPerpCandidate left right U i hlambda)) := by
      rw [hUinv_gate, hUdagLeft]
    _ = γ • pair.rightVec +
          (-(pair.σ : ℂ)) •
            projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
      calc
        γ⁻¹ •
            (pair.rightVec -
              (pair.σ : ℂ) •
                (((pair.σ : ℂ) • pair.rightVec) +
                  γ • projectedUnitaryBlockRightPerpCandidate left right U i hlambda)) =
            (γ⁻¹ + -(γ⁻¹ * ((pair.σ : ℂ) * (pair.σ : ℂ)))) •
                pair.rightVec +
              (-(γ⁻¹ * ((pair.σ : ℂ) * γ))) •
                projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
          module
        _ = γ • pair.rightVec +
              (-(pair.σ : ℂ)) •
                projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
          rw [hcoeff_left, hcoeff_perp]

/-- Source-facing certificate for one two-dimensional singular-value block in
`lemma:singInvDec`.  For a singular value `0 < sigma < 1`, Gilyén et al. build
right/left singular vectors together with their orthogonal complements so that
`U` acts by the displayed two-by-two block [GSLW19, BlockHam.tex:583-613,
655-735].  This structure records the local block data used before assembling
the global direct-sum decomposition. -/
structure SourceTwoDimensionalSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Singular value for the `0 < sigma < 1` two-dimensional source sector. -/
  σ : ℝ
  sigma_pos : 0 < σ
  sigma_lt_one : σ < 1
  /-- Right singular vector supported by the input projector. -/
  rightVec : NormalizedVector (Qubits N)
  /-- Left singular vector supported by the output projector. -/
  leftVec : NormalizedVector (Qubits N)
  /-- Right-complement vector paired with `leftVec` by `U†`. -/
  rightPerp : NormalizedVector (Qubits N)
  /-- Left-complement vector paired with `rightVec` by `U`. -/
  leftPerp : NormalizedVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  right_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp = rightPerp
  left_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement left) leftPerp = leftPerp
  U_right :
    U.applyVec rightVec =
      (σ : ℂ) • leftVec + ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • leftPerp
  U_rightPerp :
    U.applyVec rightPerp =
      ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • leftVec + (-(σ : ℂ)) • leftPerp
  Udag_left :
    U.dagger.applyVec leftVec =
      (σ : ℂ) • rightVec + ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • rightPerp
  Udag_leftPerp :
    U.dagger.applyVec leftPerp =
      ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • rightVec + (-(σ : ℂ)) • rightPerp

namespace SourceTwoDimensionalSingularBlock

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec =
      (block.σ : Complex) • block.leftVec := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) =
    (block.σ : Complex) • block.leftVec
  rw [block.U_right]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

theorem projectedUnitaryBlock_conjTranspose_applyVec_leftVec {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        block.leftVec =
      (block.σ : Complex) • block.rightVec := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.left_support]
  change HilbertOperator.applyVec right.op (U.dagger.applyVec block.leftVec) =
    (block.σ : Complex) • block.rightVec
  rw [block.Udag_left]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- On a nontrivial source two-dimensional singular block, the Gram operator has
eigenvalue `σ^2` on the right singular vector [GSLW19, BlockHam.tex:655-735,
747-764]. -/
theorem gram_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        block.rightVec =
      ((block.σ : Complex) ^ 2) • block.rightVec := by
  rw [HilbertOperator.mul_applyVec, block.projectedUnitaryBlock_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_conjTranspose_applyVec_leftVec,
    smul_smul]
  ring_nf

theorem evenSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (evenSingularValuePolynomial right P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.σ : Complex) • block.rightVec := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      ((block.σ : Complex) ^ 2) block.rightVec
      block.gram_applyVec_rightVec,
    evenSquareQuotient_eval_sq_of_hasParity hL hP,
    HilbertOperator.applyVec_smul, block.right_support]

theorem oddSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (oddSingularValuePolynomial P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.σ : Complex) • block.leftVec := by
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      ((block.σ : Complex) ^ 2) block.rightVec
      block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_applyVec_rightVec, smul_smul]
  have hodd := oddSquareQuotient_eval_sq_of_hasParity hL hP (block.σ : Complex)
  rw [← hodd]
  ring_nf

theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.σ : Complex) • block.rightVec := by
  unfold singularValuePolynomial
  simp [hL, evenSingularValuePolynomial_applyVec_rightVec block P hL hP]

theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.σ : Complex) • block.leftVec := by
  unfold singularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  simp [hnot, oddSingularValuePolynomial_applyVec_rightVec block P hL hP]

theorem sigma_mem_unitInterval {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    block.σ ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_trans (by norm_num) (le_of_lt block.sigma_pos), le_of_lt block.sigma_lt_one⟩

theorem right_phase_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
      Complex.exp (φ * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ right block.right_support

theorem right_phase_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightPerp =
      Complex.exp (-(φ * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ right block.right_perp_support

theorem left_phase_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftVec =
      Complex.exp (φ * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ left block.left_support

theorem left_phase_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftPerp =
      Complex.exp (-(φ * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ left block.left_perp_support

theorem odd_signal_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec =
      (block.σ : ℂ) • block.leftVec +
        ((Real.sqrt (1 - block.σ ^ 2) : ℝ) : ℂ) • block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem odd_signal_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp =
      ((Real.sqrt (1 - block.σ ^ 2) : ℝ) : ℂ) • block.leftVec +
        (-(block.σ : ℂ)) • block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  simpa [neg_smul] using block.U_rightPerp

theorem even_signal_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftVec =
      (block.σ : ℂ) • block.rightVec +
        ((Real.sqrt (1 - block.σ ^ 2) : ℝ) : ℂ) • block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_left

theorem even_signal_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftPerp =
      ((Real.sqrt (1 - block.σ ^ 2) : ℝ) : ℂ) • block.rightVec +
        (-(block.σ : ℂ)) • block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  simpa [neg_smul] using block.Udag_leftPerp

end SourceTwoDimensionalSingularBlock

/-- A nonzero projected-block singular pair with `0 < σ < 1` gives the
two-dimensional invariant sector of `lemma:singInvDec` [GSLW19,
BlockHam.tex:583-613,655-735]. -/
noncomputable def projectedUnitaryBlockTwoDimensionalSingularBlock {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1) :
    SourceTwoDimensionalSingularBlock U left right := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  refine
    { σ := pair.σ
      sigma_pos := pair.sigma_pos
      sigma_lt_one := hsigma_lt_one
      rightVec := pair.rightVec
      leftVec := pair.leftVec
      rightPerp := projectedUnitaryBlockRightPerp
        left right U i hlambda hsigma_lt_one
      leftPerp := projectedUnitaryBlockLeftPerp
        left right U i hlambda hsigma_lt_one
      right_support := pair.right_support
      left_support := pair.left_support
      right_perp_support :=
        projectedUnitaryBlockRightPerpCandidate_support left right U i hlambda
      left_perp_support :=
        projectedUnitaryBlockLeftPerpCandidate_support left right U i hlambda
      U_right :=
        projectedUnitaryBlock_U_rightVec_decomposition left right U i hlambda hsigma_lt_one
      U_rightPerp :=
        projectedUnitaryBlock_U_rightPerp_decomposition left right U i hlambda hsigma_lt_one
      Udag_left :=
        projectedUnitaryBlock_Udag_leftVec_decomposition left right U i hlambda hsigma_lt_one
      Udag_leftPerp :=
        projectedUnitaryBlock_Udag_leftPerp_decomposition left right U i hlambda hsigma_lt_one }

/-- Source-facing certificate for the one-dimensional singular-value-one blocks
in `lemma:singInvDec`.  These are the blocks where `U` maps a right singular
vector in `img Π` directly to the matching left singular vector in
`img \widetildeΠ` [GSLW19, BlockHam.tex:583-613,655-671,718-735]. -/
structure SourceUnitSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right singular vector in the unit singular-value sector. -/
  rightVec : NormalizedVector (Qubits N)
  /-- Left singular vector paired with `rightVec` by `U`. -/
  leftVec : NormalizedVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  U_right : U.applyVec rightVec = leftVec
  Udag_left : U.dagger.applyVec leftVec = rightVec

namespace SourceUnitSingularBlock

theorem right_phase_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
      Complex.exp (φ * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ right block.right_support

theorem left_phase_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftVec =
      Complex.exp (φ * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ left block.left_support

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec =
      block.leftVec := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) = block.leftVec
  rw [block.U_right, block.left_support]

theorem projectedUnitaryBlock_conjTranspose_applyVec_leftVec {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        block.leftVec =
      block.rightVec := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.left_support]
  change HilbertOperator.applyVec right.op (U.dagger.applyVec block.leftVec) =
    block.rightVec
  rw [block.Udag_left, block.right_support]

theorem gram_applyVec_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        block.rightVec =
      (1 : Complex) • block.rightVec := by
  rw [HilbertOperator.mul_applyVec, block.projectedUnitaryBlock_applyVec_rightVec,
    block.projectedUnitaryBlock_conjTranspose_applyVec_leftVec]
  simp

theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (1 : Complex) • block.rightVec := by
  unfold singularValuePolynomial evenSingularValuePolynomial
  rw [if_pos hL]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (1 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.right_support]
  have heven := evenSquareQuotient_eval_sq_of_hasParity hL hP (1 : Complex)
  have heven1 :
      (evenSquareQuotient P).eval (1 : Complex) = P.eval (1 : Complex) := by
    simpa using heven
  rw [heven1]

theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (1 : Complex) • block.leftVec := by
  unfold singularValuePolynomial oddSingularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  rw [if_neg hnot]
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (1 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_applyVec_rightVec]
  have hodd := oddSquareQuotient_eval_sq_of_hasParity hL hP (1 : Complex)
  rw [← hodd]
  ring_nf

theorem odd_signal_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec = block.leftVec := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem even_signal_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftVec = block.rightVec := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_left

end SourceUnitSingularBlock

/-- A nonzero projected-block singular pair with `σ = 1` gives the
one-dimensional invariant sector of `lemma:singInvDec`.  The proof uses
projector norm saturation to upgrade the projected equations
`Π̃ U Π v = w` and `Π U† Π̃ w = v` to the unprojected equations
`U v = w` and `U† w = v` [GSLW19, BlockHam.tex:583-613,655-671]. -/
noncomputable def projectedUnitaryBlockUnitSingularBlock {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ = 1) :
    SourceUnitSingularBlock U left right := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  refine
    { rightVec := pair.rightVec
      leftVec := pair.leftVec
      right_support := pair.right_support
      left_support := pair.left_support
      U_right := ?_
      Udag_left := ?_ }
  · have hproj :
        HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) = pair.leftVec := by
      have hA := pair.A_right
      change HilbertOperator.applyVec
          (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
        (pair.σ : ℂ) • pair.leftVec at hA
      rw [HilbertOperator.mul_applyVec,
        HilbertOperator.mul_applyVec, pair.right_support, hsigma] at hA
      change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (1 : ℂ) • pair.leftVec at hA
      change HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        pair.leftVec
      simpa only [one_smul] using hA
    have hproj_norm :
        ‖HilbertOperator.applyVec left.op (U.applyVec pair.rightVec)‖ = 1 := by
      rw [hproj, pair.leftVec.norm_eq_one]
    have hsupport :=
      orthogonalProjector_applyVec_eq_self_of_norm_eq_one left
        (U.apply pair.rightVec) hproj_norm
    exact hsupport.symm.trans hproj
  · have hproj :
        HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
          pair.rightVec := by
      have hA := pair.Astar_left
      change HilbertOperator.applyVec
          (Matrix.conjTranspose
            (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
        (pair.σ : ℂ) • pair.rightVec at hA
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
        HilbertOperator.mul_applyVec, pair.left_support, hsigma] at hA
      change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
        (1 : ℂ) • pair.rightVec at hA
      change HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec) =
        pair.rightVec
      simpa only [one_smul] using hA
    have hproj_norm :
        ‖HilbertOperator.applyVec right.op (U.dagger.applyVec pair.leftVec)‖ = 1 := by
      rw [hproj, pair.rightVec.norm_eq_one]
    have hsupport :=
      orthogonalProjector_applyVec_eq_self_of_norm_eq_one right
        (U.dagger.apply pair.leftVec) hproj_norm
    exact hsupport.symm.trans hproj

/-- Source-facing classification for nonzero singular sectors in
`lemma:singInvDec`: a sector is either `σ=1` and one-dimensional, or
`0<σ<1` and two-dimensional [GSLW19, BlockHam.tex:583-613,655-735]. -/
inductive SourceNonzeroClassifiedSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) : Type where
  | unitBlock : SourceUnitSingularBlock U left right ->
      SourceNonzeroClassifiedSingularBlock U left right
  | twoDimensionalBlock : SourceTwoDimensionalSingularBlock U left right ->
      SourceNonzeroClassifiedSingularBlock U left right

/-- Classify a nonzero projected singular pair into the source's `σ=1` or
`0<σ<1` invariant sector [GSLW19, BlockHam.tex:583-613,655-735]. -/
noncomputable def projectedUnitaryBlockNonzeroClassifiedSingularBlock {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceNonzeroClassifiedSingularBlock U left right := by
  classical
  by_cases hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ = 1
  · exact SourceNonzeroClassifiedSingularBlock.unitBlock
      (projectedUnitaryBlockUnitSingularBlock left right U i hlambda hsigma)
  · have hlt :
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1 := by
      rcases SourceNonzeroSingularPair.sigma_eq_one_or_lt_one
          (left := left) (right := right) (U := U) (i := i) hlambda with heq | hlt
      · exact False.elim (hsigma heq)
      · exact hlt
    exact SourceNonzeroClassifiedSingularBlock.twoDimensionalBlock
      (projectedUnitaryBlockTwoDimensionalSingularBlock left right U i hlambda hlt)

/-- Source-facing certificate for a right-kernel block in `lemma:singInvDec`.
Here the right singular vector lies in `img Π`, its encoded matrix image is
zero, and `U` sends it into the left complement [GSLW19,
BlockHam.tex:599-611,655-716]. -/
structure SourceRightKernelSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-supported vector in the zero singular-value sector. -/
  rightVec : NormalizedVector (Qubits N)
  /-- Left-complement image of the right-kernel vector under `U`. -/
  leftPerp : NormalizedVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement left) leftPerp = leftPerp
  U_right : U.applyVec rightVec = leftPerp
  Udag_leftPerp : U.dagger.applyVec leftPerp = rightVec

namespace SourceRightKernelSingularBlock

theorem right_phase_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightVec =
      Complex.exp (φ * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ right block.right_support

theorem left_phase_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftPerp =
      Complex.exp (-(φ * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ left block.left_perp_support

theorem odd_signal_on_rightVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec = block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem even_signal_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftPerp = block.rightVec := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_leftPerp

end SourceRightKernelSingularBlock

/-- Source-facing certificate for a left-kernel block in `lemma:singInvDec`.
This is the left-hand zero singular-value sector: a left singular vector in
`img \widetildeΠ` is paired with a right-complement vector by `U` and `U†`
[GSLW19, BlockHam.tex:599-611,655-716]. -/
structure SourceLeftKernelSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-complement preimage of the left-kernel vector under `U`. -/
  rightPerp : NormalizedVector (Qubits N)
  /-- Left-supported vector in the zero singular-value sector. -/
  leftVec : NormalizedVector (Qubits N)
  right_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp = rightPerp
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  U_rightPerp : U.applyVec rightPerp = leftVec
  Udag_left : U.dagger.applyVec leftVec = rightPerp

namespace SourceLeftKernelSingularBlock

theorem right_phase_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightPerp =
      Complex.exp (-(φ * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ right block.right_perp_support

theorem left_phase_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftVec =
      Complex.exp (φ * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self φ left block.left_support

theorem odd_signal_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp = block.leftVec := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_rightPerp

theorem even_signal_on_leftVec {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftVec = block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_left

end SourceLeftKernelSingularBlock

/-- Construct the right-kernel sector of `lemma:singInvDec` from a right-supported
vector whose projected-unitary image is zero.  The unprojected image is therefore
supported in the left complement, and unitarity gives the paired adjoint action
[GSLW19, BlockHam.tex:599-611,655-716]. -/
noncomputable def sourceRightKernelSingularBlockOfProjectedBlockEqZero {N : Nat}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (rightVec : NormalizedVector (Qubits N))
    (hright : HilbertOperator.applyVec right.op rightVec = rightVec)
    (hzero : HilbertOperator.applyVec (projectedUnitaryBlock left right U) rightVec = 0) :
    SourceRightKernelSingularBlock U left right :=
  { rightVec := rightVec,
    leftPerp := U.apply rightVec,
    right_support := hright,
    left_perp_support := by
      change HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (U.applyVec rightVec) = U.applyVec rightVec
      have hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightVec) = 0 := by
        have h := hzero
        unfold projectedUnitaryBlock at h
        rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, hright] at h
        change HilbertOperator.applyVec left.op (U.applyVec rightVec) = 0 at h
        change HilbertOperator.applyVec left.op (U.applyVec rightVec) = 0
        exact h
      rw [orthogonalProjector_complement_applyVec, hleft_zero, sub_zero],
    U_right := rfl,
    Udag_leftPerp := by
      exact gate_conjTranspose_applyVec_applyVec U rightVec }

/-- Construct the left-kernel sector of `lemma:singInvDec` from a left-supported
vector whose adjoint projected-unitary image is zero.  This is the left-handed
zero-singular-value companion of
`sourceRightKernelSingularBlockOfProjectedBlockEqZero`
[GSLW19, BlockHam.tex:599-611,655-716]. -/
noncomputable def sourceLeftKernelSingularBlockOfProjectedBlockConjTransposeEqZero
    {N : Nat} (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (leftVec : NormalizedVector (Qubits N))
    (hleft : HilbertOperator.applyVec left.op leftVec = leftVec)
    (hzero :
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        leftVec = 0) :
    SourceLeftKernelSingularBlock U left right :=
  { rightPerp := U.dagger.apply leftVec,
    leftVec := leftVec,
    right_perp_support := by
      change HilbertOperator.applyVec (OrthogonalProjector.complement right)
        (U.dagger.applyVec leftVec) = U.dagger.applyVec leftVec
      have hright_zero :
          HilbertOperator.applyVec right.op (U.dagger.applyVec leftVec) = 0 := by
        have h := hzero
        unfold projectedUnitaryBlock at h
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          left.selfAdjoint, right.selfAdjoint,
          HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, hleft] at h
        change HilbertOperator.applyVec right.op (U.dagger.applyVec leftVec) = 0 at h
        change HilbertOperator.applyVec right.op (U.dagger.applyVec leftVec) = 0
        exact h
      rw [orthogonalProjector_complement_applyVec, hright_zero, sub_zero],
    left_support := hleft,
    U_rightPerp := by
      exact gate_applyVec_conjTranspose_applyVec U leftVec,
    Udag_left := rfl }

/-- Source-facing certificate for the fully complementary sector in
`lemma:singInvDec`: `U` maps the right complement of the singular-vector
decomposition to the corresponding left complement [GSLW19,
BlockHam.tex:607-613,718-735]. -/
structure SourceComplementSingularBlock {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-complement vector in the fully complementary sector. -/
  rightPerp : NormalizedVector (Qubits N)
  /-- Left-complement vector paired with `rightPerp` by `U`. -/
  leftPerp : NormalizedVector (Qubits N)
  right_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp = rightPerp
  left_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement left) leftPerp = leftPerp
  U_rightPerp : U.applyVec rightPerp = leftPerp
  Udag_leftPerp : U.dagger.applyVec leftPerp = rightPerp

namespace SourceComplementSingularBlock

theorem right_phase_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ right) block.rightPerp =
      Complex.exp (-(φ * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ right block.right_perp_support

theorem left_phase_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) (φ : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp φ left) block.leftPerp =
      Complex.exp (-(φ * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self φ left block.left_perp_support

theorem odd_signal_on_rightPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp = block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_rightPerp

theorem even_signal_on_leftPerp {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftPerp = block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_leftPerp

end SourceComplementSingularBlock

/-- Package a fully complementary sector of `lemma:singInvDec`: if a vector is
already in the right complement and its image under `U` has no left-projector
component, then `U` and `U†` pair it with a left-complement vector
[GSLW19, BlockHam.tex:607-613,718-735]. -/
noncomputable def sourceComplementSingularBlockOfRightComplementProjectedZero
    {N : Nat} (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (rightPerp : NormalizedVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceComplementSingularBlock U left right :=
  { rightPerp := rightPerp,
    leftPerp := U.apply rightPerp,
    right_perp_support := hright_perp,
    left_perp_support := by
      change HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (U.applyVec rightPerp) = U.applyVec rightPerp
      rw [orthogonalProjector_complement_applyVec, hleft_zero, sub_zero],
    U_rightPerp := rfl,
    Udag_leftPerp := by
      exact gate_conjTranspose_applyVec_applyVec U rightPerp }

/-- Source-facing direct-sum skeleton for `lemma:singInvDec`.  The source
decomposes the space into singular-value-one, two-dimensional `0 < sigma < 1`,
right-kernel, left-kernel, and fully complementary sectors; each sector is
recorded above with the local `U`, `U†`, and projector-phase actions needed for
`thm:singValTransformation` [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantDecomposition {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Number of unit singular-value source sectors. -/
  unitBlockCount : Nat
  /-- Number of two-dimensional `0 < sigma < 1` source sectors. -/
  twoDimensionalBlockCount : Nat
  /-- Number of right-kernel source sectors. -/
  rightKernelBlockCount : Nat
  /-- Number of left-kernel source sectors. -/
  leftKernelBlockCount : Nat
  /-- Number of fully complementary source sectors. -/
  complementBlockCount : Nat
  /-- Unit singular-value block indexed by the source decomposition. -/
  unitBlock :
    Fin unitBlockCount -> SourceUnitSingularBlock U left right
  /-- Two-dimensional singular block indexed by the source decomposition. -/
  twoDimensionalBlock :
    Fin twoDimensionalBlockCount -> SourceTwoDimensionalSingularBlock U left right
  /-- Right-kernel singular block indexed by the source decomposition. -/
  rightKernelBlock :
    Fin rightKernelBlockCount -> SourceRightKernelSingularBlock U left right
  /-- Left-kernel singular block indexed by the source decomposition. -/
  leftKernelBlock :
    Fin leftKernelBlockCount -> SourceLeftKernelSingularBlock U left right
  /-- Fully complementary block indexed by the source decomposition. -/
  complementBlock :
    Fin complementBlockCount -> SourceComplementSingularBlock U left right

end QuantumAlg.QSP.MultiQubit.QSVT
end

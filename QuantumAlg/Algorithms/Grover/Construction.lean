/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.WalshHadamard.Mathematics
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import all QuantumAlg.Components.Oracle.Phase.Operator
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.AmplitudeAmplification.Construction
import all QuantumAlg.Primitives.WalshHadamard.Pipeline

/-!
# Predicate geometry and Grover's independent source operator

The original phase predicate and uniform-state reflection rotate the good/bad
plane. The resulting Born probability is exactly the original sine-squared
formula, including the all-marked case [dW19, qcnotes.tex:2760-2852].
Actual native execution, resource counts and measurement are connected to
this independently defined operator in separate execution owners.
-/

section

namespace QuantumAlg

open NormalizedVector

noncomputable section

namespace GroverSearch

open scoped BigOperators

/-! ### Predicate-derived good and bad states -/

/-- The finite set of indices selected by the search predicate. -/
public def markedIndices {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    Finset (Fin (2 ^ n)) :=
  Finset.univ.filter fun j => marked j = true

/-- The number of marked indices. -/
@[expose] public def markedCount {n : Nat} (marked : Fin (2 ^ n) → Bool) : Nat :=
  (markedIndices marked).card

/-- The public marked count is exactly the cardinality of the selected finite set. -/
public lemma markedCount_eq_card {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    markedCount marked = (Finset.univ.filter fun index : Fin (2 ^ n) =>
      marked index = true).card := by
  rfl

lemma markedCount_le_pow {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    markedCount marked ≤ 2 ^ n := by
  simpa [markedCount, markedIndices] using
    Finset.card_le_card
      (Finset.filter_subset (fun j => marked j = true) Finset.univ)

/-- If every possible index is counted as marked, the predicate is true on
every index. -/
lemma allMarked_of_markedCount_eq_pow {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (hcount : markedCount marked = 2 ^ n) :
    ∀ j, marked j = true := by
  have hset : markedIndices marked = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [markedCount] using hcount
  intro j
  have hj : j ∈ markedIndices marked := by rw [hset]; simp
  simpa [markedIndices] using hj

/-- Raw uniform vector on the marked indices. -/
def markedUniformVector {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    HilbertVector (Qubits n) :=
  WithLp.toLp 2 fun j =>
    if marked j then (Real.sqrt (markedCount marked) : ℂ)⁻¹ else 0

/-- Raw uniform vector on the unmarked indices. -/
def unmarkedUniformVector {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    HilbertVector (Qubits n) :=
  WithLp.toLp 2 fun j =>
    if marked j then 0
    else (Real.sqrt ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹

/-- The normalized uniform superposition of marked indices. -/
def markedUniformState {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector (markedUniformVector marked) (by
    classical
    rw [EuclideanSpace.norm_eq]
    have hsum :
        ∑ j : Fin (2 ^ n),
            ‖if marked j then (Real.sqrt (markedCount marked) : ℂ)⁻¹ else 0‖ ^ 2 =
          1 := by
      calc
        _ = ∑ j ∈ markedIndices marked,
              ‖(Real.sqrt (markedCount marked) : ℂ)⁻¹‖ ^ 2 := by
            rw [markedIndices, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : marked j = true <;> simp [hj]
        _ = (markedCount marked : Real) *
              (Real.sqrt (markedCount marked))⁻¹ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp [markedCount, Complex.norm_real,
              Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        _ = 1 := by
            rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
            exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr ht_pos.ne')
    change Real.sqrt
      (∑ j : Fin (2 ^ n),
        ‖if marked j then
            (Real.sqrt (markedCount marked) : ℂ)⁻¹ else 0‖ ^ 2) = 1
    rw [hsum, Real.sqrt_one])

/-- The normalized uniform superposition of unmarked indices.  The strict
marked-count bound prevents an invalid zero-vector normalization. -/
def unmarkedUniformState {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (ht_lt : markedCount marked < 2 ^ n) : NormalizedVector (Qubits n) :=
  NormalizedVector.ofVector (unmarkedUniformVector marked) (by
    classical
    rw [EuclideanSpace.norm_eq]
    have hremaining : 0 < 2 ^ n - markedCount marked := Nat.sub_pos_of_lt ht_lt
    have hunmarkedCard :
        (Finset.univ.filter fun j : Fin (2 ^ n) => marked j = false).card =
          2 ^ n - markedCount marked := by
      calc
        _ = Fintype.card (Fin (2 ^ n)) - (markedIndices marked).card := by
          rw [← Finset.card_compl]
          congr 1
          ext j
          simp [markedIndices]
        _ = _ := by simp [markedCount]
    have hsum :
        ∑ j : Fin (2 ^ n),
            ‖if marked j then 0
              else (Real.sqrt
                ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹‖ ^ 2 =
          1 := by
      calc
        _ = ∑ j ∈ Finset.univ.filter
              (fun j : Fin (2 ^ n) => marked j = false),
              ‖(Real.sqrt
                ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹‖ ^ 2 := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : marked j = true <;> simp [hj]
        _ = ((2 ^ n - markedCount marked : Nat) : Real) *
              (Real.sqrt
                ((2 ^ n - markedCount marked : Nat) : Real))⁻¹ ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hunmarkedCard]
            simp [Complex.norm_real,
              Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        _ = 1 := by
            rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
            exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hremaining.ne')
    change Real.sqrt
      (∑ j : Fin (2 ^ n),
        ‖if marked j then 0 else
            (Real.sqrt
              ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹‖ ^ 2) = 1
    rw [hsum, Real.sqrt_one])

@[simp] lemma markedUniformState_apply_of_marked {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_pos : 0 < markedCount marked)
    (j : Fin (2 ^ n)) (hj : marked j) :
    markedUniformState marked ht_pos j =
      (Real.sqrt (markedCount marked) : ℂ)⁻¹ := by
  simp [markedUniformState, markedUniformVector, hj]

@[simp] lemma markedUniformState_apply_of_unmarked {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_pos : 0 < markedCount marked)
    (j : Fin (2 ^ n)) (hj : ¬ marked j) :
    markedUniformState marked ht_pos j = 0 := by
  simp [markedUniformState, markedUniformVector, hj]

@[simp] lemma unmarkedUniformState_apply_of_marked {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_lt : markedCount marked < 2 ^ n)
    (j : Fin (2 ^ n)) (hj : marked j) :
    unmarkedUniformState marked ht_lt j = 0 := by
  simp [unmarkedUniformState, unmarkedUniformVector, hj]

@[simp] lemma unmarkedUniformState_apply_of_unmarked {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_lt : markedCount marked < 2 ^ n)
    (j : Fin (2 ^ n)) (hj : ¬ marked j) :
    unmarkedUniformState marked ht_lt j =
      (Real.sqrt ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹ := by
  simp [unmarkedUniformState, unmarkedUniformVector, hj]

/-- Marked and unmarked uniform states have disjoint support. -/
lemma markedUniformState_inner_unmarkedUniformState {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) :
    inner ℂ
        (markedUniformState marked ht_pos : HilbertVector (Qubits n))
        (unmarkedUniformState marked ht_lt : HilbertVector (Qubits n)) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp only [RCLike.inner_apply]
  by_cases hj : marked j
  · simp [markedUniformState_apply_of_marked,
      unmarkedUniformState_apply_of_marked, hj]
  · simp [markedUniformState_apply_of_unmarked,
      unmarkedUniformState_apply_of_unmarked, hj]

/-- The Grover angle determined by the actual marked count. -/
def groverAngle {n : Nat} (marked : Fin (2 ^ n) → Bool) : Real :=
  Real.arcsin
    (Real.sqrt ((markedCount marked : Real) / ((2 ^ n : Nat) : Real)))

private lemma markedRatio_nonneg {n : Nat}
    (marked : Fin (2 ^ n) → Bool) :
    0 ≤ (markedCount marked : Real) / ((2 ^ n : Nat) : Real) := by
  positivity

private lemma markedRatio_le_one {n : Nat}
    (marked : Fin (2 ^ n) → Bool) :
    (markedCount marked : Real) / ((2 ^ n : Nat) : Real) ≤ 1 := by
  apply (div_le_one (by positivity : (0 : Real) < ((2 ^ n : Nat) : Real))).2
  exact_mod_cast markedCount_le_pow marked

private lemma sin_groverAngle {n : Nat}
    (marked : Fin (2 ^ n) → Bool) :
    Real.sin (groverAngle marked) =
      Real.sqrt ((markedCount marked : Real) / ((2 ^ n : Nat) : Real)) := by
  rw [groverAngle, Real.sin_arcsin]
  · exact (by norm_num : (-1 : Real) ≤ 0).trans (Real.sqrt_nonneg _)
  · exact Real.sqrt_le_one.mpr (markedRatio_le_one marked)

private lemma cos_groverAngle {n : Nat}
    (marked : Fin (2 ^ n) → Bool) :
    Real.cos (groverAngle marked) =
      Real.sqrt
        (((2 ^ n - markedCount marked : Nat) : Real) /
          ((2 ^ n : Nat) : Real)) := by
  rw [groverAngle, Real.cos_arcsin]
  have hsq :
      Real.sqrt ((markedCount marked : Real) / ((2 ^ n : Nat) : Real)) ^ 2 =
        (markedCount marked : Real) / ((2 ^ n : Nat) : Real) :=
    Real.sq_sqrt (markedRatio_nonneg marked)
  rw [hsq]
  congr 1
  rw [Nat.cast_sub (markedCount_le_pow marked)]
  field_simp

private lemma sinAngle_mul_markedNormalization {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_pos : 0 < markedCount marked) :
    (Real.sin (groverAngle marked) : ℂ) *
        (Real.sqrt (markedCount marked) : ℂ)⁻¹ =
      WalshHadamard.invSqrtCard n := by
  have htReal : (0 : Real) < markedCount marked := by
    exact_mod_cast ht_pos
  have hmarkedSqrt :
      ((Real.sqrt (markedCount marked) : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr htReal)
  have hcardSqrt :
      ((Real.sqrt ((2 ^ n : Nat) : Real) : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  rw [sin_groverAngle, Real.sqrt_div (Nat.cast_nonneg _) ,
    WalshHadamard.invSqrtCard]
  push_cast
  field_simp [hmarkedSqrt, hcardSqrt]

private lemma cosAngle_mul_unmarkedNormalization {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_lt : markedCount marked < 2 ^ n) :
    (Real.cos (groverAngle marked) : ℂ) *
        (Real.sqrt ((2 ^ n - markedCount marked : Nat) : Real) : ℂ)⁻¹ =
      WalshHadamard.invSqrtCard n := by
  have hremainingReal :
      (0 : Real) < ((2 ^ n - markedCount marked : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt ht_lt
  have hremainingSqrt :
      ((Real.sqrt ((2 ^ n - markedCount marked : Nat) : Real) : Real) :
        Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hremainingReal)
  have hcardSqrt :
      ((Real.sqrt ((2 ^ n : Nat) : Real) : Real) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  rw [cos_groverAngle, Real.sqrt_div (Nat.cast_nonneg _),
    WalshHadamard.invSqrtCard]
  push_cast
  field_simp [hremainingSqrt, hcardSqrt]

/-- Source decomposition of the uniform state into predicate-derived marked
and unmarked directions. -/
lemma uniformState_decomposition {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) :
    (WalshHadamard.uniformState n : HilbertVector (Qubits n)) =
      ((Real.sin (groverAngle marked) : ℂ) •
          (markedUniformState marked ht_pos : HilbertVector (Qubits n))) +
        ((Real.cos (groverAngle marked) : ℂ) •
          (unmarkedUniformState marked ht_lt : HilbertVector (Qubits n))) := by
  apply WithLp.ofLp_injective
  funext j
  by_cases hj : marked j
  · simp only [WalshHadamard.uniformState_apply,
      markedUniformState_apply_of_marked,
      unmarkedUniformState_apply_of_marked, hj,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_zero, add_zero]
    exact (sinAngle_mul_markedNormalization marked ht_pos).symm
  · change WalshHadamard.invSqrtCard n =
      (Real.sin (groverAngle marked) : ℂ) * markedUniformState marked ht_pos j +
        (Real.cos (groverAngle marked) : ℂ) *
          unmarkedUniformState marked ht_lt j
    rw [markedUniformState_apply_of_unmarked marked ht_pos j hj,
      unmarkedUniformState_apply_of_unmarked marked ht_lt j hj,
      mul_zero, zero_add]
    exact (cosAngle_mul_unmarkedNormalization marked ht_lt).symm

/-! ### Independent diffusion and source evolution -/

/-- The semantic diffusion operator `2|U><U|-I`. -/
def diffusionOperator (n : Nat) : UnitaryOperator (Qubits n) :=
  OrthogonalProjector.rankOneReflectionOp (WalshHadamard.uniformState n)

/-- The source's full measurement-free evolution, independently of any native implementation. -/
def sourceOperator {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    UnitaryOperator (Qubits n) :=
  (diffusionOperator n * phaseOracleOp marked) ^ k * WalshHadamard.hadamardLayerOperator n

@[simp]
lemma diffusionOperator_zero :
    (diffusionOperator 0 : HilbertOperator (Qubits 0)) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [diffusionOperator, OrthogonalProjector.rankOneReflectionOp,
    OrthogonalProjector.reflectionOp, OrthogonalProjector.rankOne,
    OrthogonalProjector.rankOneOp, WalshHadamard.uniformState,
    WalshHadamard.invSqrtCard, UnitaryOperator.ofMatrix]

lemma diffusionDecomposition_applyVec (n : Nat)
    (state : HilbertVector (Qubits n)) :
    ((WalshHadamard.hadamardLayerOperator n) *
      (ZeroReflection.zeroReflectionOperator n *
        (WalshHadamard.hadamardLayerOperator n).dagger)).applyVec state =
      (diffusionOperator n).applyVec state := by
  rw [UnitaryOperator.mul_applyVec, UnitaryOperator.mul_applyVec]
  rw [ZeroReflection.zeroReflectionOperator, diffusionOperator,
    OrthogonalProjector.rankOneReflectionOp_applyVec,
    OrthogonalProjector.rankOneReflectionOp_applyVec]
  have hinner :
      inner ℂ (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
        HilbertVector (Qubits n))
          ((WalshHadamard.hadamardLayerOperator n).dagger.applyVec state) =
        inner ℂ
          ((WalshHadamard.hadamardLayerOperator n).applyVec
            (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
              HilbertVector (Qubits n))) state := by
    calc
      inner ℂ (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
        HilbertVector (Qubits n))
          ((WalshHadamard.hadamardLayerOperator n).dagger.applyVec state) =
        inner ℂ
          ((WalshHadamard.hadamardLayerOperator n).applyVec
            (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
              HilbertVector (Qubits n)))
          ((WalshHadamard.hadamardLayerOperator n).applyVec
            ((WalshHadamard.hadamardLayerOperator n).dagger.applyVec state)) := by
              symm
              exact (WalshHadamard.hadamardLayerOperator n).inner_applyVec_applyVec _ _
      _ = inner ℂ
          ((WalshHadamard.hadamardLayerOperator n).applyVec
            (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
              HilbertVector (Qubits n))) state := by
              rw [AmplitudeAmplification.unitary_applyVec_dagger_applyVec]
  have hzero :
      (WalshHadamard.hadamardLayerOperator n).applyVec
          (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
            HilbertVector (Qubits n)) =
        (WalshHadamard.uniformState n : HilbertVector (Qubits n)) := by
    simpa only [UnitaryOperator.apply_coe] using congrArg
      (fun normalized : NormalizedVector (Qubits n) =>
        (normalized : HilbertVector (Qubits n)))
      (WalshHadamard.hadamardLayerOperator_apply_zero (n := n))
  rw [(WalshHadamard.hadamardLayerOperator n).applyVec_sub,
    (WalshHadamard.hadamardLayerOperator n).applyVec_smul,
    AmplitudeAmplification.unitary_applyVec_dagger_applyVec, hinner, hzero]

/-- The concrete phase oracle acts diagonally on any state vector. -/
lemma phaseOracleOp_applyVec_apply {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (state : HilbertVector (Qubits n))
    (j : Fin (2 ^ n)) :
    (phaseOracleOp marked).applyVec state j =
      (if marked j then -1 else 1 : ℂ) * state j := by
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply]
  change (∑ k : Fin (2 ^ n),
    (if j = k then (if marked k then -1 else 1 : ℂ) else 0) * state k) = _
  simp only [ite_mul, zero_mul]
  rw [Fintype.sum_ite_eq]

/-- The actual phase oracle negates the normalized marked-uniform direction. -/
lemma phaseOracle_apply_markedUniformState {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_pos : 0 < markedCount marked) :
    (phaseOracleOp marked).applyVec
        (markedUniformState marked ht_pos : HilbertVector (Qubits n)) =
      -(markedUniformState marked ht_pos : HilbertVector (Qubits n)) := by
  apply WithLp.ofLp_injective
  funext j
  rw [phaseOracleOp_applyVec_apply]
  by_cases hj : marked j <;>
    simp [hj, markedUniformState_apply_of_marked,
      markedUniformState_apply_of_unmarked]

/-- The actual phase oracle fixes the normalized unmarked-uniform direction. -/
lemma phaseOracle_apply_unmarkedUniformState {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (ht_lt : markedCount marked < 2 ^ n) :
    (phaseOracleOp marked).applyVec
        (unmarkedUniformState marked ht_lt : HilbertVector (Qubits n)) =
      (unmarkedUniformState marked ht_lt : HilbertVector (Qubits n)) := by
  apply WithLp.ofLp_injective
  funext j
  rw [phaseOracleOp_applyVec_apply]
  by_cases hj : marked j <;>
    simp [hj, unmarkedUniformState_apply_of_marked,
      unmarkedUniformState_apply_of_unmarked]

private lemma hadamardLayerOperator_applyVec_zero (n : Nat) :
    (WalshHadamard.hadamardLayerOperator n).applyVec
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
          HilbertVector (Qubits n)) =
      (WalshHadamard.uniformState n : HilbertVector (Qubits n)) := by
  simpa only [UnitaryOperator.apply_coe] using congrArg
    (fun state : NormalizedVector (Qubits n) =>
      (state : HilbertVector (Qubits n)))
    (WalshHadamard.hadamardLayerOperator_apply_zero (n := n))

/-- The nontrivial marked/unmarked plane as an intrinsic amplitude-amplification
model.  Its preparation is the same initial Hadamard circuit used by Grover. -/
def nontrivialModel {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) :
    IntrinsicAmplitudeAmplificationModel n where
  θ := groverAngle marked
  preparation := WalshHadamard.hadamardLayerOperator n
  good := markedUniformState marked ht_pos
  bad := unmarkedUniformState marked ht_lt
  good_bad_inner :=
    markedUniformState_inner_unmarkedUniformState marked ht_pos ht_lt
  prepares_start := by
    rw [hadamardLayerOperator_applyVec_zero]
    exact uniformState_decomposition marked ht_pos ht_lt

private lemma phaseOracle_apply_stateAt_eq_badReflection {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (α : Real) :
    (phaseOracleOp marked).applyVec
        ((nontrivialModel marked ht_pos ht_lt).stateAt α) =
      (OrthogonalProjector.rankOneReflectionOp
          (nontrivialModel marked ht_pos ht_lt).bad).applyVec
        ((nontrivialModel marked ht_pos ht_lt).stateAt α) := by
  rw [AmplitudeAmplification.intrinsicBadReflection_apply_stateAt]
  rw [IntrinsicAmplitudeAmplificationModel.stateAt_coe]
  simp only [nontrivialModel, UnitaryOperator.applyVec_add,
    UnitaryOperator.applyVec_smul, phaseOracle_apply_markedUniformState,
    phaseOracle_apply_unmarkedUniformState]
  module

private lemma diffusionOperator_applyVec_eq_preparedReflection {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n)
    (state : HilbertVector (Qubits n)) :
    (diffusionOperator n).applyVec state =
      (nontrivialModel marked ht_pos ht_lt).preparation.applyVec
        ((OrthogonalProjector.rankOneReflectionOp
            (nontrivialModel marked ht_pos ht_lt).zeroKet).applyVec
          ((nontrivialModel marked ht_pos ht_lt).preparation.dagger.applyVec state)) := by
  rw [diffusionOperator,
    OrthogonalProjector.rankOneReflectionOp_applyVec,
    AmplitudeAmplification.intrinsicPreparedReflection_applyVec]
  have hprepared :
      (nontrivialModel marked ht_pos ht_lt).preparation.applyVec
          ((nontrivialModel marked ht_pos ht_lt).zeroKet : HilbertVector (Qubits n)) =
        (WalshHadamard.uniformState n : HilbertVector (Qubits n)) := by
    simpa only [nontrivialModel,
      IntrinsicAmplitudeAmplificationModel.zeroKet] using
      hadamardLayerOperator_applyVec_zero n
  rw [hprepared]

/-- The actual phase-oracle/diffusion product advances the predicate-derived
good/bad plane by `2 theta`.  The bridge is deliberately an action theorem on
that plane, not a false full-space operator equality. -/
private lemma groverStepOperator_apply_stateAt_coe {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (α : Real) :
    (diffusionOperator n * phaseOracleOp marked).applyVec
        ((nontrivialModel marked ht_pos ht_lt).stateAt α) =
      (nontrivialModel marked ht_pos ht_lt).stateAt
        (α + 2 * groverAngle marked) := by
  have hsource :
      (AmplitudeAmplification.intrinsicSourceStepOperator
          (nontrivialModel marked ht_pos ht_lt)).applyVec
          ((nontrivialModel marked ht_pos ht_lt).stateAt α) =
        ((nontrivialModel marked ht_pos ht_lt).stateAt
          (α + 2 * groverAngle marked) : HilbertVector (Qubits n)) := by
    simpa only [UnitaryOperator.apply_coe, nontrivialModel] using congrArg
      (fun state : NormalizedVector (Qubits n) =>
        (state : HilbertVector (Qubits n)))
      (AmplitudeAmplification.intrinsicSourceStepOperator_apply_stateAt
        (nontrivialModel marked ht_pos ht_lt) α)
  rw [UnitaryOperator.mul_applyVec,
    phaseOracle_apply_stateAt_eq_badReflection,
    diffusionOperator_applyVec_eq_preparedReflection]
  simpa only [AmplitudeAmplification.intrinsicSourceStepOperator,
      UnitaryOperator.mul_applyVec, nontrivialModel] using
    hsource

/-- The concrete Grover step maps normalized plane states to normalized plane
states. -/
lemma groverStepOperator_apply_stateAt {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (α : Real) :
    (diffusionOperator n * phaseOracleOp marked).apply
        ((nontrivialModel marked ht_pos ht_lt).stateAt α) =
      (nontrivialModel marked ht_pos ht_lt).stateAt
        (α + 2 * groverAngle marked) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun state : HilbertVector (Qubits n) => state i)
    (groverStepOperator_apply_stateAt_coe marked ht_pos ht_lt α)

private lemma groverStepOperator_apply_amplifiedState {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    (diffusionOperator n * phaseOracleOp marked).applyVec
        ((nontrivialModel marked ht_pos ht_lt).amplifiedState k) =
      (nontrivialModel marked ht_pos ht_lt).amplifiedState (k + 1) := by
  rw [IntrinsicAmplitudeAmplificationModel.amplifiedState,
    groverStepOperator_apply_stateAt_coe]
  unfold IntrinsicAmplitudeAmplificationModel.amplifiedState
  congr 1
  simp only [nontrivialModel]
  unfold amplitudeAmplificationAngle
  push_cast
  ring_nf

private lemma groverStepOperator_pow_apply_uniform {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    HilbertOperator.applyVec
        (((diffusionOperator n * phaseOracleOp marked :
          UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) ^ k)
        (WalshHadamard.uniformState n : HilbertVector (Qubits n)) =
      (nontrivialModel marked ht_pos ht_lt).amplifiedState k := by
  have hstart :
      (WalshHadamard.uniformState n : HilbertVector (Qubits n)) =
        (nontrivialModel marked ht_pos ht_lt).amplifiedState 0 := by
    have hprepared := congrArg
      (fun state : NormalizedVector (Qubits n) =>
        (state : HilbertVector (Qubits n)))
      (IntrinsicAmplitudeAmplificationModel.prepared_eq_amplifiedState_zero
        (nontrivialModel marked ht_pos ht_lt))
    rw [← hprepared]
    simpa only [UnitaryOperator.apply_coe, nontrivialModel,
      IntrinsicAmplitudeAmplificationModel.zeroKet] using
      (hadamardLayerOperator_applyVec_zero n).symm
  induction k with
  | zero => simpa [HilbertOperator.one_applyVec] using hstart
  | succ k ih =>
      rw [pow_succ', HilbertOperator.mul_applyVec, ih]
      exact groverStepOperator_apply_amplifiedState marked ht_pos ht_lt k

/-- The independent source evolution has the exact nontrivial-plane closed form. -/
private lemma sourceOperator_apply_zero_coe {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    (sourceOperator marked k).applyVec
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)) :
          HilbertVector (Qubits n)) =
      (nontrivialModel marked ht_pos ht_lt).amplifiedState k := by
  rw [sourceOperator, UnitaryOperator.mul_applyVec, hadamardLayerOperator_applyVec_zero]
  exact groverStepOperator_pow_apply_uniform marked ht_pos ht_lt k

/-- The source operator sends the normalized zero input to the normalized closed form. -/
lemma sourceOperator_apply_zero {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    (sourceOperator marked k).apply
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))) =
      (nontrivialModel marked ht_pos ht_lt).amplifiedState k := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun state : HilbertVector (Qubits n) => state i)
    (sourceOperator_apply_zero_coe marked ht_pos ht_lt k)

/-! ### The evolved vector and its exact mathematical Born probability -/

/-- Canonical physical placement of the complete search register. -/
def layout (n : Nat) : QubitLayout n where
  physical_idx := fun index => index.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp] lemma layout_systemIdx (n : Nat) :
    (layout n).systemIdx = List.range n := by
  simp [layout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Canonically placed all-zero input.  The Hadamard preparation is kept in the
source operator rather than hidden in the input state. -/
def inputState (n : Nat) : QubitLayout.State (layout n) where
  state := PureState.ofNormalized
    (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n)))
    (layout n).systemIdx
  system_idx_eq := rfl

/-- Grover succeeds exactly when the returned full-register index satisfies
the same predicate queried by the circuit. -/
def SuccessfulIndex {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (j : Fin (2 ^ n)) : Prop :=
  marked j = true

/-- The normalized state predicted by the independent source evolution. -/
def evolvedState {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    QubitLayout.State (layout n) :=
  { state := PureState.ofNormalized
      ((sourceOperator marked k).apply
        (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))))
      (layout n).systemIdx
    system_idx_eq := rfl }

lemma evolvedState_vector {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    (evolvedState marked k).normalized =
      (nontrivialModel marked ht_pos ht_lt).amplifiedState k := by
  change (sourceOperator marked k).apply
      (NormalizedVector.ket (R := Qubits n) (0 : Fin (2 ^ n))) = _
  exact sourceOperator_apply_zero marked ht_pos ht_lt k

/-- Marked-event mass of the Born PMF of the exact evolved state. -/
noncomputable def sourceSuccessProbability {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat) : ENNReal :=
  (QubitLayout.basisPMF (evolvedState marked k)).toOuterMeasure
    {index | SuccessfulIndex marked index}

private lemma amplifiedState_markedMass {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    ∑ j ∈ markedIndices marked,
        ‖(nontrivialModel marked ht_pos ht_lt).amplifiedState k j‖ ^ 2 =
      Real.sin (amplitudeAmplificationAngle (groverAngle marked) k) ^ 2 := by
  classical
  have hterm : ∀ j ∈ markedIndices marked,
      ‖(nontrivialModel marked ht_pos ht_lt).amplifiedState k j‖ ^ 2 =
        Real.sin (amplitudeAmplificationAngle (groverAngle marked) k) ^ 2 /
          markedCount marked := by
    intro j hj
    have hmarked : marked j := by simpa [markedIndices] using hj
    change ‖(((nontrivialModel marked ht_pos ht_lt).amplifiedState k :
      HilbertVector (Qubits n)) j)‖ ^ 2 = _
    rw [IntrinsicAmplitudeAmplificationModel.amplifiedState_coe,
      IntrinsicAmplitudeAmplificationModel.stateAt_coe]
    simp only [nontrivialModel, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      markedUniformState_apply_of_marked marked ht_pos j hmarked,
      unmarkedUniformState_apply_of_marked marked ht_lt j hmarked,
      mul_zero, add_zero]
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow, sq_abs, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]
  calc
    _ = ∑ _j ∈ markedIndices marked,
        (Real.sin (amplitudeAmplificationAngle (groverAngle marked) k) ^ 2 /
          markedCount marked) := Finset.sum_congr rfl hterm
    _ = markedCount marked *
        (Real.sin (amplitudeAmplificationAngle (groverAngle marked) k) ^ 2 /
          markedCount marked) := by
          rw [Finset.sum_const, nsmul_eq_mul, markedCount]
    _ = _ := by
      field_simp [Nat.cast_ne_zero.mpr ht_pos.ne']

private lemma nontrivial_sourceSuccessProbability_eq {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_pos : 0 < markedCount marked)
    (ht_lt : markedCount marked < 2 ^ n) (k : Nat) :
    sourceSuccessProbability marked k =
      ENNReal.ofReal
        (Real.sin (amplitudeAmplificationAngle (groverAngle marked) k) ^ 2) := by
  classical
  rw [sourceSuccessProbability, PMF.toOuterMeasure_apply_fintype]
  calc
    ∑ j : Fin (2 ^ n),
        Set.indicator {j | SuccessfulIndex marked j}
          (QubitLayout.basisPMF (evolvedState marked k)) j =
        ∑ j ∈ markedIndices marked,
          ENNReal.ofReal
            (‖(nontrivialModel marked ht_pos ht_lt).amplifiedState k j‖ ^ 2) := by
      rw [markedIndices, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : marked j
      · simp only [SuccessfulIndex, hj, Set.mem_ofPred_eq,
          Set.indicator_of_mem, QubitLayout.basisPMF_apply]
        rw [congrArg (fun state : NormalizedVector (Qubits n) => state j)
          (evolvedState_vector marked ht_pos ht_lt k)]
        simp only [if_true]
      · simp [SuccessfulIndex, hj]
    _ = ENNReal.ofReal
        (∑ j ∈ markedIndices marked,
          ‖(nontrivialModel marked ht_pos ht_lt).amplifiedState k j‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro j _
      positivity
    _ = _ := by rw [amplifiedState_markedMass]

private lemma allMarked_sourceSuccessProbability_eq_one {n : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (hcount : markedCount marked = 2 ^ n) (k : Nat) :
    sourceSuccessProbability marked k = 1 := by
  classical
  have hall := allMarked_of_markedCount_eq_pow marked hcount
  rw [sourceSuccessProbability, PMF.toOuterMeasure_apply_fintype]
  simp only [SuccessfulIndex, hall, Set.mem_ofPred_eq, Set.indicator_of_mem]
  simpa only [tsum_fintype] using
    (QubitLayout.basisPMF (evolvedState marked k)).tsum_coe

private lemma allMarked_sourceProbability_eq_one {n t k : Nat}
    (ht : t = 2 ^ n) :
    ENNReal.ofReal
        (Real.sin (((2 : Real) * k + 1) *
          Real.arcsin (Real.sqrt ((t : Real) / ((2 ^ n : Nat) : Real)))) ^ 2) =
      1 := by
  subst t
  have hangle :
      ((2 : Real) * k + 1) * (Real.pi / 2) =
        Real.pi / 2 + k * Real.pi := by ring
  rw [show (((2 ^ n : Nat) : Real) / ((2 ^ n : Nat) : Real)) = 1 by
      field_simp,
    Real.sqrt_one, Real.arcsin_one, hangle,
    Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  simp only [mul_one]
  have hsign_sq : (((-1 : Real) ^ k) ^ 2) = 1 := by
    calc
      _ = |(-1 : Real) ^ k| ^ 2 := (sq_abs _).symm
      _ = 1 := by rw [abs_neg_one_pow]; norm_num
  rw [hsign_sq, ENNReal.ofReal_one]

/-- Exact marked-event mass of the evolved-state Born PMF, including the
all-marked and `n=0` edge case. -/
lemma sourceSuccessProbability_eq {n t k : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (ht_count : markedCount marked = t) (ht_pos : 0 < t) :
    sourceSuccessProbability marked k =
      ENNReal.ofReal
        (Real.sin (((2 : Real) * k + 1) *
          Real.arcsin (Real.sqrt ((t : Real) / ((2 ^ n : Nat) : Real)))) ^ 2) := by
  by_cases h_all : t = 2 ^ n
  · rw [allMarked_sourceSuccessProbability_eq_one marked
        (ht_count.trans h_all) k,
      allMarked_sourceProbability_eq_one h_all]
  · have ht_lt : t < 2 ^ n :=
      lt_of_le_of_ne (ht_count ▸ markedCount_le_pow marked) h_all
    have hcount_pos : 0 < markedCount marked := by
      simpa [ht_count] using ht_pos
    have hcount_lt : markedCount marked < 2 ^ n := ht_count.trans_lt ht_lt
    rw [nontrivial_sourceSuccessProbability_eq marked hcount_pos hcount_lt]
    simp [groverAngle, amplitudeAmplificationAngle, ht_count]

/-- The concrete phase oracle has the source-stated action on every basis
index. -/
lemma main_phase_oracle_basis_action {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (j : Fin (2 ^ n)) :
    (phaseOracleOp marked).applyVec
        (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) =
      (if marked j then -1 else 1 : ℂ) •
        (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) := by
  exact phaseOracle_apply_ket marked j

end GroverSearch

end

end QuantumAlg

end

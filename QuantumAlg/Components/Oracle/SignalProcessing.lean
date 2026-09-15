/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Signal-processing oracle components

Reusable QSVT signal, projector, and phase declarations. Each declaration
owns its resource coordinate. Derived families own their operator construction;
the opaque signal-unitary seam explicitly accepts certified semantics.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT

noncomputable section

/-! ## Signal-unitary query -/

/-- Stable opaque-subroutine family for an `N`-qubit QSVT signal unitary. -/
def qsvtOracleLabel (N : ℕ) : Resource.SubroutineLabel where
  family := "qsvt"
  name := "qsvt-signal-unitary"
  parameters := [N]



/-- Literal strict event for one QSVT signal-unitary query. -/
def qsvtOracleEvent (N : ℕ) : Resource.Event .quantum :=
  .quantumSubroutine (qsvtOracleLabel N).quantum



/-- Compatibility constructor for the certified QSVT signal operator. -/
def qsvtOracleOp {N : ℕ} (U : UnitaryOperator (Qubits N)) :
    UnitaryOperator (Qubits N) :=
  U

/-- A QSVT signal query with explicit certified semantics at a caller-supplied
physical placement. -/
def qsvtOracleLeafAt {N : ℕ} (U : UnitaryOperator (Qubits N))
    (systemIdx : List Nat) : UnitaryLeaf (Qubits N) :=
  UnitaryLeaf.subroutine (qsvtOracleLabel N) systemIdx U

/-- A QSVT signal query on its canonical signal-register placement. -/
def qsvtOracleLeaf {N : ℕ} (U : UnitaryOperator (Qubits N)) :
    UnitaryLeaf (Qubits N) :=
  qsvtOracleLeafAt U (List.range N)

/-! ## Projector-controlled NOT queries -/

/-- The two fixed projector roles in projected QSVT. -/
inductive QSVTProjectorSide where
  | left
  | right
deriving DecidableEq

/-- Stable left-projector controlled-NOT subroutine family. -/
def qsvtLeftProjectorOracleLabel (N : ℕ) : Resource.SubroutineLabel where
  family := "qsvt"
  name := "qsvt-left-projector-controlled-not"
  parameters := [N]

/-- Stable right-projector controlled-NOT subroutine family. -/
def qsvtRightProjectorOracleLabel (N : ℕ) : Resource.SubroutineLabel where
  family := "qsvt"
  name := "qsvt-right-projector-controlled-not"
  parameters := [N]



/-- Literal strict event for one left-projector query. -/
def qsvtLeftProjectorOracleEvent (N : ℕ) : Resource.Event .quantum :=
  .quantumSubroutine (qsvtLeftProjectorOracleLabel N).quantum





/-- Literal strict event for one right-projector query. -/
def qsvtRightProjectorOracleEvent (N : ℕ) : Resource.Event .quantum :=
  .quantumSubroutine (qsvtRightProjectorOracleLabel N).quantum



/-- The fixed projector side selected at one remaining phase slot. -/
def qsvtProjectorSide (remaining : ℕ) : QSVTProjectorSide :=
  if remaining % 2 = 0 then .right else .left

/-- The role-specific projector query selected at one remaining phase slot. -/
def qsvtProjectorOracleLabel (N remaining : ℕ) : Resource.SubroutineLabel :=
  if remaining % 2 = 0 then qsvtRightProjectorOracleLabel N
  else qsvtLeftProjectorOracleLabel N



/-- Literal strict event for the parity-selected projector query. -/
def qsvtProjectorOracleEvent (N remaining : ℕ) :
    Resource.Event .quantum :=
  .quantumSubroutine (qsvtProjectorOracleLabel N remaining).quantum

section ProjectorControlledNotLeaves

variable {N : Nat} (P : OrthogonalProjector N)

/-- A left-projector controlled NOT at a caller-supplied placement. -/
def qsvtLeftProjectorControlledNotLeafAt
    (systemIdx : List Nat) : UnitaryLeaf (Qubits (1 + N)) :=
  UnitaryLeaf.subroutine (qsvtLeftProjectorOracleLabel N) systemIdx
    (OrthogonalProjector.controlledNotOp P)

/-- A right-projector controlled NOT at a caller-supplied placement. -/
def qsvtRightProjectorControlledNotLeafAt
    (systemIdx : List Nat) : UnitaryLeaf (Qubits (1 + N)) :=
  UnitaryLeaf.subroutine (qsvtRightProjectorOracleLabel N) systemIdx
    (OrthogonalProjector.controlledNotOp P)

end ProjectorControlledNotLeaves

/-- A role-specific projector-controlled NOT on its canonical placement. -/
def qsvtProjectorControlledNotLeaf {N : Nat} (side : QSVTProjectorSide)
    (P : OrthogonalProjector N) : UnitaryLeaf (Qubits (1 + N)) :=
  match side with
  | .left => qsvtLeftProjectorControlledNotLeafAt P (List.range (1 + N))
  | .right => qsvtRightProjectorControlledNotLeafAt P (List.range (1 + N))

/-! ## Projected phase declarations -/

/-- One declared phase-rotation coordinate in the projected-QSVT
implementation. -/
def qsvtControlledPhaseLabel : Resource.GateLabel :=
  .declared "qsvt" "qsvt-controlled-phase"



/-- Literal strict event for one projected-QSVT controlled phase. -/
def qsvtControlledPhaseEvent : Resource.Event .quantum :=
  .gate qsvtControlledPhaseLabel



/-- A projected-QSVT phase rotation at a caller-supplied placement. -/
def qsvtControlledPhaseLeafAt (φ : ℝ)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits 1) :=
  UnitaryLeaf.gate qsvtControlledPhaseLabel systemIdx (rotZStdOp φ)

/-- A projected-QSVT phase rotation on its canonical ancilla placement. -/
def qsvtControlledPhaseLeaf (φ : ℝ) : UnitaryLeaf (Qubits 1) :=
  qsvtControlledPhaseLeafAt φ [0]

/-! ## Source projector phase -/

/-- Stable source-projector phase gate coordinate. -/
def qsvtSourceProjectorPhaseLabel : Resource.GateLabel :=
  .declared "qsvt" "qsvt-projector-phase"



/-- Literal strict event for one source-projector phase. -/
def qsvtSourceProjectorPhaseEvent : Resource.Event .quantum :=
  .gate qsvtSourceProjectorPhaseLabel

/-- The source projector phase `e^{iφ(2P-I)}` as a metadata-free unitary.
[GSLW19, BlockHam.tex:738-745,883-887]. -/
def projectorPhaseMatrix {N : Nat} (φ : ℝ)
    (P : OrthogonalProjector N) : HilbertOperator (Qubits N) :=
  Complex.exp (φ * Complex.I) • P.op +
    Complex.exp (-(φ * Complex.I)) • OrthogonalProjector.complement P

/-- The certified source-projector phase operator. -/
def projectorPhaseOp {N : Nat} (φ : ℝ)
    (P : OrthogonalProjector N) : UnitaryOperator (Qubits N) :=
  UnitaryOperator.ofMatrix (projectorPhaseMatrix φ P) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hconj :
        (projectorPhaseMatrix φ P).conjTranspose =
          Complex.exp (-(φ * Complex.I)) • P.op +
            Complex.exp (φ * Complex.I) • OrthogonalProjector.complement P := by
      unfold projectorPhaseMatrix
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_smul, P.selfAdjoint,
        OrthogonalProjector.complement_conjTranspose]
      simp [conj_exp_I, conj_exp_neg_I]
    rw [hconj]
    unfold projectorPhaseMatrix
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [P.idempotent, OrthogonalProjector.mul_complement,
      OrthogonalProjector.complement_mul, OrthogonalProjector.complement_sq]
    simp only [exp_neg_I_mul_exp_I, one_smul, smul_zero, add_zero,
      exp_I_mul_exp_neg_I, zero_add]
    have hsum :
        P.op + OrthogonalProjector.complement P =
          (1 : HilbertOperator (Qubits N)) := by
      simp [OrthogonalProjector.complement]
    exact hsum)

@[simp]
theorem coe_projectorPhaseOp {N : Nat} (φ : ℝ)
    (P : OrthogonalProjector N) :
    (projectorPhaseOp φ P : HilbertOperator (Qubits N)) =
      Complex.exp (φ * Complex.I) • P.op +
        Complex.exp (-(φ * Complex.I)) • OrthogonalProjector.complement P :=
  rfl

/-- On the projector image, the source projector phase acts by `e^{i phi}`. -/
theorem projectorPhaseOp_applyVec_of_projector_applyVec_eq_self {N : Nat}
    (φ : ℝ) (P : OrthogonalProjector N) {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec P.op ψ = ψ) :
    HilbertOperator.applyVec (projectorPhaseOp φ P) ψ =
      Complex.exp (φ * Complex.I) • ψ := by
  change HilbertOperator.applyVec
      (Complex.exp (φ * Complex.I) • P.op +
        Complex.exp (-(φ * Complex.I)) • OrthogonalProjector.complement P) ψ = _
  rw [HilbertOperator.add_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.smul_applyVec, hpsi,
    OrthogonalProjector.complement_applyVec_eq_zero_of_projector_applyVec_eq_self
      P hpsi]
  simp

/-- On the projector complement, the source projector phase acts by
`e^{-i phi}`. -/
theorem projectorPhaseOp_applyVec_of_complement_applyVec_eq_self {N : Nat}
    (φ : ℝ) (P : OrthogonalProjector N) {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ = ψ) :
    HilbertOperator.applyVec (projectorPhaseOp φ P) ψ =
      Complex.exp (-(φ * Complex.I)) • ψ := by
  change HilbertOperator.applyVec
      (Complex.exp (φ * Complex.I) • P.op +
        Complex.exp (-(φ * Complex.I)) • OrthogonalProjector.complement P) ψ = _
  rw [HilbertOperator.add_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.smul_applyVec,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self P hpsi,
    hpsi]
  simp

/-- A source projector phase at a caller-supplied placement. -/
def projectorPhaseLeafAt {N : Nat} (φ : ℝ) (P : OrthogonalProjector N)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits N) :=
  UnitaryLeaf.gate qsvtSourceProjectorPhaseLabel systemIdx
    (projectorPhaseOp φ P)

/-- A source projector phase on its canonical signal-register placement. -/
def projectorPhaseLeaf {N : Nat} (φ : ℝ)
    (P : OrthogonalProjector N) : UnitaryLeaf (Qubits N) :=
  projectorPhaseLeafAt φ P (List.range N)

/-! ## Branch global phase -/

/-- Raw global-phase scaling formula. -/
def phaseScaledOperatorRaw {R : Register} (ζ : ℂ)
    (V : UnitaryOperator R) : HilbertOperator R :=
  ζ • (V : HilbertOperator R)

/-- Certify global-phase scaling under the unit-modulus side condition. -/
def phaseScaledOperator {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (V : UnitaryOperator R) : UnitaryOperator R :=
  UnitaryOperator.ofMatrix (ζ • (V : HilbertOperator R)) (by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm]
    have hphase : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj]
      exact_mod_cast hζ
    have hphase' : ζ * star ζ = 1 := by
      simpa using hphase
    rw [hphase', one_smul]
    exact Matrix.mem_unitaryGroup_iff.mp V.property)

@[simp]
theorem phaseScaledOperator_coe {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (V : UnitaryOperator R) :
    ((phaseScaledOperator ζ hζ V : UnitaryOperator R) : HilbertOperator R) =
      phaseScaledOperatorRaw ζ V :=
  rfl

/-- Stable gate coordinate for an explicit global phase on one QSVT branch. -/
def qsvtBranchPhaseLabel : Resource.GateLabel :=
  .declared "qsvt" "qsvt-branch-global-phase"



/-- Literal strict event for one explicit branch-global phase. -/
def qsvtBranchPhaseEvent : Resource.Event .quantum :=
  .gate qsvtBranchPhaseLabel



/-- The family-specialized global phase applied to the identity operator. -/
def qsvtBranchPhaseOp {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) : UnitaryOperator R :=
  UnitaryOperator.ofMatrix (ζ • (1 : HilbertOperator R)) (by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm]
    have hphase : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj]
      exact_mod_cast hζ
    have hphase' : ζ * star ζ = 1 := by
      simpa using hphase
    rw [hphase', one_smul]
    exact Matrix.mem_unitaryGroup_iff.mp
      (1 : UnitaryOperator R).property)

/-- A global branch phase at a caller-supplied placement. -/
def qsvtBranchPhaseLeafAt {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1)
    (systemIdx : List Nat) : UnitaryLeaf R :=
  UnitaryLeaf.gate qsvtBranchPhaseLabel systemIdx (qsvtBranchPhaseOp ζ hζ)

/-- A global branch phase on its canonical empty placement. -/
def qsvtBranchPhaseLeaf {R : Register} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) : UnitaryLeaf R :=
  qsvtBranchPhaseLeafAt ζ hζ []

/-! ## Scalar dilation -/

/-- The standard one-qubit unitary dilation of a scalar contraction `p`.
The top-left entry is `p`; the remaining entries make the matrix unitary when
`|p| ≤ 1`. -/
def scalarDilationOp (p : ℂ) : HilbertOperator (Qubits 1) :=
  !![p, ((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ);
    -((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ), star p]

/-- The scalar dilation is unitary under the contraction side condition. -/
theorem scalarDilationOp_mem_unitaryGroup (p : ℂ)
    (hp : Complex.normSq p <= 1) :
    scalarDilationOp p ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : Real.sqrt (1 - Complex.normSq p) *
      Real.sqrt (1 - Complex.normSq p) = 1 - Complex.normSq p := by
    rw [← sq, Real.sq_sqrt]
    linarith
  have hsC :
      ((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ) *
          ((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ) =
        ((1 - Complex.normSq p : ℝ) : ℂ) := by
    exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply, hsC,
      Complex.mul_conj]
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply]
    ring
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply]
    ring
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply, hsC,
      Complex.normSq_eq_conj_mul_self]

@[simp]
theorem scalarDilationOp_block_entry (p : ℂ) : scalarDilationOp p 0 0 = p := by
  simp [scalarDilationOp]

/-- Certified scalar dilation under the contraction side condition. -/
def scalarDilationOperator (p : ℂ)
    (hp : Complex.normSq p <= 1) : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix (scalarDilationOp p)
    (scalarDilationOp_mem_unitaryGroup p hp)

@[simp]
theorem scalarDilationOperator_block_entry (p : ℂ)
    (hp : Complex.normSq p <= 1) :
    (scalarDilationOperator p hp : HilbertOperator (Qubits 1)) 0 0 = p := by
  simp [scalarDilationOperator, scalarDilationOp]

/-- Block-diagonal direct sum of scalar dilations over a finite index set. -/
def diagonalScalarDilationOp {ι : Type*} [DecidableEq ι]
    (p : ι → ℂ) : Matrix (Fin (2 ^ 1) × ι) (Fin (2 ^ 1) × ι) ℂ :=
  Matrix.of fun r s =>
    if r.2 = s.2 then scalarDilationOp (p r.2) r.1 s.1 else 0

/-- A direct sum of scalar contraction dilations is unitary. -/
theorem diagonalScalarDilationOp_mem_unitaryGroup {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    diagonalScalarDilationOp p ∈
      Matrix.unitaryGroup (Fin (2 ^ 1) × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext r s
  rw [Matrix.mul_apply]
  by_cases hrs : r.2 = s.2
  · have hsr : s.2 = r.2 := hrs.symm
    have hunit := scalarDilationOp_mem_unitaryGroup (p r.2) (hp r.2)
    rw [Matrix.mem_unitaryGroup_iff] at hunit
    have hentry := congrFun (congrFun hunit r.1) s.1
    rw [Matrix.mul_apply] at hentry
    rw [Fintype.sum_prod_type]
    have hcollapse :
        (∑ x : Fin (2 ^ 1), ∑ y : ι,
            diagonalScalarDilationOp p r (x, y) *
              star (diagonalScalarDilationOp p) (x, y) s) =
          ∑ x : Fin (2 ^ 1),
            scalarDilationOp (p r.2) r.1 x *
              star (scalarDilationOp (p r.2)) x s.1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single r.2]
      · unfold diagonalScalarDilationOp
        rw [Matrix.star_apply]
        rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, if_pos hsr]
        rw [hsr]
        rw [Matrix.star_apply]
      · intro y _ hy
        have hyr : ¬r.2 = y := fun h => hy h.symm
        unfold diagonalScalarDilationOp
        rw [Matrix.of_apply, if_neg hyr, zero_mul]
      · intro hmissing
        exact False.elim (hmissing (Finset.mem_univ r.2))
    have hone :
        (1 : Matrix (Fin (2 ^ 1) × ι) (Fin (2 ^ 1) × ι) ℂ) r s =
          (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) r.1 s.1 := by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases h1 : r.1 = s.1
      · have hpairs : r = s := Prod.ext h1 hrs
        simp [hpairs]
      · have hpairs : r ≠ s := fun h => h1 (congrArg Prod.fst h)
        simp [hpairs, h1]
    rw [hcollapse, hone]
    exact hentry
  · rw [Fintype.sum_prod_type]
    have hsr : ¬s.2 = r.2 := fun h => hrs h.symm
    have hpair : r ≠ s := fun h => hrs (congrArg Prod.snd h)
    rw [Finset.sum_eq_zero]
    · rw [Matrix.one_apply]
      simp [hpair]
    · intro x _
      rw [Finset.sum_eq_zero]
      intro y _
      by_cases hyr : r.2 = y
      · have hsy : ¬s.2 = y := fun h => hrs (hyr.trans h.symm)
        unfold diagonalScalarDilationOp
        rw [Matrix.star_apply]
        rw [Matrix.of_apply, Matrix.of_apply, if_pos hyr, if_neg hsy,
          star_zero, mul_zero]
      · unfold diagonalScalarDilationOp
        rw [Matrix.of_apply, if_neg hyr, zero_mul]

/-- Reindexing both axes by one equivalence preserves unitarity. -/
theorem reindex_mem_unitaryGroup {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, hM, Matrix.submatrix_one_equiv]

/-- The direct-sum scalar dilation reindexed to the `(1+n)`-qubit basis. -/
def diagonalScalarDilationQubitOp {n : Nat}
    (p : Fin (2 ^ n) → ℂ) : HilbertOperator (Qubits (1 + n)) :=
  Matrix.reindex (prodEquiv (m := 1) (n := n))
    (prodEquiv (m := 1) (n := n)) (diagonalScalarDilationOp p)

theorem diagonalScalarDilationQubitOp_mem_unitaryGroup {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    diagonalScalarDilationQubitOp p ∈
      Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  reindex_mem_unitaryGroup (prodEquiv (m := 1) (n := n))
    (diagonalScalarDilationOp p) (diagonalScalarDilationOp_mem_unitaryGroup p hp)

/-- Certified direct sum of scalar dilations under pointwise contraction. -/
def diagonalScalarDilationOperator {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    UnitaryOperator (Qubits (1 + n)) :=
  UnitaryOperator.ofMatrix (diagonalScalarDilationQubitOp p)
    (diagonalScalarDilationQubitOp_mem_unitaryGroup p hp)

/-- The top-left block of the qubit-indexed direct sum is diagonal. -/
theorem diagonalScalarDilationOperator_projectedBlock {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    projectedBlock 1 n
        (diagonalScalarDilationOperator p hp :
          HilbertOperator (Qubits (1 + n))) =
      Matrix.diagonal p := by
  ext i j
  unfold projectedBlock diagonalScalarDilationOperator
    diagonalScalarDilationQubitOp
  simp [diagonalScalarDilationOp, Matrix.diagonal]

theorem diagonalScalarDilationOperator_exactBlockEncoding {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    ExactBlockEncoding 1 n
      (diagonalScalarDilationOperator p hp) (Matrix.diagonal p) := by
  constructor
  intro i j
  rw [diagonalScalarDilationOperator_projectedBlock]

/-- Reassociate the phase ancilla plus an `m`-qubit block ancilla and an
`n`-qubit system from `1 + (m+n)` to `(1+m)+n`. -/
def phaseAncillaAssocEquiv (m n : Nat) :
    Fin (2 ^ (1 + (m + n))) ≃ Fin (2 ^ ((1 + m) + n)) :=
  finCongr (by rw [← Nat.add_assoc])

/-- Reindex a unitary from the nested phase/source layout to the standard
block-encoding layout. -/
def reassociatePhaseAncillaOperator {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) :
    UnitaryOperator (Qubits ((1 + m) + n)) :=
  UnitaryOperator.ofMatrix
    (Matrix.reindex (phaseAncillaAssocEquiv m n) (phaseAncillaAssocEquiv m n)
      (V : HilbertOperator (Qubits (1 + (m + n)))))
    (reindex_mem_unitaryGroup (phaseAncillaAssocEquiv m n)
      (V : HilbertOperator (Qubits (1 + (m + n)))) V.property)

/-- Dilation of a scalar system operator while retaining `m` source
ancillas in the intrinsic block-encoding carrier. -/
def scalarDilationWithSourceAncillas {m n : Nat}
    (c : ℂ) (hc : Complex.normSq c ≤ 1) :
    UnitaryOperator (Qubits ((1 + m) + n)) :=
  reassociatePhaseAncillaOperator (m := m) (n := n)
    (diagonalScalarDilationOperator (n := m + n) (fun _ => c) (fun _ => hc))

/-! ## Scalar-dilation declaration -/

/-- Stable gate coordinate for the closed scalar-dilation branch. -/
def qsvtScalarDilationLabel : Resource.GateLabel :=
  .declared "qsvt" "qsvt-scalar-dilation"



/-- Literal strict event for one closed scalar-dilation branch. -/
def qsvtScalarDilationEvent : Resource.Event .quantum :=
  .gate qsvtScalarDilationLabel



/-- The certified closed scalar-dilation operator family. -/
def qsvtScalarDilationOp {m n : Nat} (c : ℂ)
    (hc : Complex.normSq c ≤ 1) :
    UnitaryOperator (Qubits ((1 + m) + n)) :=
  UnitaryOperator.ofMatrix
    (Matrix.reindex (phaseAncillaAssocEquiv m n) (phaseAncillaAssocEquiv m n)
      (diagonalScalarDilationOperator (n := m + n)
        (fun _ => c) (fun _ => hc) :
          HilbertOperator (Qubits (1 + (m + n)))))
    (reindex_mem_unitaryGroup (phaseAncillaAssocEquiv m n)
      (diagonalScalarDilationOperator (n := m + n)
        (fun _ => c) (fun _ => hc) :
          HilbertOperator (Qubits (1 + (m + n))))
      (diagonalScalarDilationOperator (n := m + n)
        (fun _ => c) (fun _ => hc)).property)

/-- A closed scalar dilation at a caller-supplied physical placement. -/
def qsvtScalarDilationLeafAt {m n : Nat} (c : ℂ)
    (hc : Complex.normSq c ≤ 1)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits ((1 + m) + n)) :=
  UnitaryLeaf.gate qsvtScalarDilationLabel systemIdx
    (qsvtScalarDilationOp (m := m) (n := n) c hc)

end

end QSVT

end QSP.MultiQubit

end QuantumAlg

end

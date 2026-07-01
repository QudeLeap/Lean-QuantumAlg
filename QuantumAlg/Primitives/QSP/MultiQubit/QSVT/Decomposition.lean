/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Pair

/-!
# Projected QSVT circuits

Alternating phase modulation, projected-QSVT circuit witnesses, and same-circuit
resource accounting.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT

/-! ### Alternating phase modulation words -/

/-- Lift a signal gate to the phase-ancilla plus signal space used in
alternating phase modulation. -/
def liftSignalGate {N : Nat} (U : Gate (Qubits N)) : Gate (Qubits (1 + N)) :=
  Gate.tensor (1 : Gate (Qubits 1)) U

/-- Controlled direct sum over the phase ancilla: on the `|0⟩` branch it applies
`V0`, and on the `|1⟩` branch it applies `V1`.  This elementary gate is the
linear-algebraic carrier for the real-polynomial controlled construction in
[GSLW19, BlockHam.tex:851-887]. -/
noncomputable def phaseControlledDirectSum {N : Nat}
    (V0 V1 : Gate (Qubits N)) : Gate (Qubits (1 + N)) :=
  Gate.controlled (V1 * V0.conjTranspose) * Gate.tensor (1 : Gate (Qubits 1)) V0

/-- Matrix decomposition of `phaseControlledDirectSum`. -/
theorem phaseControlledDirectSum_eq_tensor_decomp {N : Nat}
    (V0 V1 : Gate (Qubits N)) :
    (phaseControlledDirectSum V0 V1 : HilbertOperator (Qubits (1 + N))) =
      HilbertOperator.tensor Gate.proj0 (V0 : HilbertOperator (Qubits N)) +
        HilbertOperator.tensor Gate.proj1 (V1 : HilbertOperator (Qubits N)) := by
  have hV0 :
      (V0 : HilbertOperator (Qubits N)).conjTranspose *
          (V0 : HilbertOperator (Qubits N)) =
        1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp V0.unitary
  have htail :
      (((V1 * V0.conjTranspose : Gate (Qubits N)) : HilbertOperator (Qubits N)) *
          (V0 : HilbertOperator (Qubits N))) =
        (V1 : HilbertOperator (Qubits N)) := by
    calc
      (((V1 * V0.conjTranspose : Gate (Qubits N)) : HilbertOperator (Qubits N)) *
          (V0 : HilbertOperator (Qubits N))) =
          ((V1 : HilbertOperator (Qubits N)) *
            (V0 : HilbertOperator (Qubits N)).conjTranspose) *
              (V0 : HilbertOperator (Qubits N)) := rfl
      _ = (V1 : HilbertOperator (Qubits N)) *
            ((V0 : HilbertOperator (Qubits N)).conjTranspose *
              (V0 : HilbertOperator (Qubits N))) := by
          rw [Matrix.mul_assoc]
      _ = (V1 : HilbertOperator (Qubits N)) := by
          rw [hV0, Matrix.mul_one]
  change Gate.controlledOp (V1 * V0.conjTranspose) *
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
        (V0 : HilbertOperator (Qubits N)) =
      HilbertOperator.tensor Gate.proj0 (V0 : HilbertOperator (Qubits N)) +
        HilbertOperator.tensor Gate.proj1 (V1 : HilbertOperator (Qubits N))
  rw [Gate.controlledOp, Matrix.add_mul,
    HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
    Matrix.one_mul, htail]
  simp

/-- The `|+⟩` block of a controlled direct sum is the arithmetic average of its
two branches.  This is the elementary controlled-sum calculation used by the
real-polynomial projected-QSVT corollary [GSLW19, BlockHam.tex:851-887]. -/
theorem phasePlusBlock_phaseControlledDirectSum {N : Nat}
    (V0 V1 : Gate (Qubits N)) :
    phasePlusBlock (phaseControlledDirectSum V0 V1) =
      ((1 / 2 : ℂ) • (V0 : HilbertOperator (Qubits N)) +
        (1 / 2 : ℂ) • (V1 : HilbertOperator (Qubits N))) := by
  ext i j
  rw [phasePlusBlock]
  rw [phaseControlledDirectSum_eq_tensor_decomp]
  simp only [HilbertOperator.tensor_apply, Gate.proj0, Gate.proj1,
    Nat.reducePow, PureState.ketPlus_apply, Matrix.add_apply,
    Equiv.symm_apply_apply, Fin.sum_univ_two, Fin.isValue, one_div,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.smul_apply, smul_eq_mul, one_mul, zero_mul, add_zero, zero_add]
  have hstar : (starRingEnd ℂ) PureState.invSqrt2 = PureState.invSqrt2 :=
    PureState.star_invSqrt2
  rw [hstar]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [show PureState.invSqrt2 * (V0 : HilbertOperator (Qubits N)) i j *
        PureState.invSqrt2 = (2 : ℂ)⁻¹ * (V0 : HilbertOperator (Qubits N)) i j by
      rw [mul_assoc, PureState.invSqrt2_mul_mul_invSqrt2]]
  rw [show PureState.invSqrt2 * (V1 : HilbertOperator (Qubits N)) i j *
        PureState.invSqrt2 = (2 : ℂ)⁻¹ * (V1 : HilbertOperator (Qubits N)) i j by
      rw [mul_assoc, PureState.invSqrt2_mul_mul_invSqrt2]]

/-- Hadamard-wrapped controlled direct sums average the top-left projected
blocks of two branches.  This is the circuit-level linear-combination gadget
used when the arbitrary-parity Hermitian QSVT theorem combines real-polynomial
branches [GSLW19, BlockHam.tex:1948-1952]. -/
noncomputable def averageProjectedBlockGate {a n : Nat}
    (V0 V1 : Gate (Qubits (a + n))) : Gate (Qubits ((1 + a) + n)) :=
  reassociatePhaseAncillaGate (m := a) (n := n)
    (phaseHadamardWrapper (phaseControlledDirectSum V0 V1))

/-- The projected block of `averageProjectedBlockGate` is the arithmetic
average of the projected blocks of its two branches. -/
theorem projectedBlock_averageProjectedBlockGate {a n : Nat}
    (V0 V1 : Gate (Qubits (a + n))) :
    projectedBlock (1 + a) n
        (averageProjectedBlockGate (a := a) (n := n) V0 V1 :
          HilbertOperator (Qubits ((1 + a) + n))) =
      (1 / 2 : ℂ) • projectedBlock a n (V0 : HilbertOperator (Qubits (a + n))) +
        (1 / 2 : ℂ) • projectedBlock a n (V1 : HilbertOperator (Qubits (a + n))) := by
  unfold averageProjectedBlockGate
  rw [projectedBlock_reassociatedPhaseHadamardWrapper,
    phasePlusBlock_phaseControlledDirectSum]
  ext i j
  simp [projectedBlock, Matrix.add_apply, Matrix.smul_apply]

/-- Averaging two exact block encodings yields an exact block encoding of the
averaged target, with the averaging ancilla accounted for in the carrier. -/
theorem exactBlockEncoding_averageProjectedBlockGate {a n : Nat}
    {V0 V1 : Gate (Qubits (a + n))}
    {A0 A1 : HilbertOperator (Qubits n)}
    (h0 : ExactBlockEncoding a n V0 A0) (h1 : ExactBlockEncoding a n V1 A1) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockGate (a := a) (n := n) V0 V1)
      ((1 / 2 : ℂ) • A0 + (1 / 2 : ℂ) • A1) := by
  constructor
  intro i j
  have hblock := projectedBlock_averageProjectedBlockGate (a := a) (n := n) V0 V1
  have hentry := congrFun (congrFun hblock i) j
  have h0block := h0.projected_block_eq
  have h1block := h1.projected_block_eq
  simpa [h0block, h1block, Matrix.add_apply, Matrix.smul_apply] using hentry

/-- Average four block encodings with two selector ancillas. This internal
bookkeeping gadget is useful for auditing the four real/imaginary even/odd
branches in the arbitrary-parity QSVT note [GSLW19, BlockHam.tex:1936-1952]. -/
noncomputable def fourWayAverageProjectedBlockGate {a n : Nat}
    (V00 V01 V10 V11 : Gate (Qubits (a + n))) :
    Gate (Qubits ((1 + (1 + a)) + n)) :=
  averageProjectedBlockGate (a := 1 + a) (n := n)
    (averageProjectedBlockGate (a := a) (n := n) V00 V01)
    (averageProjectedBlockGate (a := a) (n := n) V10 V11)

/-- The projected block of `fourWayAverageProjectedBlockGate` is the arithmetic
mean of the four branch projected blocks. -/
theorem projectedBlock_fourWayAverageProjectedBlockGate {a n : Nat}
    (V00 V01 V10 V11 : Gate (Qubits (a + n))) :
    projectedBlock (1 + (1 + a)) n
        (fourWayAverageProjectedBlockGate (a := a) (n := n) V00 V01 V10 V11 :
          HilbertOperator (Qubits ((1 + (1 + a)) + n))) =
      (1 / 4 : ℂ) • projectedBlock a n (V00 : HilbertOperator (Qubits (a + n))) +
        (1 / 4 : ℂ) • projectedBlock a n (V01 : HilbertOperator (Qubits (a + n))) +
      ((1 / 4 : ℂ) • projectedBlock a n (V10 : HilbertOperator (Qubits (a + n))) +
        (1 / 4 : ℂ) • projectedBlock a n (V11 : HilbertOperator (Qubits (a + n)))) := by
  unfold fourWayAverageProjectedBlockGate
  rw [projectedBlock_averageProjectedBlockGate,
    projectedBlock_averageProjectedBlockGate,
    projectedBlock_averageProjectedBlockGate]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- Averaging four exact block encodings yields an exact block encoding of the
four-way averaged target, with both selector ancillas accounted for. -/
theorem exactBlockEncoding_fourWayAverageProjectedBlockGate {a n : Nat}
    {V00 V01 V10 V11 : Gate (Qubits (a + n))}
    {A00 A01 A10 A11 : HilbertOperator (Qubits n)}
    (h00 : ExactBlockEncoding a n V00 A00)
    (h01 : ExactBlockEncoding a n V01 A01)
    (h10 : ExactBlockEncoding a n V10 A10)
    (h11 : ExactBlockEncoding a n V11 A11) :
    ExactBlockEncoding (1 + (1 + a)) n
      (fourWayAverageProjectedBlockGate (a := a) (n := n) V00 V01 V10 V11)
      ((1 / 4 : ℂ) • A00 + (1 / 4 : ℂ) • A01 +
        ((1 / 4 : ℂ) • A10 + (1 / 4 : ℂ) • A11)) := by
  constructor
  intro i j
  have hblock :=
    projectedBlock_fourWayAverageProjectedBlockGate (a := a) (n := n)
      V00 V01 V10 V11
  have hentry := congrFun (congrFun hblock i) j
  have h00block := h00.projected_block_eq
  have h01block := h01.projected_block_eq
  have h10block := h10.projected_block_eq
  have h11block := h11.projected_block_eq
  simpa [h00block, h01block, h10block, h11block, Matrix.add_apply,
    Matrix.smul_apply] using hentry

/-- Multiply a gate by a global phase.  This keeps the same mathematical
carrier circuit while scaling every projected block by the same phase. -/
noncomputable def phaseScaledGate {R : Register} (ζ : ℂ) (hζ : Complex.normSq ζ = 1)
    (V : Gate R) : Gate R :=
  Gate.ofUnitary (ζ • (V : HilbertOperator R)) (by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm]
    have hphase : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj]
      exact_mod_cast hζ
    have hphase' : ζ * star ζ = 1 := by
      simpa using hphase
    rw [hphase', one_smul]
    exact Matrix.mem_unitaryGroup_iff.mp V.unitary)

@[simp]
theorem phaseScaledGate_coe {R : Register} (ζ : ℂ) (hζ : Complex.normSq ζ = 1)
    (V : Gate R) :
    ((phaseScaledGate ζ hζ V : Gate R) : HilbertOperator R) =
      ζ • (V : HilbertOperator R) := rfl

/-- Global phase scaling of a carrier scales the encoded target by the same
phase. -/
theorem exactBlockEncoding_phaseScaledGate {a n : Nat} {V : Gate (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (ζ : ℂ) (hζ : Complex.normSq ζ = 1)
    (h : ExactBlockEncoding a n V A) :
    ExactBlockEncoding a n (phaseScaledGate ζ hζ V) (ζ • A) := by
  constructor
  intro i j
  simp [projectedBlock, Matrix.smul_apply, h.block_entry i j]

/-- Dilation of a scalar system operator, with `m` source ancillas retained in
the block-encoding carrier.  This is used for constant branches in the
arbitrary-parity split. -/
noncomputable def scalarDilationWithSourceAncillas {m n : Nat}
    (c : ℂ) (hc : Complex.normSq c ≤ 1) : Gate (Qubits ((1 + m) + n)) :=
  reassociatePhaseAncillaGate (m := m) (n := n)
    (diagonalScalarDilationGate (n := m + n) (fun _ => c) (fun _ => hc))

/-- The scalar dilation with retained source ancillas exactly block-encodes
`c • I` on the system register. -/
theorem exactBlockEncoding_scalarDilationWithSourceAncillas {m n : Nat}
    (c : ℂ) (hc : Complex.normSq c ≤ 1) :
    ExactBlockEncoding (1 + m) n
      (scalarDilationWithSourceAncillas (m := m) (n := n) c hc)
      (c • (1 : HilbertOperator (Qubits n))) := by
  constructor
  intro i j
  unfold scalarDilationWithSourceAncillas
  rw [show
      projectedBlock (1 + m) n
          (reassociatePhaseAncillaGate (m := m) (n := n)
            (diagonalScalarDilationGate (n := m + n) (fun _ => c) (fun _ => hc)) :
            HilbertOperator (Qubits ((1 + m) + n))) =
        projectedBlock m n
          (ancillaBlock 0 0
            (diagonalScalarDilationGate (n := m + n) (fun _ => c) (fun _ => hc))) by
      rw [projectedBlock_reassociatePhaseAncillaGate]]
  unfold projectedBlock ancillaBlock diagonalScalarDilationGate
    diagonalScalarDilationQubitOp diagonalScalarDilationOp
  simp [Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Constant polynomial branch, encoded with one dilation ancilla while
retaining the source ancillas in the carrier. -/
theorem exactBlockEncoding_constantPolynomialWithSourceAncillas {m n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    (hdeg : P.natDegree = 0) (hcontract : Complex.normSq (P.coeff 0) ≤ 1) :
    ExactBlockEncoding (1 + m) n
      (scalarDilationWithSourceAncillas (m := m) (n := n) (P.coeff 0) hcontract)
      (polynomialOperator P A) := by
  have hscalar :=
    exactBlockEncoding_scalarDilationWithSourceAncillas
      (m := m) (n := n) (P.coeff 0) hcontract
  have htarget :=
    polynomialOperator_eq_scalar_one_of_natDegree_eq_zero P A hdeg
  constructor
  intro i j
  exact (hscalar.block_entry i j).trans (congrFun (congrFun htarget.symm i) j)

theorem complex_normSq_I : Complex.normSq Complex.I = 1 := by
  simp [Complex.normSq]

/-- Four branch encodings for the real/imaginary and even/odd pieces of `P`
combine into a normalization-four encoding of `P(A)`.  This is the block
encoding form of the source's complex-polynomial note following
`thm:arbParity` [GSLW19, BlockHam.tex:1936-1952]. -/
theorem exactBlockEncoding_complexFourPartAverageProjectedBlockGate {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    {VReEven VReOdd VImEven VImOdd : Gate (Qubits (a + n))}
    (hReEven : ExactBlockEncoding a n VReEven
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A))
    (hReOdd : ExactBlockEncoding a n VReOdd
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A))
    (hImEven : ExactBlockEncoding a n VImEven
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialImagPart P))) A))
    (hImOdd : ExactBlockEncoding a n VImOdd
      (polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialImagPart P))) A)) :
    ExactBlockEncoding (1 + (1 + a)) n
      (fourWayAverageProjectedBlockGate (a := a) (n := n)
        VReEven VReOdd
        (phaseScaledGate Complex.I complex_normSq_I VImEven)
        (phaseScaledGate Complex.I complex_normSq_I VImOdd))
      ((1 / 4 : ℂ) • polynomialOperator P A) := by
  have hImEvenScaled :
      ExactBlockEncoding a n
        (phaseScaledGate Complex.I complex_normSq_I VImEven)
        (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) := by
    exact exactBlockEncoding_phaseScaledGate Complex.I complex_normSq_I hImEven
  have hImOddScaled :
      ExactBlockEncoding a n
        (phaseScaledGate Complex.I complex_normSq_I VImOdd)
        (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) := by
    exact exactBlockEncoding_phaseScaledGate Complex.I complex_normSq_I hImOdd
  have hAvg :=
    exactBlockEncoding_fourWayAverageProjectedBlockGate
      (a := a) (n := n) hReEven hReOdd hImEvenScaled hImOddScaled
  have htarget :
      (1 / 4 : ℂ) • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
        (1 / 4 : ℂ) • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialRealPart P))) A +
        ((1 / 4 : ℂ) • Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
          (1 / 4 : ℂ) • Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) =
        (1 / 4 : ℂ) • polynomialOperator P A := by
    simpa [smul_smul] using polynomialOperator_complex_fourPart_average_recompose P A
  constructor
  intro i j
  exact (hAvg.block_entry i j).trans (congrFun (congrFun htarget i) j)

/-- If two branches encode the doubled even and odd parts of a real polynomial,
their selector average encodes the original polynomial.  This is the
block-encoding form of the real arbitrary-parity split in `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem exactBlockEncoding_realEvenOddDoubleAverageProjectedBlockGate {a n : Nat}
    (PRe : Polynomial ℝ) (A : HilbertOperator (Qubits n))
    {VEven VOdd : Gate (Qubits (a + n))}
    (hEven : ExactBlockEncoding a n VEven
      (polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialEvenPart PRe)) A))
    (hOdd : ExactBlockEncoding a n VOdd
      (polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialOddPart PRe)) A)) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockGate (a := a) (n := n) VEven VOdd)
      (polynomialOperator (realPolynomialToComplex PRe) A) := by
  have hAvg :=
    exactBlockEncoding_averageProjectedBlockGate (a := a) (n := n) hEven hOdd
  have htarget :=
    polynomialOperator_real_evenOdd_double_average_recompose PRe A
  constructor
  intro i j
  exact (hAvg.block_entry i j).trans (congrFun (congrFun htarget i) j)

/-- If two branches encode the doubled even and odd complex coefficient parts,
their selector average encodes the original complex polynomial.  This is the
two-branch interface needed for the source-style complex arbitrary-parity QSVT
construction without adding a third selector ancilla. -/
theorem exactBlockEncoding_complexEvenOddDoubleAverageProjectedBlockGate {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    {VEven VOdd : Gate (Qubits (a + n))}
    (hEven : ExactBlockEncoding a n VEven
      (polynomialOperator ((2 : ℂ) • complexPolynomialEvenPart P) A))
    (hOdd : ExactBlockEncoding a n VOdd
      (polynomialOperator ((2 : ℂ) • complexPolynomialOddPart P) A)) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockGate (a := a) (n := n) VEven VOdd)
      (polynomialOperator P A) := by
  have hAvg :=
    exactBlockEncoding_averageProjectedBlockGate (a := a) (n := n) hEven hOdd
  have htarget :=
    polynomialOperator_complex_evenOdd_double_average_recompose P A
  constructor
  intro i j
  exact (hAvg.block_entry i j).trans (congrFun (congrFun htarget i) j)

@[simp]
theorem ancillaBlock_tensor {N : Nat} (a b : Fin (2 ^ 1))
    (G : Gate (Qubits 1)) (K : Gate (Qubits N)) :
    ancillaBlock a b (Gate.tensor G K) =
      G a b • (K : HilbertOperator (Qubits N)) := by
  ext i j
  simp [ancillaBlock, Gate.tensor_apply, smul_eq_mul]

@[simp]
theorem ancillaBlock_liftSignalGate {N : Nat} (a b : Fin (2 ^ 1))
    (U : Gate (Qubits N)) :
    ancillaBlock a b (liftSignalGate U) =
      (if a = b then (U : HilbertOperator (Qubits N)) else 0) := by
  ext i j
  by_cases h : a = b <;>
    simp [liftSignalGate, ancillaBlock_tensor, h]

@[simp]
theorem phasePlusBlock_liftSignalGate {N : Nat} (U : Gate (Qubits N)) :
    phasePlusBlock (liftSignalGate U) = (U : HilbertOperator (Qubits N)) := by
  rw [phasePlusBlock_eq_sum_ancillaBlock]
  ext i j
  simp only [Nat.reducePow, PureState.ketPlus_apply, ancillaBlock_liftSignalGate, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  have hstar : (starRingEnd ℂ) PureState.invSqrt2 = PureState.invSqrt2 := by
    exact PureState.star_invSqrt2
  rw [hstar]
  change 2 * (PureState.invSqrt2 *
      (PureState.invSqrt2 * ((U : HilbertOperator (Qubits N)) i j))) =
    (U : HilbertOperator (Qubits N)) i j
  calc
    2 * (PureState.invSqrt2 *
        (PureState.invSqrt2 * ((U : HilbertOperator (Qubits N)) i j))) =
        (2 * (PureState.invSqrt2 * PureState.invSqrt2)) *
          ((U : HilbertOperator (Qubits N)) i j) := by
      ring
    _ = (U : HilbertOperator (Qubits N)) i j := by
      rw [PureState.invSqrt2_mul_self]
      ring

@[simp]
theorem projectedPhasePlusBlock_liftSignalGate {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    projectedPhasePlusBlock left right (liftSignalGate U) =
      projectedUnitaryBlock left right U := by
  simp [projectedPhasePlusBlock, projectedUnitaryBlock]

/-- One projector-controlled phase block, implemented by the source's
`C_P NOT (R_Z(phi) ⊗ I) C_P NOT` pattern. -/
noncomputable def projectorPhaseGate {N : Nat} (phi : ℝ) (P : OrthogonalProjector N) :
    Gate (Qubits (1 + N)) :=
  OrthogonalProjector.controlledNot P
    * Gate.tensor (rotZStd phi) (1 : Gate (Qubits N))
    * OrthogonalProjector.controlledNot P

@[simp]
theorem X_mul_rotZStd_mul_X (phi : ℝ) :
    Gate.X * rotZStd phi * Gate.X = rotZStd (-phi) := by
  ext i j
  change ((Gate.X : HilbertOperator (Qubits 1)) *
      (rotZStd phi : HilbertOperator (Qubits 1)) *
      (Gate.X : HilbertOperator (Qubits 1))) i j =
    (rotZStd (-phi) : HilbertOperator (Qubits 1)) i j
  fin_cases i <;> fin_cases j <;>
    simp [Gate.X, Gate.ofPerm, rotZStd, rotZ, rotZOp, Matrix.mul_apply] <;>
    congr 1 <;> ring

@[simp]
theorem X_mul_rotZStd_mul_X_op (phi : ℝ) :
    (Gate.X : HilbertOperator (Qubits 1)) *
        ((rotZStd phi : Gate (Qubits 1)) : HilbertOperator (Qubits 1)) *
        (Gate.X : HilbertOperator (Qubits 1)) =
      ((rotZStd (-phi) : Gate (Qubits 1)) : HilbertOperator (Qubits 1)) := by
  change ((Gate.X * rotZStd phi * Gate.X : Gate (Qubits 1)) :
      HilbertOperator (Qubits 1)) =
    ((rotZStd (-phi) : Gate (Qubits 1)) : HilbertOperator (Qubits 1))
  rw [X_mul_rotZStd_mul_X]

@[simp]
theorem X_mul_rotZStd_mul_X_op_assoc (phi : ℝ) :
    (Gate.X : HilbertOperator (Qubits 1)) *
        (((rotZStd phi : Gate (Qubits 1)) : HilbertOperator (Qubits 1)) *
          (Gate.X : HilbertOperator (Qubits 1))) =
      ((rotZStd (-phi) : Gate (Qubits 1)) : HilbertOperator (Qubits 1)) := by
  rw [← Matrix.mul_assoc, X_mul_rotZStd_mul_X_op]

/-- Matrix decomposition of the projector-controlled phase gadget.  On the
projector branch it conjugates the ancilla `rotZStd` by `X`, and on the
complement branch it leaves the ancilla rotation unchanged.  This is the
gate-level semantic content of the source implementation
`C_P NOT (R_Z(phi) ⊗ I) C_P NOT` [GSLW19, BlockHam.tex:883-887]. -/
theorem projectorPhaseGate_eq_tensor_decomp {N : Nat}
    (phi : ℝ) (P : OrthogonalProjector N) :
    (projectorPhaseGate phi P : HilbertOperator (Qubits (1 + N))) =
      HilbertOperator.tensor (rotZStd (-phi) : HilbertOperator (Qubits 1)) P.op +
        HilbertOperator.tensor (rotZStd phi : HilbertOperator (Qubits 1))
          (OrthogonalProjector.complement P) := by
  change OrthogonalProjector.controlledNotOp P *
      HilbertOperator.tensor (rotZStd phi : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits N)) *
      OrthogonalProjector.controlledNotOp P =
      HilbertOperator.tensor (rotZStd (-phi) : HilbertOperator (Qubits 1)) P.op +
        HilbertOperator.tensor (rotZStd phi : HilbertOperator (Qubits 1))
          (OrthogonalProjector.complement P)
  rw [OrthogonalProjector.controlledNotOp]
  rw [Matrix.add_mul]
  rw [Matrix.mul_add]
  rw [Matrix.add_mul, Matrix.add_mul]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  rw [X_mul_rotZStd_mul_X_op]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [P.idempotent,
    OrthogonalProjector.complement_mul P, OrthogonalProjector.mul_complement P,
    OrthogonalProjector.complement_sq P]
  simp [HilbertOperator.tensor_zero]

@[simp]
theorem projectorPhaseGate_zero {N : Nat} (P : OrthogonalProjector N) :
    projectorPhaseGate 0 P = 1 := by
  apply Gate.ext
  intro i j
  change (projectorPhaseGate 0 P : HilbertOperator (Qubits (1 + N))) i j =
    (1 : HilbertOperator (Qubits (1 + N))) i j
  rw [show (projectorPhaseGate 0 P : HilbertOperator (Qubits (1 + N))) =
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1)) P.op +
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          (OrthogonalProjector.complement P) by
    simpa using projectorPhaseGate_eq_tensor_decomp (N := N) 0 P]
  rw [← HilbertOperator.tensor_add]
  have hsum : P.op + OrthogonalProjector.complement P =
      (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  rw [hsum, HilbertOperator.one_tensor_one]

@[simp]
theorem ancillaBlock_projectorPhaseGate {N : Nat} (a b : Fin (2 ^ 1))
    (phi : ℝ) (P : OrthogonalProjector N) :
    ancillaBlock a b (projectorPhaseGate phi P) =
      ((rotZStd (-phi) : Gate (Qubits 1)) a b) • P.op +
        ((rotZStd phi : Gate (Qubits 1)) a b) • OrthogonalProjector.complement P := by
  ext i j
  change (projectorPhaseGate phi P : HilbertOperator (Qubits (1 + N)))
      (prodEquiv (a, i)) (prodEquiv (b, j)) =
    (((rotZStd (-phi) : Gate (Qubits 1)) a b) • P.op +
      ((rotZStd phi : Gate (Qubits 1)) a b) • OrthogonalProjector.complement P) i j
  rw [show (projectorPhaseGate phi P : HilbertOperator (Qubits (1 + N))) =
      HilbertOperator.tensor (rotZStd (-phi) : HilbertOperator (Qubits 1)) P.op +
        HilbertOperator.tensor (rotZStd phi : HilbertOperator (Qubits 1))
          (OrthogonalProjector.complement P) by
    exact projectorPhaseGate_eq_tensor_decomp phi P]
  simp [HilbertOperator.tensor_apply, smul_eq_mul]

/-- Select the alternating projector used at slot `k`. -/
def alternatingProjector {N : Nat} (left right : OrthogonalProjector N) (k : ℕ) :
    OrthogonalProjector N :=
  if k % 2 = 0 then left else right

/-- The parity-selected output projector `Π_L` in the projected-QSVT statement
[GSLW19, BlockHam.tex:883-887].  We use `left = \widetilde Π` and
`right = Π`, so odd `L` selects `left` and even `L` selects `right`. -/
def projectedOutputProjector {N : Nat} (left right : OrthogonalProjector N) (L : ℕ) :
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

/-- Gate-level alternating phase modulation word over a projected-unitary
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
def sourcePhaseSignal {N : Nat} (U : Gate (Qubits N)) (remaining : ℕ) :
    Gate (Qubits N) :=
  if remaining % 2 = 0 then U.conjTranspose else U

/-- Lift the source-aligned signal oracle for one projected-QSVT phase slot. -/
def liftSourcePhaseSignal {N : Nat} (U : Gate (Qubits N)) (remaining : ℕ) :
    Gate (Qubits (1 + N)) :=
  liftSignalGate (sourcePhaseSignal U remaining)

/-! ### Source-level alternating phase modulation on the signal space -/

/-- The source projector phase `e^{iφ(2P-I)}` on the signal space, written using
the projector/complement decomposition.  The projector-controlled-NOT gadget
below is an implementation of this signal-space unitary, not the mathematical
definition of `U_Φ` itself [GSLW19, BlockHam.tex:738-745,883-887]. -/
noncomputable def projectorPhaseOp {N : Nat} (phi : ℝ) (P : OrthogonalProjector N) :
    HilbertOperator (Qubits N) :=
  Complex.exp (phi * Complex.I) • P.op +
    Complex.exp (-(phi * Complex.I)) • OrthogonalProjector.complement P

theorem projectorPhaseOp_conjTranspose {N : Nat} (phi : ℝ) (P : OrthogonalProjector N) :
    (projectorPhaseOp phi P).conjTranspose =
      Complex.exp (-(phi * Complex.I)) • P.op +
        Complex.exp (phi * Complex.I) • OrthogonalProjector.complement P := by
  rw [projectorPhaseOp, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, P.selfAdjoint,
    OrthogonalProjector.complement_conjTranspose]
  simp [conj_exp_I, conj_exp_neg_I]

theorem projectorPhaseOp_mem_unitaryGroup {N : Nat} (phi : ℝ)
    (P : OrthogonalProjector N) :
    projectorPhaseOp phi P ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    projectorPhaseOp_conjTranspose]
  rw [projectorPhaseOp, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [P.idempotent, OrthogonalProjector.mul_complement,
    OrthogonalProjector.complement_mul, OrthogonalProjector.complement_sq]
  simp only [exp_neg_I_mul_exp_I, one_smul, smul_zero, add_zero,
    exp_I_mul_exp_neg_I, zero_add]
  have hsum : P.op + OrthogonalProjector.complement P = (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  exact hsum

/-- On the projector image, the source projector phase acts by `e^{i phi}`.
This is the one-dimensional block of the phase operators in `lemma:singInvDec`
[GSLW19, BlockHam.tex:672-714]. -/
theorem projectorPhaseOp_applyVec_of_projector_applyVec_eq_self {N : Nat}
    (phi : ℝ) (P : OrthogonalProjector N) {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec P.op psi = psi) :
    HilbertOperator.applyVec (projectorPhaseOp phi P) psi =
      Complex.exp (phi * Complex.I) • psi := by
  rw [projectorPhaseOp, HilbertOperator.add_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.smul_applyVec, hpsi,
    OrthogonalProjector.complement_applyVec_eq_zero_of_projector_applyVec_eq_self P hpsi]
  simp

/-- On the projector complement, the source projector phase acts by `e^{-i phi}`.
This is the complementary block of the phase operators in `lemma:singInvDec`
[GSLW19, BlockHam.tex:672-714]. -/
theorem projectorPhaseOp_applyVec_of_complement_applyVec_eq_self {N : Nat}
    (phi : ℝ) (P : OrthogonalProjector N) {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement P) psi = psi) :
    HilbertOperator.applyVec (projectorPhaseOp phi P) psi =
      Complex.exp (-(phi * Complex.I)) • psi := by
  rw [projectorPhaseOp, HilbertOperator.add_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.smul_applyVec,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self P hpsi,
    hpsi]
  simp

/-- Left-complement vector candidate for the `0 < σ < 1` source sector in
`lemma:singInvDec`.  It is the normalized component of `U |v⟩` outside
`img \widetildeΠ` [GSLW19, BlockHam.tex:655-716]. -/
noncomputable def projectedUnitaryBlockLeftPerpCandidate {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    StateVector (Qubits N) :=
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)⁻¹ •
    HilbertOperator.applyVec (OrthogonalProjector.complement left) (U.applyVec pair.rightVec)

/-- Right-complement vector candidate for the `0 < σ < 1` source sector in
`lemma:singInvDec`.  It is the normalized component of `U† |w⟩` outside
`img Π` [GSLW19, BlockHam.tex:655-716]. -/
noncomputable def projectedUnitaryBlockRightPerpCandidate {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    StateVector (Qubits N) :=
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)⁻¹ •
    HilbertOperator.applyVec (OrthogonalProjector.complement right)
      (U.conjTranspose.applyVec pair.leftVec)

/-- The left-complement candidate is supported on `I - \widetildeΠ`. -/
theorem projectedUnitaryBlockLeftPerpCandidate_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
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
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
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

/-- In the `0 < σ < 1` sector, `U |v⟩` splits into its projected singular
component and normalized left-complement component [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_U_rightVec_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1) :
    U.applyVec (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec =
      ((projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma : ℂ) •
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec +
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).sigma ^ 2) :
          ℝ) : ℂ) •
        projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hproj :
      HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (pair.sigma : ℂ) • pair.leftVec := by
    have hA := pair.A_right
    change HilbertOperator.applyVec
        (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
      (pair.sigma : ℂ) • pair.leftVec at hA
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
      pair.right_support] at hA
    simpa [Gate.applyVec] using hA
  have hgamma_ne :
      ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < 1 - pair.sigma ^ 2 := by
      nlinarith [pair.sigma_pos, hsigma_lt_one]
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hcomp :
      HilbertOperator.applyVec (OrthogonalProjector.complement left) (U.applyVec pair.rightVec) =
        ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) •
          projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
    let gamma : ℂ := ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)
    have hgamma_ne' : gamma ≠ 0 := hgamma_ne
    unfold projectedUnitaryBlockLeftPerpCandidate
    dsimp [pair]
    change
      HilbertOperator.applyVec (OrthogonalProjector.complement left)
        (U.applyVec pair.rightVec) =
      gamma • (gamma⁻¹ •
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
    _ = (pair.sigma : ℂ) • pair.leftVec +
          ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) •
            projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
      rw [hproj, hcomp]

/-- In the `0 < σ < 1` sector, `U† |w⟩` splits into its projected singular
component and normalized right-complement component [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_Udag_leftVec_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1) :
    U.conjTranspose.applyVec
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec =
      ((projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma : ℂ) •
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec +
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).sigma ^ 2) :
          ℝ) : ℂ) •
        projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  have hproj :
      HilbertOperator.applyVec right.op (U.conjTranspose.applyVec pair.leftVec) =
        (pair.sigma : ℂ) • pair.rightVec := by
    have hA := pair.Astar_left
    change HilbertOperator.applyVec
        (Matrix.conjTranspose
          (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
      (pair.sigma : ℂ) • pair.rightVec at hA
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
      HilbertOperator.mul_applyVec, pair.left_support] at hA
    simpa [Gate.applyVec] using hA
  have hgamma_ne :
      ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < 1 - pair.sigma ^ 2 := by
      nlinarith [pair.sigma_pos, hsigma_lt_one]
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hcomp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right)
          (U.conjTranspose.applyVec pair.leftVec) =
        ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) •
          projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
    let gamma : ℂ := ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)
    have hgamma_ne' : gamma ≠ 0 := hgamma_ne
    unfold projectedUnitaryBlockRightPerpCandidate
    dsimp [pair]
    change HilbertOperator.applyVec (OrthogonalProjector.complement right)
        (U.conjTranspose.applyVec pair.leftVec) =
      gamma • (gamma⁻¹ •
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
          (U.conjTranspose.applyVec pair.leftVec))
    rw [smul_smul, mul_inv_cancel₀ hgamma_ne']
    simp
  have hsum : right.op + OrthogonalProjector.complement right =
      (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  calc
    U.conjTranspose.applyVec pair.leftVec =
        HilbertOperator.applyVec (1 : HilbertOperator (Qubits N))
          (U.conjTranspose.applyVec pair.leftVec) := by
      rw [HilbertOperator.one_applyVec]
    _ = HilbertOperator.applyVec (right.op + OrthogonalProjector.complement right)
          (U.conjTranspose.applyVec pair.leftVec) := by
      rw [hsum]
    _ = HilbertOperator.applyVec right.op (U.conjTranspose.applyVec pair.leftVec) +
          HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (U.conjTranspose.applyVec pair.leftVec) := by
      rw [HilbertOperator.add_applyVec]
    _ = (pair.sigma : ℂ) • pair.rightVec +
          ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ) •
            projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
      rw [hproj, hcomp]

/-- In the `0 < σ < 1` sector, `U` maps the right-complement vector to the
second row of the source two-by-two singular block [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_U_rightPerp_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1) :
    U.applyVec (projectedUnitaryBlockRightPerpCandidate left right U i hlambda) =
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).sigma ^ 2) :
          ℝ) : ℂ) •
          (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).leftVec +
        (-(projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma : ℂ) •
          projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  let gamma : ℂ := ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)
  have hgamma_pos : 0 < 1 - pair.sigma ^ 2 := by
    nlinarith [pair.sigma_pos, hsigma_lt_one]
  have hgamma_ne : gamma ≠ 0 := by
    dsimp [gamma]
    exact_mod_cast (Real.sqrt_pos.2 hgamma_pos).ne'
  have hgamma_sq : gamma * gamma = 1 - (pair.sigma : ℂ) ^ 2 := by
    dsimp [gamma]
    have hsqrt_sq :
        Real.sqrt (1 - pair.sigma ^ 2) * Real.sqrt (1 - pair.sigma ^ 2) =
          1 - pair.sigma ^ 2 := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hgamma_pos)]
    rw [← Complex.ofReal_mul, hsqrt_sq]
    norm_num [pow_two]
  have hproj :
      HilbertOperator.applyVec right.op (U.conjTranspose.applyVec pair.leftVec) =
        (pair.sigma : ℂ) • pair.rightVec := by
    have hA := pair.Astar_left
    change HilbertOperator.applyVec
        (Matrix.conjTranspose
          (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
      (pair.sigma : ℂ) • pair.rightVec at hA
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
      HilbertOperator.mul_applyVec, pair.left_support] at hA
    simpa [Gate.applyVec] using hA
  have hrightPerp :
      projectedUnitaryBlockRightPerpCandidate left right U i hlambda =
        gamma⁻¹ •
          (U.conjTranspose.applyVec pair.leftVec -
            (pair.sigma : ℂ) • pair.rightVec) := by
    unfold projectedUnitaryBlockRightPerpCandidate
    dsimp [pair, gamma]
    rw [orthogonalProjector_complement_applyVec, hproj]
    rfl
  have hUright :=
    projectedUnitaryBlock_U_rightVec_decomposition left right U i hlambda hsigma_lt_one
  have hUinv := gate_applyVec_conjTranspose_applyVec U pair.leftVec
  have hscale_left : gamma⁻¹ * (1 - (pair.sigma : ℂ) ^ 2) = gamma := by
    rw [← hgamma_sq]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hscale_perp : gamma⁻¹ * ((pair.sigma : ℂ) * gamma) = (pair.sigma : ℂ) := by
    rw [mul_comm (pair.sigma : ℂ) gamma]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hcoeff_left :
      gamma⁻¹ + -(gamma⁻¹ * ((pair.sigma : ℂ) * (pair.sigma : ℂ))) = gamma := by
    have h := hscale_left
    rw [sub_eq_add_neg, mul_add, mul_one, mul_neg, pow_two] at h
    simpa [mul_assoc] using h
  have hcoeff_perp :
      -(gamma⁻¹ * ((pair.sigma : ℂ) * gamma)) = -(pair.sigma : ℂ) := by
    rw [hscale_perp]
  calc
    U.applyVec (projectedUnitaryBlockRightPerpCandidate left right U i hlambda) =
        U.applyVec (gamma⁻¹ •
          (U.conjTranspose.applyVec pair.leftVec -
            (pair.sigma : ℂ) • pair.rightVec)) := by
      rw [hrightPerp]
    _ = gamma⁻¹ •
          (U.applyVec (U.conjTranspose.applyVec pair.leftVec) -
            (pair.sigma : ℂ) • U.applyVec pair.rightVec) := by
      rw [Gate.applyVec_smul, Gate.applyVec_sub, Gate.applyVec_smul]
    _ = gamma⁻¹ •
          (pair.leftVec -
            (pair.sigma : ℂ) •
              (((pair.sigma : ℂ) • pair.leftVec) +
                gamma • projectedUnitaryBlockLeftPerpCandidate left right U i hlambda)) := by
      rw [hUinv, hUright]
    _ = gamma • pair.leftVec +
          (-(pair.sigma : ℂ)) •
            projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
      calc
        gamma⁻¹ •
            (pair.leftVec -
              (pair.sigma : ℂ) •
                (((pair.sigma : ℂ) • pair.leftVec) +
                  gamma • projectedUnitaryBlockLeftPerpCandidate left right U i hlambda)) =
            (gamma⁻¹ + -(gamma⁻¹ * ((pair.sigma : ℂ) * (pair.sigma : ℂ)))) •
                pair.leftVec +
              (-(gamma⁻¹ * ((pair.sigma : ℂ) * gamma))) •
                projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
          module
        _ = gamma • pair.leftVec +
              (-(pair.sigma : ℂ)) •
                projectedUnitaryBlockLeftPerpCandidate left right U i hlambda := by
          rw [hcoeff_left, hcoeff_perp]

/-- In the `0 < σ < 1` sector, `U†` maps the left-complement vector to the
second column of the source two-by-two singular block [GSLW19,
BlockHam.tex:655-716]. -/
theorem projectedUnitaryBlock_Udag_leftPerp_decomposition {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1) :
    U.conjTranspose.applyVec (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda) =
      ((Real.sqrt
          (1 -
            (projectedUnitaryBlockNonzeroSingularPair
              left right U i hlambda).sigma ^ 2) :
          ℝ) : ℂ) •
          (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).rightVec +
        (-(projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma : ℂ) •
          projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  let gamma : ℂ := ((Real.sqrt (1 - pair.sigma ^ 2) : ℝ) : ℂ)
  have hgamma_pos : 0 < 1 - pair.sigma ^ 2 := by
    nlinarith [pair.sigma_pos, hsigma_lt_one]
  have hgamma_ne : gamma ≠ 0 := by
    dsimp [gamma]
    exact_mod_cast (Real.sqrt_pos.2 hgamma_pos).ne'
  have hgamma_sq : gamma * gamma = 1 - (pair.sigma : ℂ) ^ 2 := by
    dsimp [gamma]
    have hsqrt_sq :
        Real.sqrt (1 - pair.sigma ^ 2) * Real.sqrt (1 - pair.sigma ^ 2) =
          1 - pair.sigma ^ 2 := by
      rw [← pow_two, Real.sq_sqrt (le_of_lt hgamma_pos)]
    rw [← Complex.ofReal_mul, hsqrt_sq]
    norm_num [pow_two]
  have hproj :
      HilbertOperator.applyVec left.op (U.applyVec pair.rightVec) =
        (pair.sigma : ℂ) • pair.leftVec := by
    have hA := pair.A_right
    change HilbertOperator.applyVec
        (left.op * (U : HilbertOperator (Qubits N)) * right.op) pair.rightVec =
      (pair.sigma : ℂ) • pair.leftVec at hA
    rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
      pair.right_support] at hA
    simpa [Gate.applyVec] using hA
  have hleftPerp :
      projectedUnitaryBlockLeftPerpCandidate left right U i hlambda =
        gamma⁻¹ •
          (U.applyVec pair.rightVec -
            (pair.sigma : ℂ) • pair.leftVec) := by
    unfold projectedUnitaryBlockLeftPerpCandidate
    dsimp [pair, gamma]
    rw [orthogonalProjector_complement_applyVec, hproj]
    rfl
  have hUdagLeft :=
    projectedUnitaryBlock_Udag_leftVec_decomposition left right U i hlambda hsigma_lt_one
  have hUinv := gate_conjTranspose_applyVec_applyVec U pair.rightVec
  have hscale_left : gamma⁻¹ * (1 - (pair.sigma : ℂ) ^ 2) = gamma := by
    rw [← hgamma_sq]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hscale_perp : gamma⁻¹ * ((pair.sigma : ℂ) * gamma) = (pair.sigma : ℂ) := by
    rw [mul_comm (pair.sigma : ℂ) gamma]
    rw [← mul_assoc, inv_mul_cancel₀ hgamma_ne, one_mul]
  have hcoeff_left :
      gamma⁻¹ + -(gamma⁻¹ * ((pair.sigma : ℂ) * (pair.sigma : ℂ))) = gamma := by
    have h := hscale_left
    rw [sub_eq_add_neg, mul_add, mul_one, mul_neg, pow_two] at h
    simpa [mul_assoc] using h
  have hcoeff_perp :
      -(gamma⁻¹ * ((pair.sigma : ℂ) * gamma)) = -(pair.sigma : ℂ) := by
    rw [hscale_perp]
  calc
    U.conjTranspose.applyVec
        (projectedUnitaryBlockLeftPerpCandidate left right U i hlambda) =
        U.conjTranspose.applyVec (gamma⁻¹ •
          (U.applyVec pair.rightVec -
            (pair.sigma : ℂ) • pair.leftVec)) := by
      rw [hleftPerp]
    _ = gamma⁻¹ •
          (U.conjTranspose.applyVec (U.applyVec pair.rightVec) -
            (pair.sigma : ℂ) • U.conjTranspose.applyVec pair.leftVec) := by
      rw [Gate.applyVec_smul, Gate.applyVec_sub, Gate.applyVec_smul]
    _ = gamma⁻¹ •
          (pair.rightVec -
            (pair.sigma : ℂ) •
              (((pair.sigma : ℂ) • pair.rightVec) +
                gamma • projectedUnitaryBlockRightPerpCandidate left right U i hlambda)) := by
      rw [hUinv, hUdagLeft]
    _ = gamma • pair.rightVec +
          (-(pair.sigma : ℂ)) •
            projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
      calc
        gamma⁻¹ •
            (pair.rightVec -
              (pair.sigma : ℂ) •
                (((pair.sigma : ℂ) • pair.rightVec) +
                  gamma • projectedUnitaryBlockRightPerpCandidate left right U i hlambda)) =
            (gamma⁻¹ + -(gamma⁻¹ * ((pair.sigma : ℂ) * (pair.sigma : ℂ)))) •
                pair.rightVec +
              (-(gamma⁻¹ * ((pair.sigma : ℂ) * gamma))) •
                projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
          module
        _ = gamma • pair.rightVec +
              (-(pair.sigma : ℂ)) •
                projectedUnitaryBlockRightPerpCandidate left right U i hlambda := by
          rw [hcoeff_left, hcoeff_perp]

/-- Source-facing certificate for one two-dimensional singular-value block in
`lemma:singInvDec`.  For a singular value `0 < sigma < 1`, Gilyén et al. build
right/left singular vectors together with their orthogonal complements so that
`U` acts by the displayed two-by-two block [GSLW19, BlockHam.tex:583-613,
655-735].  This structure records the local block data used before assembling
the global direct-sum decomposition. -/
structure SourceTwoDimensionalSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Singular value for the `0 < sigma < 1` two-dimensional source sector. -/
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  /-- Right singular vector supported by the input projector. -/
  rightVec : StateVector (Qubits N)
  /-- Left singular vector supported by the output projector. -/
  leftVec : StateVector (Qubits N)
  /-- Right-complement vector paired with `leftVec` by `U†`. -/
  rightPerp : StateVector (Qubits N)
  /-- Left-complement vector paired with `rightVec` by `U`. -/
  leftPerp : StateVector (Qubits N)
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
      (sigma : ℂ) • leftVec + ((Real.sqrt (1 - sigma ^ 2) : ℝ) : ℂ) • leftPerp
  U_rightPerp :
    U.applyVec rightPerp =
      ((Real.sqrt (1 - sigma ^ 2) : ℝ) : ℂ) • leftVec + (-(sigma : ℂ)) • leftPerp
  Udag_left :
    U.conjTranspose.applyVec leftVec =
      (sigma : ℂ) • rightVec + ((Real.sqrt (1 - sigma ^ 2) : ℝ) : ℂ) • rightPerp
  Udag_leftPerp :
    U.conjTranspose.applyVec leftPerp =
      ((Real.sqrt (1 - sigma ^ 2) : ℝ) : ℂ) • rightVec + (-(sigma : ℂ)) • rightPerp

namespace SourceTwoDimensionalSingularBlock

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec =
      (block.sigma : Complex) • block.leftVec := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) =
    (block.sigma : Complex) • block.leftVec
  rw [block.U_right]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

theorem projectedUnitaryBlock_conjTranspose_applyVec_leftVec {N : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        block.leftVec =
      (block.sigma : Complex) • block.rightVec := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.left_support]
  change HilbertOperator.applyVec right.op (U.conjTranspose.applyVec block.leftVec) =
    (block.sigma : Complex) • block.rightVec
  rw [block.Udag_left]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- On a nontrivial source two-dimensional singular block, the Gram operator has
eigenvalue `σ^2` on the right singular vector [GSLW19, BlockHam.tex:655-735,
747-764]. -/
theorem gram_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        block.rightVec =
      ((block.sigma : Complex) ^ 2) • block.rightVec := by
  rw [HilbertOperator.mul_applyVec, block.projectedUnitaryBlock_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_conjTranspose_applyVec_leftVec,
    smul_smul]
  ring_nf

theorem evenSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (evenSingularValuePolynomial right P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.rightVec := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      ((block.sigma : Complex) ^ 2) block.rightVec
      block.gram_applyVec_rightVec,
    evenSquareQuotient_eval_sq_of_hasParity hL hP,
    HilbertOperator.applyVec_smul, block.right_support]

theorem oddSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (oddSingularValuePolynomial P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.leftVec := by
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      ((block.sigma : Complex) ^ 2) block.rightVec
      block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_applyVec_rightVec, smul_smul]
  have hodd := oddSquareQuotient_eval_sq_of_hasParity hL hP (block.sigma : Complex)
  rw [← hodd]
  ring_nf

theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.rightVec := by
  unfold singularValuePolynomial
  simp [hL, evenSingularValuePolynomial_applyVec_rightVec block P hL hP]

theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.leftVec := by
  unfold singularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  simp [hnot, oddSingularValuePolynomial_applyVec_rightVec block P hL hP]

theorem sigma_mem_unitInterval {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    block.sigma ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨le_trans (by norm_num) (le_of_lt block.sigma_pos), le_of_lt block.sigma_lt_one⟩

theorem right_phase_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
      Complex.exp (phi * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi right block.right_support

theorem right_phase_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightPerp =
      Complex.exp (-(phi * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi right block.right_perp_support

theorem left_phase_on_leftVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftVec =
      Complex.exp (phi * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi left block.left_support

theorem left_phase_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftPerp =
      Complex.exp (-(phi * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi left block.left_perp_support

theorem odd_signal_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec =
      (block.sigma : ℂ) • block.leftVec +
        ((Real.sqrt (1 - block.sigma ^ 2) : ℝ) : ℂ) • block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem odd_signal_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp =
      ((Real.sqrt (1 - block.sigma ^ 2) : ℝ) : ℂ) • block.leftVec +
        (-(block.sigma : ℂ)) • block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  simpa [neg_smul] using block.U_rightPerp

theorem even_signal_on_leftVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftVec =
      (block.sigma : ℂ) • block.rightVec +
        ((Real.sqrt (1 - block.sigma ^ 2) : ℝ) : ℂ) • block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  exact block.Udag_left

theorem even_signal_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    (sourcePhaseSignal U remaining).applyVec block.leftPerp =
      ((Real.sqrt (1 - block.sigma ^ 2) : ℝ) : ℂ) • block.rightVec +
        (-(block.sigma : ℂ)) • block.rightPerp := by
  rw [sourcePhaseSignal, if_pos hremaining]
  simpa [neg_smul] using block.Udag_leftPerp

end SourceTwoDimensionalSingularBlock

/-- A nonzero projected-block singular pair with `0 < σ < 1` gives the
two-dimensional invariant sector of `lemma:singInvDec` [GSLW19,
BlockHam.tex:583-613,655-735]. -/
noncomputable def projectedUnitaryBlockTwoDimensionalSingularBlock {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma_lt_one :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1) :
    SourceTwoDimensionalSingularBlock U left right := by
  let pair := projectedUnitaryBlockNonzeroSingularPair left right U i hlambda
  refine
    { sigma := pair.sigma
      sigma_pos := pair.sigma_pos
      sigma_lt_one := hsigma_lt_one
      rightVec := pair.rightVec
      leftVec := pair.leftVec
      rightPerp := projectedUnitaryBlockRightPerpCandidate left right U i hlambda
      leftPerp := projectedUnitaryBlockLeftPerpCandidate left right U i hlambda
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
structure SourceUnitSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right singular vector in the unit singular-value sector. -/
  rightVec : StateVector (Qubits N)
  /-- Left singular vector paired with `rightVec` by `U`. -/
  leftVec : StateVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  U_right : U.applyVec rightVec = leftVec
  Udag_left : U.conjTranspose.applyVec leftVec = rightVec

namespace SourceUnitSingularBlock

theorem right_phase_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
      Complex.exp (phi * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi right block.right_support

theorem left_phase_on_leftVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftVec =
      Complex.exp (phi * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi left block.left_support

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec =
      block.leftVec := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) = block.leftVec
  rw [block.U_right, block.left_support]

theorem projectedUnitaryBlock_conjTranspose_applyVec_leftVec {N : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        block.leftVec =
      block.rightVec := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.left_support]
  change HilbertOperator.applyVec right.op (U.conjTranspose.applyVec block.leftVec) =
    block.rightVec
  rw [block.Udag_left, block.right_support]

theorem gram_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
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
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
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
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
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

theorem odd_signal_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec = block.leftVec := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem even_signal_on_leftVec {N : Nat} {U : Gate (Qubits N)}
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
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma = 1) :
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
        (pair.sigma : ℂ) • pair.leftVec at hA
      rw [HilbertOperator.mul_applyVec,
        HilbertOperator.mul_applyVec, pair.right_support, hsigma] at hA
      simpa [Gate.applyVec] using hA
    have hU_norm : ‖U.applyVec pair.rightVec‖ = 1 := by
      change ‖HilbertOperator.applyVec (U : HilbertOperator (Qubits N)) pair.rightVec‖ = 1
      rw [HilbertOperator.norm_applyVec_of_mem_unitaryGroup U.unitary, pair.right_norm]
    have hproj_norm :
        ‖HilbertOperator.applyVec left.op (U.applyVec pair.rightVec)‖ = 1 := by
      rw [hproj, pair.left_norm]
    have hsupport :=
      orthogonalProjector_applyVec_eq_self_of_norm_eq_one left
        (U.applyVec pair.rightVec) hU_norm hproj_norm
    exact hsupport.symm.trans hproj
  · have hproj :
        HilbertOperator.applyVec right.op (U.conjTranspose.applyVec pair.leftVec) =
          pair.rightVec := by
      have hA := pair.Astar_left
      change HilbertOperator.applyVec
          (Matrix.conjTranspose
            (left.op * (U : HilbertOperator (Qubits N)) * right.op)) pair.leftVec =
        (pair.sigma : ℂ) • pair.rightVec at hA
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        left.selfAdjoint, right.selfAdjoint, HilbertOperator.mul_applyVec,
        HilbertOperator.mul_applyVec, pair.left_support, hsigma] at hA
      simpa [Gate.applyVec] using hA
    have hU_norm : ‖U.conjTranspose.applyVec pair.leftVec‖ = 1 := by
      change ‖HilbertOperator.applyVec (U.conjTranspose : HilbertOperator (Qubits N))
        pair.leftVec‖ = 1
      rw [HilbertOperator.norm_applyVec_of_mem_unitaryGroup U.conjTranspose.unitary,
        pair.left_norm]
    have hproj_norm :
        ‖HilbertOperator.applyVec right.op (U.conjTranspose.applyVec pair.leftVec)‖ = 1 := by
      rw [hproj, pair.right_norm]
    have hsupport :=
      orthogonalProjector_applyVec_eq_self_of_norm_eq_one right
        (U.conjTranspose.applyVec pair.leftVec) hU_norm hproj_norm
    exact hsupport.symm.trans hproj

/-- Source-facing classification for nonzero singular sectors in
`lemma:singInvDec`: a sector is either `σ=1` and one-dimensional, or
`0<σ<1` and two-dimensional [GSLW19, BlockHam.tex:583-613,655-735]. -/
inductive SourceNonzeroClassifiedSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) : Type where
  | unitBlock : SourceUnitSingularBlock U left right ->
      SourceNonzeroClassifiedSingularBlock U left right
  | twoDimensionalBlock : SourceTwoDimensionalSingularBlock U left right ->
      SourceNonzeroClassifiedSingularBlock U left right

/-- Classify a nonzero projected singular pair into the source's `σ=1` or
`0<σ<1` invariant sector [GSLW19, BlockHam.tex:583-613,655-735]. -/
noncomputable def projectedUnitaryBlockNonzeroClassifiedSingularBlock {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceNonzeroClassifiedSingularBlock U left right := by
  classical
  by_cases hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma = 1
  · exact SourceNonzeroClassifiedSingularBlock.unitBlock
      (projectedUnitaryBlockUnitSingularBlock left right U i hlambda hsigma)
  · have hlt :
        (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1 := by
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
structure SourceRightKernelSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-supported vector in the zero singular-value sector. -/
  rightVec : StateVector (Qubits N)
  /-- Left-complement image of the right-kernel vector under `U`. -/
  leftPerp : StateVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement left) leftPerp = leftPerp
  U_right : U.applyVec rightVec = leftPerp
  Udag_leftPerp : U.conjTranspose.applyVec leftPerp = rightVec

namespace SourceRightKernelSingularBlock

theorem right_phase_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
      Complex.exp (phi * Complex.I) • block.rightVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi right block.right_support

theorem left_phase_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftPerp =
      Complex.exp (-(phi * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi left block.left_perp_support

theorem odd_signal_on_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightVec = block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_right

theorem even_signal_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
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
structure SourceLeftKernelSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-complement preimage of the left-kernel vector under `U`. -/
  rightPerp : StateVector (Qubits N)
  /-- Left-supported vector in the zero singular-value sector. -/
  leftVec : StateVector (Qubits N)
  right_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp = rightPerp
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  U_rightPerp : U.applyVec rightPerp = leftVec
  Udag_left : U.conjTranspose.applyVec leftVec = rightPerp

namespace SourceLeftKernelSingularBlock

theorem right_phase_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightPerp =
      Complex.exp (-(phi * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi right block.right_perp_support

theorem left_phase_on_leftVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftVec =
      Complex.exp (phi * Complex.I) • block.leftVec :=
  projectorPhaseOp_applyVec_of_projector_applyVec_eq_self phi left block.left_support

theorem odd_signal_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp = block.leftVec := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_rightPerp

theorem even_signal_on_leftVec {N : Nat} {U : Gate (Qubits N)}
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
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (rightVec : StateVector (Qubits N))
    (hright : HilbertOperator.applyVec right.op rightVec = rightVec)
    (hzero : HilbertOperator.applyVec (projectedUnitaryBlock left right U) rightVec = 0) :
    SourceRightKernelSingularBlock U left right :=
  { rightVec := rightVec,
    leftPerp := U.applyVec rightVec,
    right_support := hright,
    left_perp_support := by
      have hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightVec) = 0 := by
        have h := hzero
        unfold projectedUnitaryBlock at h
        rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, hright] at h
        simpa [Gate.applyVec] using h
      rw [orthogonalProjector_complement_applyVec, hleft_zero, sub_zero],
    U_right := rfl,
    Udag_leftPerp := by
      simpa using gate_conjTranspose_applyVec_applyVec U rightVec }

/-- Construct the left-kernel sector of `lemma:singInvDec` from a left-supported
vector whose adjoint projected-unitary image is zero.  This is the left-handed
zero-singular-value companion of
`sourceRightKernelSingularBlockOfProjectedBlockEqZero`
[GSLW19, BlockHam.tex:599-611,655-716]. -/
noncomputable def sourceLeftKernelSingularBlockOfProjectedBlockConjTransposeEqZero
    {N : Nat} (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (leftVec : StateVector (Qubits N))
    (hleft : HilbertOperator.applyVec left.op leftVec = leftVec)
    (hzero :
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        leftVec = 0) :
    SourceLeftKernelSingularBlock U left right :=
  { rightPerp := U.conjTranspose.applyVec leftVec,
    leftVec := leftVec,
    right_perp_support := by
      have hright_zero :
          HilbertOperator.applyVec right.op (U.conjTranspose.applyVec leftVec) = 0 := by
        have h := hzero
        unfold projectedUnitaryBlock at h
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          left.selfAdjoint, right.selfAdjoint,
          HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, hleft] at h
        simpa [Gate.applyVec] using h
      rw [orthogonalProjector_complement_applyVec, hright_zero, sub_zero],
    left_support := hleft,
    U_rightPerp := by
      simpa using gate_applyVec_conjTranspose_applyVec U leftVec,
    Udag_left := rfl }

/-- Source-facing certificate for the fully complementary sector in
`lemma:singInvDec`: `U` maps the right complement of the singular-vector
decomposition to the corresponding left complement [GSLW19,
BlockHam.tex:607-613,718-735]. -/
structure SourceComplementSingularBlock {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Right-complement vector in the fully complementary sector. -/
  rightPerp : StateVector (Qubits N)
  /-- Left-complement vector paired with `rightPerp` by `U`. -/
  leftPerp : StateVector (Qubits N)
  right_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp = rightPerp
  left_perp_support :
    HilbertOperator.applyVec (OrthogonalProjector.complement left) leftPerp = leftPerp
  U_rightPerp : U.applyVec rightPerp = leftPerp
  Udag_leftPerp : U.conjTranspose.applyVec leftPerp = rightPerp

namespace SourceComplementSingularBlock

theorem right_phase_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightPerp =
      Complex.exp (-(phi * Complex.I)) • block.rightPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi right block.right_perp_support

theorem left_phase_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) (phi : ℝ) :
    HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftPerp =
      Complex.exp (-(phi * Complex.I)) • block.leftPerp :=
  projectorPhaseOp_applyVec_of_complement_applyVec_eq_self phi left block.left_perp_support

theorem odd_signal_on_rightPerp {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    (sourcePhaseSignal U remaining).applyVec block.rightPerp = block.leftPerp := by
  rw [sourcePhaseSignal, if_neg hremaining]
  exact block.U_rightPerp

theorem even_signal_on_leftPerp {N : Nat} {U : Gate (Qubits N)}
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
    {N : Nat} (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (rightPerp : StateVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceComplementSingularBlock U left right :=
  { rightPerp := rightPerp,
    leftPerp := U.applyVec rightPerp,
    right_perp_support := hright_perp,
    left_perp_support := by
      rw [orthogonalProjector_complement_applyVec, hleft_zero, sub_zero],
    U_rightPerp := rfl,
    Udag_leftPerp := by
      simpa using gate_conjTranspose_applyVec_applyVec U rightPerp }

/-- Source-facing direct-sum skeleton for `lemma:singInvDec`.  The source
decomposes the space into singular-value-one, two-dimensional `0 < sigma < 1`,
right-kernel, left-kernel, and fully complementary sectors; each sector is
recorded above with the local `U`, `U†`, and projector-phase actions needed for
`thm:singValTransformation` [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantDecomposition {N : Nat} (U : Gate (Qubits N))
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

/-- Bundle the source projector phase as a signal-space gate. -/
noncomputable def projectorPhase {N : Nat} (phi : ℝ) (P : OrthogonalProjector N) :
    Gate (Qubits N) :=
  Gate.ofUnitary (projectorPhaseOp phi P) (projectorPhaseOp_mem_unitaryGroup phi P)

@[simp]
theorem projectorPhase_zero {N : Nat} (P : OrthogonalProjector N) :
    projectorPhase 0 P = 1 := by
  apply Gate.ext
  intro i j
  change projectorPhaseOp 0 P i j = (1 : HilbertOperator (Qubits N)) i j
  simp [projectorPhaseOp, OrthogonalProjector.complement]

/-- Source-level alternating phase modulation sequence `U_Φ` on the signal
space.  This is Definition `def:phaseSeq`: it alternates projector phases with
`U` and `U†`, starting from `\widetilde\Pi/U` for odd length and from
`\Pi/U†` for even length [GSLW19, BlockHam.tex:738-745]. -/
noncomputable def sourceAlternatingPhaseModulation {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) : List ℝ → Gate (Qubits N)
  | [] => 1
  | phi :: phases =>
      projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))
        * sourcePhaseSignal U (phases.length + 1)
        * sourceAlternatingPhaseModulation U left right phases

@[simp]
theorem sourceAlternatingPhaseModulation_nil {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) :
    sourceAlternatingPhaseModulation U left right [] = 1 := rfl

theorem sourceAlternatingPhaseModulation_cons {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phi : ℝ) (phases : List ℝ) :
    sourceAlternatingPhaseModulation U left right (phi :: phases) =
      projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))
        * sourcePhaseSignal U (phases.length + 1)
        * sourceAlternatingPhaseModulation U left right phases := rfl

/-- Scalar phase product accumulated by a one-dimensional singular block of
the source alternating phase sequence. -/
noncomputable def phaseProduct (phases : List ℝ) : ℂ :=
  (phases.map fun phi => Complex.exp (phi * Complex.I)).prod

@[simp]
theorem phaseProduct_nil : phaseProduct [] = 1 := rfl

@[simp]
theorem phaseProduct_cons (phi : ℝ) (phases : List ℝ) :
    phaseProduct (phi :: phases) =
      Complex.exp (phi * Complex.I) * phaseProduct phases := by
  simp [phaseProduct]

/-- The `(0,0)` scalar entry of the `W`-convention one-qubit QSP product at
`x=1` is the product of all scalar phase factors. -/
theorem qspW_one_zero_zero_eq_phaseProduct (φ₀ : ℝ) (φs : List ℝ) :
    qspW φ₀ φs 1 0 0 =
      Complex.exp (φ₀ * Complex.I) *
        (φs.map fun φ => Complex.exp (φ * Complex.I)).prod := by
  induction φs using List.reverseRecOn with
  | nil =>
      simp [qspW, rotZ, rotZOp]
  | append_singleton φs φ ih =>
      rw [qspW_concat]
      simp [Matrix.mul_apply, signalW, rotZ, rotZOp, ih]
      ring

/-- The real `R(x)` signal block used in the source proof of singular-value
transformation.  It is the local two-dimensional block induced by `U` and
`U†` on a nontrivial singular sector [GSLW19, BlockHam.tex:520-528,768-849]. -/
noncomputable def singularSignalR (x : ℝ) : HilbertOperator (Qubits 1) :=
  !![(x : ℂ), (Real.sqrt (1 - x ^ 2) : ℂ);
     (Real.sqrt (1 - x ^ 2) : ℂ), (-(x : ℂ))]

-- CSLib weak-linter exception: this source-aligned 2x2 matrix expansion is
-- kept in its existing proof shape; `simp only` rewrites were brittle here.
set_option linter.flexible false in
/-- In the repository's `rotZ` convention, the source identity
`W(x)=i e^{-iπσ_z/4} R(x)e^{-iπσ_z/4}` is the matrix bridge from the
`W`-convention QSP certificate to the projected-QSVT `R` product
[GSLW19, BlockHam.tex:514-517]. -/
theorem signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ (x : ℝ) :
    signalW x =
      (Complex.I : ℂ) •
        ((rotZ (-(Real.pi / 4)) : HilbertOperator (Qubits 1)) *
          singularSignalR x * (rotZ (-(Real.pi / 4)) : HilbertOperator (Qubits 1))) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [signalW, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
    have hprod :
        Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑x * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑x * Complex.exp (-(↑Real.pi / 2 * Complex.I)) := by
      rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑x * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑x * (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))) by ring]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    rw [hprod, exp_neg_pi_div_two_mul_I]
    rw [mul_comm (x : ℂ) (-Complex.I), ← mul_assoc]
    rw [show Complex.I * -Complex.I = (1 : ℂ) by
      rw [mul_neg, Complex.I_mul_I]
      ring]
    ring
  · simp [signalW, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
    have hprod :
        Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑√(1 - x ^ 2) * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑√(1 - x ^ 2) := by
      rw [show Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            ↑√(1 - x ^ 2) * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑√(1 - x ^ 2) * (Complex.exp (-(↑Real.pi / 4 * Complex.I)) *
            Complex.exp (↑Real.pi / 4 * Complex.I)) by ring]
      rw [← Complex.exp_add]
      simp
    rw [hprod]
  · simp [signalW, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
    have hprod :
        Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑√(1 - x ^ 2) * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑√(1 - x ^ 2) := by
      rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑√(1 - x ^ 2) * Complex.exp (-(↑Real.pi / 4 * Complex.I)) =
          ↑√(1 - x ^ 2) * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (-(↑Real.pi / 4 * Complex.I))) by ring]
      rw [← Complex.exp_add]
      simp
    rw [hprod]
  · simp [signalW, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
    have hprod :
        Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑x * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑x * Complex.exp (↑Real.pi / 2 * Complex.I) := by
      rw [show Complex.exp (↑Real.pi / 4 * Complex.I) *
            ↑x * Complex.exp (↑Real.pi / 4 * Complex.I) =
          ↑x * (Complex.exp (↑Real.pi / 4 * Complex.I) *
            Complex.exp (↑Real.pi / 4 * Complex.I)) by ring]
      rw [← Complex.exp_add]
      congr 1
      ring_nf
    rw [hprod, exp_pi_div_two_mul_I]
    rw [mul_comm (x : ℂ) Complex.I, ← mul_assoc, Complex.I_mul_I]
    ring

/-- The source's `R`-convention product
`∏_j (e^{iφ_jσ_z} R(x))`, written in the same left-to-right order as the
projected-unitary phase sequence [GSLW19, BlockHam.tex:520-528,768-849]. -/
noncomputable def singularSignalRProduct : List ℝ -> ℝ -> HilbertOperator (Qubits 1)
  | [], _ => 1
  | phi :: phases, x =>
      (rotZ phi : HilbertOperator (Qubits 1)) *
        singularSignalR x * singularSignalRProduct phases x

@[simp]
theorem singularSignalRProduct_nil (x : ℝ) :
    singularSignalRProduct [] x = 1 := rfl

@[simp]
theorem singularSignalRProduct_cons (phi : ℝ) (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (phi :: phases) x =
      (rotZ phi : HilbertOperator (Qubits 1)) *
        singularSignalR x * singularSignalRProduct phases x := rfl

/-- Appending one source `R`-signal block on the right multiplies the existing
source product by that block [GSLW19, BlockHam.tex:501-528]. -/
theorem singularSignalRProduct_append_singleton (phases : List ℝ) (phi x : ℝ) :
    singularSignalRProduct (phases ++ [phi]) x =
      singularSignalRProduct phases x *
        ((rotZ phi : HilbertOperator (Qubits 1)) * singularSignalR x) := by
  induction phases with
  | nil =>
      simp [singularSignalRProduct]
  | cons theta phases ih =>
      simp [singularSignalRProduct, ih, mul_assoc]

private theorem rotZ_neg_eq_map_star (phi : ℝ) :
    (rotZ (-phi) : HilbertOperator (Qubits 1)) =
      ((rotZ phi : HilbertOperator (Qubits 1)).map (starRingEnd ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotZOp, conj_exp_I, conj_exp_neg_I]

private theorem singularSignalR_eq_map_star (x : ℝ) :
    singularSignalR x = (singularSignalR x).map (starRingEnd ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [singularSignalR]

theorem singularSignalRProduct_map_neg_eq_map_star (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (phases.map fun phi => -phi) x =
      (singularSignalRProduct phases x).map (starRingEnd ℂ) := by
  induction phases with
  | nil =>
      simp [singularSignalRProduct]
  | cons phi phases ih =>
      simp only [List.map_cons, singularSignalRProduct_cons]
      rw [ih, rotZ_neg_eq_map_star]
      rw [Matrix.map_mul, Matrix.map_mul]
      rw [← singularSignalR_eq_map_star]

theorem singularSignalRProduct_map_neg_zero_zero (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (phases.map fun phi => -phi) x 0 0 =
      star (singularSignalRProduct phases x 0 0) := by
  rw [singularSignalRProduct_map_neg_eq_map_star]
  rfl

/-- The `rotZ` multiplication rule at the `HilbertOperator` coercion layer. -/
theorem rotZ_op_mul (a b : ℝ) :
    (rotZ a : HilbertOperator (Qubits 1)) *
        (rotZ b : HilbertOperator (Qubits 1)) =
      (rotZ (a + b) : HilbertOperator (Qubits 1)) := by
  simpa using congrArg (fun G : Gate (Qubits 1) => (G : HilbertOperator (Qubits 1)))
    (rotZ_mul_rotZ a b)

private theorem matrix_smul_mul_smul_mul (A B C : HilbertOperator (Qubits 1)) (c d : ℂ) :
    (c • A) * ((d • B) * C) = (c * d) • (A * B * C) := by
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp [mul_assoc]

/-- Reassociate the source's `R`-signal bridge phases around one signal block.
This is the local matrix identity used in converting `W`-convention QSP
products into `R`-convention projected-QSVT products
[GSLW19, BlockHam.tex:514-528]. -/
private theorem rotZ_singularSignalR_rotZ_reassociate (a b c d x : ℝ) :
    (rotZ a : HilbertOperator (Qubits 1)) *
        ((rotZ b : HilbertOperator (Qubits 1)) * singularSignalR x *
          (rotZ c : HilbertOperator (Qubits 1))) *
        (rotZ d : HilbertOperator (Qubits 1)) =
      (rotZ (a + b) : HilbertOperator (Qubits 1)) *
        singularSignalR x * (rotZ (c + d) : HilbertOperator (Qubits 1)) := by
  calc
    (rotZ a : HilbertOperator (Qubits 1)) *
        ((rotZ b : HilbertOperator (Qubits 1)) * singularSignalR x *
          (rotZ c : HilbertOperator (Qubits 1))) *
        (rotZ d : HilbertOperator (Qubits 1))
        = ((rotZ a : HilbertOperator (Qubits 1)) *
            (rotZ b : HilbertOperator (Qubits 1))) *
          singularSignalR x *
            ((rotZ c : HilbertOperator (Qubits 1)) *
              (rotZ d : HilbertOperator (Qubits 1))) := by
          noncomm_ring
    _ = (rotZ (a + b) : HilbertOperator (Qubits 1)) *
        singularSignalR x * (rotZ (c + d) : HilbertOperator (Qubits 1)) := by
          rw [rotZ_op_mul, rotZ_op_mul]

/-- The raw `R`-product appearing before the source absorbs the terminal scalar
phase into the first projected-QSVT phase [GSLW19, BlockHam.tex:514-528]. -/
noncomputable def singularSignalRRawProduct (φ₀ : ℝ) (init : List ℝ) (x : ℝ) :
    HilbertOperator (Qubits 1) :=
  singularSignalRProduct ((φ₀ - Real.pi / 4) :: init.map (fun φ => φ - Real.pi / 2)) x

-- CSLib weak-linter exception: this induction depends on the existing broad
-- simplification shape of the imported single-qubit `qspW` product.
set_option linter.flexible false in
/-- Source `W`-convention QSP products equal the raw `R`-convention projected
QSVT product, up to the scalar `i^{L}` and the terminal source phase.  This is
the product form of the phase conversion in [GSLW19, BlockHam.tex:514-528]. -/
theorem qspW_eq_I_pow_smul_rawProduct_mul_terminal (φ₀ : ℝ)
    (init : List ℝ) (last x : ℝ) :
    qspW φ₀ (init ++ [last]) x =
      (Complex.I ^ (init.length + 1)) •
        (singularSignalRRawProduct φ₀ init x *
          (rotZ (last - Real.pi / 4) : HilbertOperator (Qubits 1))) := by
  revert last
  induction init using List.reverseRecOn with
  | nil =>
      intro last
      simp [qspW, singularSignalRRawProduct, singularSignalRProduct,
        signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ]
      rw [show (rotZ φ₀).op *
          ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
            (rotZ (-(Real.pi / 4))).op * (rotZ last).op) =
        (rotZ φ₀).op *
          ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
            (rotZ (-(Real.pi / 4))).op) *
          (rotZ last).op by noncomm_ring]
      calc
        (rotZ φ₀).op *
            ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
              (rotZ (-(Real.pi / 4))).op) *
            (rotZ last).op =
          (rotZ (φ₀ + -(Real.pi / 4))).op *
            singularSignalR x * (rotZ (-(Real.pi / 4) + last)).op := by
            simpa using
              rotZ_singularSignalR_rotZ_reassociate φ₀ (-(Real.pi / 4))
                (-(Real.pi / 4)) last x
        _ =
          (rotZ (φ₀ - Real.pi / 4)).op * singularSignalR x *
            (rotZ (last - Real.pi / 4)).op := by
            congr 2
            all_goals ring_nf
  | append_singleton init φ ih =>
      intro last
      rw [show init ++ [φ] ++ [last] = (init ++ [φ]) ++ [last] by simp]
      rw [qspW_concat, ih φ]
      rw [signalW_eq_I_smul_rotZ_mul_singularSignalR_mul_rotZ]
      rw [matrix_smul_mul_smul_mul]
      unfold singularSignalRRawProduct
      rw [List.map_append]
      change (Complex.I ^ (init.length + 1) * Complex.I) •
          (singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZ (φ - Real.pi / 4)).op *
            ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                (rotZ (-(Real.pi / 4))).op) *
              (rotZ last).op) =
        Complex.I ^ ((init ++ [φ]).length + 1) •
          (singularSignalRProduct
              (((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) ++ [φ - Real.pi / 2]) x *
            (rotZ (last - Real.pi / 4)).op)
      rw [singularSignalRProduct_append_singleton]
      rw [show (Complex.I ^ (init.length + 1) * Complex.I) =
          Complex.I ^ ((init ++ [φ]).length + 1) by
        simp [pow_succ]]
      have hmatrix :
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZ (φ - Real.pi / 4)).op *
            ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                (rotZ (-(Real.pi / 4))).op) *
              (rotZ last).op =
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
            ((rotZ (φ - Real.pi / 2)).op * singularSignalR x) *
              (rotZ (last - Real.pi / 4)).op := by
        have hblock :
            (rotZ (φ - Real.pi / 4)).op *
                ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                  (rotZ (-(Real.pi / 4))).op) *
                (rotZ last).op =
              (rotZ (φ - Real.pi / 2)).op * singularSignalR x *
                (rotZ (last - Real.pi / 4)).op := by
          calc
            (rotZ (φ - Real.pi / 4)).op *
                ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                  (rotZ (-(Real.pi / 4))).op) *
                (rotZ last).op =
              (rotZ ((φ - Real.pi / 4) + -(Real.pi / 4))).op *
                singularSignalR x * (rotZ (-(Real.pi / 4) + last)).op := by
                simpa using
                  rotZ_singularSignalR_rotZ_reassociate (φ - Real.pi / 4)
                    (-(Real.pi / 4)) (-(Real.pi / 4)) last x
            _ =
              (rotZ (φ - Real.pi / 2)).op * singularSignalR x *
                (rotZ (last - Real.pi / 4)).op := by
                congr 2
                all_goals ring_nf
        calc
          singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              (rotZ (φ - Real.pi / 4)).op *
            ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                (rotZ (-(Real.pi / 4))).op) *
              (rotZ last).op
              =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZ (φ - Real.pi / 4)).op *
                ((rotZ (-(Real.pi / 4))).op * singularSignalR x *
                  (rotZ (-(Real.pi / 4))).op) *
                (rotZ last).op) := by
                noncomm_ring
          _ =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZ (φ - Real.pi / 2)).op * singularSignalR x *
                (rotZ (last - Real.pi / 4)).op) := by
                rw [hblock]
          _ =
            singularSignalRProduct ((φ₀ - Real.pi / 4) ::
                List.map (fun φ => φ - Real.pi / 2) init) x *
              ((rotZ (φ - Real.pi / 2)).op * singularSignalR x) *
                (rotZ (last - Real.pi / 4)).op := by
                noncomm_ring
      rw [hmatrix]

/-- Right multiplication by `rotZ` multiplies the `(0,0)` entry by the positive
phase. -/
private theorem mul_rotZ_zero_zero (A : HilbertOperator (Qubits 1)) (theta : ℝ) :
    (A * (rotZ theta : HilbertOperator (Qubits 1))) 0 0 =
      A 0 0 * Complex.exp ((theta : ℂ) * Complex.I) := by
  simp [rotZ, rotZOp, Matrix.mul_apply]

/-- The scalar part of the source phase conversion
[GSLW19, BlockHam.tex:523-528]. -/
theorem I_pow_mul_terminal_phase (n : Nat) (last : ℝ) :
    Complex.I ^ (n + 1) * Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((last + n * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
        Complex.I) := by
  have hstep (theta : ℝ) :
      Complex.exp ((theta : ℂ) * Complex.I) * Complex.I =
        Complex.exp (((theta + Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp ((theta : ℂ) * Complex.I) * Complex.I =
          Complex.exp ((theta : ℂ) * Complex.I) *
            Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
            rw [exp_pi_div_two_mul_I]
      _ = Complex.exp (((theta : ℂ) * Complex.I) +
            ((Real.pi : ℂ) / 2 * Complex.I)) := by
            rw [Complex.exp_add]
      _ = Complex.exp (((theta + Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
            congr 1
            norm_num
            ring_nf
  induction n with
  | zero =>
      rw [pow_one]
      rw [show Complex.I * Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) * Complex.I by ring]
      rw [hstep]
      congr 1
      norm_num
      ring_nf
  | succ n ih =>
      rw [show Complex.I ^ (n + 1 + 1) *
          Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
          (Complex.I ^ (n + 1) *
            Complex.exp (((last - Real.pi / 4 : ℝ) : ℂ) * Complex.I)) * Complex.I by
          rw [pow_succ]
          ring]
      rw [ih]
      rw [hstep]
      congr 1
      norm_num
      ring_nf

-- CSLib weak-linter exception: the terminal phase proof relies on the current
-- matrix-entry expansion of `rotZ` and the raw QSP product.
set_option linter.flexible false in
/-- The `(0,0)` entry of the `W`-convention QSP product equals the raw
`R`-product entry with the source scalar phase absorbed
[GSLW19, BlockHam.tex:514-528]. -/
theorem qspW_zero_zero_eq_rawProduct (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    qspW φ₀ (init ++ [last]) x 0 0 =
      Complex.exp (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) * singularSignalRRawProduct φ₀ init x 0 0 := by
  rw [qspW_eq_I_pow_smul_rawProduct_mul_terminal]
  simp [Matrix.mul_apply, rotZ, rotZOp]
  change Complex.I ^ (init.length + 1) *
      (singularSignalRRawProduct φ₀ init x 0 0 *
        Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I)) =
    Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
        (Real.pi : ℂ) / 4) * Complex.I) *
      singularSignalRRawProduct φ₀ init x 0 0
  have hphase :
      Complex.I ^ (init.length + 1) *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I) =
        Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
            (Real.pi : ℂ) / 4) * Complex.I) := by
    simpa using I_pow_mul_terminal_phase init.length last
  calc
    Complex.I ^ (init.length + 1) *
        (singularSignalRRawProduct φ₀ init x 0 0 *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I))
        =
      (Complex.I ^ (init.length + 1) *
          Complex.exp (((last : ℂ) - (Real.pi : ℂ) / 4) * Complex.I)) *
        singularSignalRRawProduct φ₀ init x 0 0 := by
        ring
    _ =
      Complex.exp (((last : ℂ) + (init.length : ℂ) * ((Real.pi : ℂ) / 2) +
          (Real.pi : ℂ) / 4) * Complex.I) *
        singularSignalRRawProduct φ₀ init x 0 0 := by
        rw [hphase]

-- CSLib weak-linter exception: this entrywise product proof is intentionally
-- kept close to the source phase algebra.
set_option linter.flexible false in
/-- Changing only the first source `R`-product phase multiplies the `(0,0)`
entry by the corresponding scalar phase [GSLW19, BlockHam.tex:523-528]. -/
theorem singularSignalRProduct_first_phase_zero_zero
    (a b : ℝ) (tail : List ℝ) (x : ℝ) :
    singularSignalRProduct (a :: tail) x 0 0 =
      Complex.exp (((a : ℂ) - (b : ℂ)) * Complex.I) *
        singularSignalRProduct (b :: tail) x 0 0 := by
  simp [singularSignalRProduct, rotZ, rotZOp, Matrix.mul_apply]
  have h_exp :
      Complex.exp (((a : ℂ) - (b : ℂ)) * Complex.I) *
          Complex.exp ((b : ℂ) * Complex.I) =
        Complex.exp ((a : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [mul_add]
  repeat rw [← mul_assoc]
  rw [h_exp]

theorem phaseProduct_eq_exp_sum (phases : List ℝ) :
    phaseProduct phases = Complex.exp (((phases.sum : ℝ) : ℂ) * Complex.I) := by
  induction phases with
  | nil =>
      simp [phaseProduct]
  | cons phi phases ih =>
      rw [phaseProduct_cons, ih, ← Complex.exp_add]
      congr 1
      norm_num
      ring

private theorem list_sum_map_const_add (c : ℝ) (xs : List ℝ) :
    (xs.map fun x => c + x).sum = xs.length * c + xs.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]
      ring_nf

private theorem list_sum_map_sub_const (c : ℝ) (xs : List ℝ) :
    (xs.map fun x => x - c).sum = xs.sum - xs.length * c := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]
      ring_nf

namespace SourceUnitSingularBlock

/-- On a one-dimensional singular-value-one block, the source alternating
phase sequence alternates between the right and left singular vectors and
accumulates the product of the scalar projector phases [GSLW19,
BlockHam.tex:655-671,738-849]. -/
theorem sourceAlternating_applyVec_rightVec {N : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          phaseProduct phases • block.rightVec) ∧
      (phases.length % 2 = 1 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          phaseProduct phases • block.leftVec) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [sourceAlternatingPhaseModulation]
      · intro h
        norm_num at h
  | cons phi phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              phaseProduct phases • block.leftVec :=
          ih.2 htail
        rw [htail_action, Gate.applyVec_smul]
        rw [SourceUnitSingularBlock.even_signal_on_leftVec block
          (remaining := phases.length + 1) hrem]
        change (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
            (phaseProduct phases • block.rightVec) =
          phaseProduct (phi :: phases) • block.rightVec
        rw [Gate.applyVec_smul]
        have hphase :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (phi * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
            Complex.exp (phi * Complex.I) • block.rightVec
          exact SourceUnitSingularBlock.right_phase_on_rightVec block phi
        rw [hphase]
        rw [phaseProduct_cons, smul_smul]
        have hmul :
            phaseProduct phases * Complex.exp (phi * Complex.I) =
              Complex.exp (phi * Complex.I) * phaseProduct phases := by ring
        rw [hmul]
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              phaseProduct phases • block.rightVec :=
          ih.1 htail
        rw [htail_action, Gate.applyVec_smul]
        rw [SourceUnitSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        change (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
            (phaseProduct phases • block.leftVec) =
          phaseProduct (phi :: phases) • block.leftVec
        rw [Gate.applyVec_smul]
        have hphase :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftVec =
                Complex.exp (phi * Complex.I) • block.leftVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftVec =
            Complex.exp (phi * Complex.I) • block.leftVec
          exact SourceUnitSingularBlock.left_phase_on_leftVec block phi
        rw [hphase]
        rw [phaseProduct_cons, smul_smul]
        have hmul :
            phaseProduct phases * Complex.exp (phi * Complex.I) =
              Complex.exp (phi * Complex.I) * phaseProduct phases := by ring
        rw [hmul]

end SourceUnitSingularBlock

namespace SourceTwoDimensionalSingularBlock

/-- On a nontrivial two-dimensional singular block, the source alternating
phase sequence has exactly the coordinates of the source `R`-convention QSP
product.  This is the local block computation used in
`thm:singValTransformation` before projecting onto the singular-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceAlternating_applyVec_rightVec_singularSignalRProduct {N : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases block.sigma 0 0 • block.rightVec +
            singularSignalRProduct phases block.sigma 1 0 • block.rightPerp) ∧
      (phases.length % 2 = 1 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases block.sigma 0 0 • block.leftVec +
            singularSignalRProduct phases block.sigma 1 0 • block.leftPerp) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [sourceAlternatingPhaseModulation]
      · intro h
        norm_num at h
  | cons phi phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases block.sigma 0 0 • block.leftVec +
                singularSignalRProduct phases block.sigma 1 0 • block.leftPerp :=
          ih.2 htail
        rw [htail_action, Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul]
        rw [SourceTwoDimensionalSingularBlock.even_signal_on_leftVec block
          (remaining := phases.length + 1) hrem]
        rw [SourceTwoDimensionalSingularBlock.even_signal_on_leftPerp block
          (remaining := phases.length + 1) hrem]
        rw [Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul,
          Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul,
          Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul]
        have hphase_right :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (phi * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
            Complex.exp (phi * Complex.I) • block.rightVec
          exact SourceTwoDimensionalSingularBlock.right_phase_on_rightVec block phi
        have hphase_right_perp :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightPerp =
                Complex.exp (-(phi * Complex.I)) • block.rightPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightPerp =
            Complex.exp (-(phi * Complex.I)) • block.rightPerp
          exact SourceTwoDimensionalSingularBlock.right_phase_on_rightPerp block phi
        rw [hphase_right, hphase_right_perp]
        simp [singularSignalRProduct, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
        module
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases block.sigma 0 0 • block.rightVec +
                singularSignalRProduct phases block.sigma 1 0 • block.rightPerp :=
          ih.1 htail
        rw [htail_action, Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul]
        rw [SourceTwoDimensionalSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        rw [SourceTwoDimensionalSingularBlock.odd_signal_on_rightPerp block
          (remaining := phases.length + 1) hrem_ne]
        rw [Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul,
          Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul,
          Gate.applyVec_add, Gate.applyVec_smul, Gate.applyVec_smul]
        have hphase_left :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftVec =
                Complex.exp (phi * Complex.I) • block.leftVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftVec =
            Complex.exp (phi * Complex.I) • block.leftVec
          exact SourceTwoDimensionalSingularBlock.left_phase_on_leftVec block phi
        have hphase_left_perp :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftPerp =
                Complex.exp (-(phi * Complex.I)) • block.leftPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftPerp =
            Complex.exp (-(phi * Complex.I)) • block.leftPerp
          exact SourceTwoDimensionalSingularBlock.left_phase_on_leftPerp block phi
        rw [hphase_left, hphase_left_perp]
        simp [singularSignalRProduct, singularSignalR, rotZ, rotZOp, Matrix.mul_apply]
        module

end SourceTwoDimensionalSingularBlock

namespace SourceRightKernelSingularBlock

/-- On a right-kernel singular block (`σ = 0`), the source alternating phase
sequence follows the `R(0)` local product: even lengths return to the right
singular vector, and odd lengths land in the left-complement vector.  This is
the zero-singular-value right-sector part of `thm:singValTransformation`
[GSLW19, BlockHam.tex:599-611,655-716,768-849]. -/
theorem sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero {N : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    ∀ phases : List ℝ,
      (phases.length % 2 = 0 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases 0 0 0 • block.rightVec) ∧
      (phases.length % 2 = 1 →
        (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
          singularSignalRProduct phases 0 1 0 • block.leftPerp) := by
  intro phases
  induction phases with
  | nil =>
      constructor
      · intro _
        simp [sourceAlternatingPhaseModulation]
      · intro h
        norm_num at h
  | cons phi phases ih =>
      constructor
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 0 := by
          exact hlen
        have htail : phases.length % 2 = 1 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases 0 1 0 • block.leftPerp :=
          ih.2 htail
        rw [htail_action, Gate.applyVec_smul]
        rw [SourceRightKernelSingularBlock.even_signal_on_leftPerp block
          (remaining := phases.length + 1) hrem]
        rw [Gate.applyVec_smul]
        have hphase_right :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.rightVec =
                Complex.exp (phi * Complex.I) • block.rightVec := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = right := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_even left right (L := phases.length + 1) hrem)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi right) block.rightVec =
            Complex.exp (phi * Complex.I) • block.rightVec
          exact SourceRightKernelSingularBlock.right_phase_on_rightVec block phi
        rw [hphase_right]
        simp [singularSignalRProduct, singularSignalR, rotZ, rotZOp, Matrix.mul_apply,
          smul_smul, mul_comm, mul_assoc]
      · intro hlen
        have hrem : (phases.length + 1) % 2 = 1 := by
          exact hlen
        have htail : phases.length % 2 = 0 := by omega
        have hrem_ne : (phases.length + 1) % 2 ≠ 0 := by omega
        rw [sourceAlternatingPhaseModulation_cons, Gate.mul_applyVec, Gate.mul_applyVec]
        have htail_action :
            (sourceAlternatingPhaseModulation U left right phases).applyVec block.rightVec =
              singularSignalRProduct phases 0 0 0 • block.rightVec :=
          ih.1 htail
        rw [htail_action, Gate.applyVec_smul]
        rw [SourceRightKernelSingularBlock.odd_signal_on_rightVec block
          (remaining := phases.length + 1) hrem_ne]
        rw [Gate.applyVec_smul]
        have hphase_left_perp :
            (projectorPhase phi (sourcePhaseProjector left right (phases.length + 1))).applyVec
              block.leftPerp =
                Complex.exp (-(phi * Complex.I)) • block.leftPerp := by
          have hp : sourcePhaseProjector left right (phases.length + 1) = left := by
            simpa [sourcePhaseProjector] using
              (projectedOutputProjector_of_odd left right (L := phases.length + 1) hrem_ne)
          rw [hp]
          change HilbertOperator.applyVec (projectorPhaseOp phi left) block.leftPerp =
            Complex.exp (-(phi * Complex.I)) • block.leftPerp
          exact SourceRightKernelSingularBlock.left_phase_on_leftPerp block phi
        rw [hphase_left_perp]
        simp [singularSignalRProduct, singularSignalR, rotZ, rotZOp, Matrix.mul_apply,
          smul_smul, mul_comm, mul_assoc]

end SourceRightKernelSingularBlock

/-- The source-level projected block `Π_out U_Φ Π_in` from the singular-value
transformation theorem [GSLW19, BlockHam.tex:768-849]. -/
noncomputable def sourceProjectedBlock {N : Nat} (output input : OrthogonalProjector N)
    (V : Gate (Qubits N)) : HilbertOperator (Qubits N) :=
  output.op * V * input.op

/-- Vectors in the input-projector complement are killed by the projected block
`Π_out V Π_in`. -/
theorem sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support {N : Nat}
    (output input : OrthogonalProjector N) (V : Gate (Qubits N))
    (psi : StateVector (Qubits N))
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement input) psi = psi) :
    HilbertOperator.applyVec (sourceProjectedBlock output input V) psi = 0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self input hpsi]
  simp [HilbertOperator.applyVec]

/-- Applying a Hilbert operator commutes with a list-indexed vector sum. -/
private theorem hilbertOperator_applyVec_list_sum {N : Nat}
    (A : HilbertOperator (Qubits N)) (v : List (StateVector (Qubits N))) :
    HilbertOperator.applyVec A v.sum =
      (v.map fun psi => HilbertOperator.applyVec A psi).sum := by
  induction v with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons psi rest ih =>
      simp [HilbertOperator.applyVec_add, ih]

/-- If two Hilbert operators agree on an indexed family, they agree on every
finite linear combination of that family. -/
private theorem hilbertOperator_applyVec_eq_on_list_linearCombination {N : Nat}
    {ι : Type} (vec : ι -> StateVector (Qubits N))
    {A B : HilbertOperator (Qubits N)}
    (h : ∀ i : ι, HilbertOperator.applyVec A (vec i) =
      HilbertOperator.applyVec B (vec i))
    (terms : List (ℂ × ι)) :
    HilbertOperator.applyVec A ((terms.map fun term => term.1 • vec term.2).sum) =
      HilbertOperator.applyVec B ((terms.map fun term => term.1 • vec term.2).sum) := by
  induction terms with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons term rest ih =>
      rcases term with ⟨c, i⟩
      simp [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul, h i, ih]

namespace SourceLeftKernelSingularBlock

/-- Left-kernel input-side vectors lie in the right-projector complement, hence
the source projected block kills them. -/
theorem sourceProjectedBlock_applyVec_rightPerp_eq_zero {N : Nat}
    {U : Gate (Qubits N)} {left right output : OrthogonalProjector N}
    (block : SourceLeftKernelSingularBlock U left right)
    (V : Gate (Qubits N)) :
    HilbertOperator.applyVec (sourceProjectedBlock output right V) block.rightPerp = 0 :=
  sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support output right V
    block.rightPerp block.right_perp_support

end SourceLeftKernelSingularBlock

namespace SourceComplementSingularBlock

/-- Fully complementary input-side vectors lie in the right-projector complement,
hence the source projected block kills them. -/
theorem sourceProjectedBlock_applyVec_rightPerp_eq_zero {N : Nat}
    {U : Gate (Qubits N)} {left right output : OrthogonalProjector N}
    (block : SourceComplementSingularBlock U left right)
    (V : Gate (Qubits N)) :
    HilbertOperator.applyVec (sourceProjectedBlock output right V) block.rightPerp = 0 :=
  sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support output right V
    block.rightPerp block.right_perp_support

end SourceComplementSingularBlock

/-- Source-level singular-value correctness target for `U_Φ`, before adding the
one-ancilla controlled implementation used by the public real-polynomial
statement [GSLW19, BlockHam.tex:768-849]. -/
def SourceProjectedQSVTBlockCorrectness {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (phases : List ℝ) : Prop :=
  sourceProjectedBlock (projectedOutputProjector left right L) right
      (sourceAlternatingPhaseModulation U left right phases) =
    singularValuePolynomial right L P (projectedUnitaryBlock left right U)

/-- Degree-one base case of the source-level projected QSVT theorem.  The
single zero phase realizes the original projected block, corresponding to
`P(X)=X`. -/
theorem sourceProjectedQSVTBlockCorrectness_X_single_zero {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) :
    SourceProjectedQSVTBlockCorrectness U left right 1 (Polynomial.X : Polynomial ℂ) [0] := by
  unfold SourceProjectedQSVTBlockCorrectness sourceProjectedBlock
  simp [sourceAlternatingPhaseModulation, sourcePhaseProjector, projectedOutputProjector,
    sourcePhaseSignal, singularValuePolynomial_X_one, projectedUnitaryBlock]

/-- Degree-zero source-level projected QSVT sanity case: the empty phase sequence
realizes the constant polynomial `1` on the input projector. -/
theorem sourceProjectedQSVTBlockCorrectness_one_nil {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) :
    SourceProjectedQSVTBlockCorrectness U left right 0 (Polynomial.C 1 : Polynomial ℂ) [] := by
  unfold SourceProjectedQSVTBlockCorrectness sourceProjectedBlock singularValuePolynomial
    evenSingularValuePolynomial polynomialOperator
  simp [sourceAlternatingPhaseModulation, projectedOutputProjector,
    projectedUnitaryBlock, right.idempotent]

/-- Negate every source phase.  The controlled real-polynomial construction uses
the direct sum of `U_Φ` and `U_{-Φ}` [GSLW19, BlockHam.tex:851-887]. -/
def negPhases (phases : List ℝ) : List ℝ :=
  phases.map fun phi => -phi

@[simp]
theorem negPhases_length (phases : List ℝ) :
    (negPhases phases).length = phases.length := by
  simp [negPhases]

theorem singularSignalRProduct_negPhases_zero_zero (phases : List ℝ) (x : ℝ) :
    singularSignalRProduct (negPhases phases) x 0 0 =
      star (singularSignalRProduct phases x 0 0) := by
  simpa [negPhases] using singularSignalRProduct_map_neg_zero_zero phases x

theorem phaseProduct_negPhases (phases : List ℝ) :
    phaseProduct (negPhases phases) = star (phaseProduct phases) := by
  induction phases with
  | nil =>
      simp [negPhases]
  | cons phi phases ih =>
      simp only [negPhases, List.map_cons, phaseProduct_cons]
      change Complex.exp ((-phi : ℝ) * Complex.I) *
          phaseProduct (negPhases phases) =
        star (Complex.exp (phi * Complex.I) * phaseProduct phases)
      rw [ih]
      rw [star_mul]
      rw [mul_comm (star (phaseProduct phases)) (star (Complex.exp (phi * Complex.I)))]
      have hexp :
          star (Complex.exp (phi * Complex.I)) =
            Complex.exp ((-phi : ℝ) * Complex.I) := by
        simpa using conj_exp_I phi
      rw [hexp]

/-- Controlled direct sum of the source-level phase sequences `U_Φ` and
`U_{-Φ}` used by the matching-parity real-polynomial corollary
[GSLW19, BlockHam.tex:851-887]. -/
noncomputable def sourceRealProjectedGate {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) : Gate (Qubits (1 + N)) :=
  phaseControlledDirectSum
    (sourceAlternatingPhaseModulation U left right phases)
    (sourceAlternatingPhaseModulation U left right (negPhases phases))

/-- The `|+⟩` block of the controlled real-projected gate is the average of
the source phase sequence and its negated-phase companion. -/
theorem phasePlusBlock_sourceRealProjectedGate {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    phasePlusBlock (sourceRealProjectedGate U left right phases) =
      (1 / 2 : ℂ) •
          (sourceAlternatingPhaseModulation U left right phases : HilbertOperator (Qubits N)) +
        (1 / 2 : ℂ) •
          (sourceAlternatingPhaseModulation U left right (negPhases phases) :
            HilbertOperator (Qubits N)) := by
  simp [sourceRealProjectedGate, phasePlusBlock_phaseControlledDirectSum]

/-- Projected form of `phasePlusBlock_sourceRealProjectedGate`. -/
theorem projectedPhasePlusBlock_sourceRealProjectedGate {N : Nat}
    (U : Gate (Qubits N)) (output input left right : OrthogonalProjector N)
    (phases : List ℝ) :
    projectedPhasePlusBlock output input (sourceRealProjectedGate U left right phases) =
      output.op *
        ((1 / 2 : ℂ) •
            (sourceAlternatingPhaseModulation U left right phases :
              HilbertOperator (Qubits N)) +
          (1 / 2 : ℂ) •
            (sourceAlternatingPhaseModulation U left right (negPhases phases) :
              HilbertOperator (Qubits N))) *
        input.op := by
  simp [projectedPhasePlusBlock, phasePlusBlock_sourceRealProjectedGate]

@[simp]
theorem sourcePhaseSignal_of_odd {N : Nat} (U : Gate (Qubits N)) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    sourcePhaseSignal U remaining = U := by
  rw [sourcePhaseSignal, if_neg hremaining]

@[simp]
theorem sourcePhaseSignal_of_even {N : Nat} (U : Gate (Qubits N)) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    sourcePhaseSignal U remaining = U.conjTranspose := by
  rw [sourcePhaseSignal, if_pos hremaining]

@[simp]
theorem liftSourcePhaseSignal_of_odd {N : Nat} (U : Gate (Qubits N)) {remaining : ℕ}
    (hremaining : remaining % 2 ≠ 0) :
    liftSourcePhaseSignal U remaining = liftSignalGate U := by
  simp [liftSourcePhaseSignal, hremaining]

@[simp]
theorem liftSourcePhaseSignal_of_even {N : Nat} (U : Gate (Qubits N)) {remaining : ℕ}
    (hremaining : remaining % 2 = 0) :
    liftSourcePhaseSignal U remaining = liftSignalGate U.conjTranspose := by
  simp [liftSourcePhaseSignal, hremaining]

/-- Gate-level alternating phase modulation word over a projected-unitary
encoding, following Definition `def:phaseSeq` in the source. -/
noncomputable def alternatingPhaseModulation {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) : List ℝ → Gate (Qubits (1 + N))
  | [] => 1
  | phi :: phases =>
      projectorPhaseGate phi (sourcePhaseProjector left right (phases.length + 1))
        * liftSourcePhaseSignal U (phases.length + 1)
        * alternatingPhaseModulation U left right phases

/-! ### Projected QSVT circuit spine -/

/-- Resource counters for the projected QSVT theorem of [GSLW19,
BlockHam.tex:768-887].  These are intentionally more specific than the generic
`ResourceProfile`: the public statement distinguishes signal-oracle queries,
projector-controlled-NOT queries, controlled phase gates, and the single phase
ancilla. -/
structure ProjectedResourceProfile where
  /-- Trusted count of signal-oracle queries. -/
  signalQueries : ℕ
  /-- Trusted count of left-projector controlled-not queries. -/
  leftProjectorControlledNotQueries : ℕ
  /-- Trusted count of right-projector controlled-not queries. -/
  rightProjectorControlledNotQueries : ℕ
  /-- Trusted count of controlled phase gates. -/
  controlledPhaseGates : ℕ
  /-- Ancilla qubits used by the projected construction. -/
  ancillaQubits : ℕ
deriving DecidableEq

namespace ProjectedResourceProfile

/-- The exact projected-QSVT resource profile for a phase list of length `L`. -/
def ofLength (L : ℕ) : ProjectedResourceProfile where
  signalQueries := L
  leftProjectorControlledNotQueries := L
  rightProjectorControlledNotQueries := L
  controlledPhaseGates := L
  ancillaQubits := 1

/-- Exact counter claim used by the projected QSVT endpoint. -/
def HasExactCounts (profile : ProjectedResourceProfile) (L : ℕ) : Prop :=
  profile.signalQueries = L ∧
    profile.leftProjectorControlledNotQueries = L ∧
    profile.rightProjectorControlledNotQueries = L ∧
    profile.controlledPhaseGates = L ∧
    profile.ancillaQubits = 1

@[simp]
theorem ofLength_hasExactCounts (L : ℕ) :
    HasExactCounts (ofLength L) L := by
  simp [HasExactCounts, ofLength]

end ProjectedResourceProfile

/-- Circuit wrapper for the source-aligned real projected-QSVT controlled
construction.  The matrix is the controlled direct sum of `U_Φ` and `U_{-Φ}`,
and the resource counters are tied to the same phase list [GSLW19,
BlockHam.tex:851-887]. -/
noncomputable def sourceRealProjectedCircuit {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) : Circuit (Qubits (1 + N)) :=
  { history := CircuitHistory.atom "qsvt-real-projected"
    matrix := sourceRealProjectedGate U left right phases
    resources := { ResourceProfile.zero with
      oracleQueries := phases.length
      elementaryGates := phases.length }
    depth := phases.length
    queryDepth := phases.length }

@[simp]
theorem sourceRealProjectedCircuit_matrix {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((sourceRealProjectedCircuit U left right phases).matrix :
        HilbertOperator (Qubits (1 + N))) =
      sourceRealProjectedGate U left right phases := rfl

theorem sourceRealProjectedCircuit_resourceProfile {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ResourceProfile.HasExactCounts
      (sourceRealProjectedCircuit U left right phases).resources
      phases.length 0 phases.length 0 := by
  simp [sourceRealProjectedCircuit, ResourceProfile.HasExactCounts,
    ResourceProfile.zero]

theorem sourceRealProjectedCircuit_matrix_and_resources {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((sourceRealProjectedCircuit U left right phases).matrix :
        HilbertOperator (Qubits (1 + N))) =
          sourceRealProjectedGate U left right phases ∧
      ProjectedResourceProfile.HasExactCounts
        (ProjectedResourceProfile.ofLength phases.length) phases.length ∧
      ResourceProfile.HasExactCounts
        (sourceRealProjectedCircuit U left right phases).resources
        phases.length 0 phases.length 0 := by
  exact ⟨rfl, ProjectedResourceProfile.ofLength_hasExactCounts phases.length,
    sourceRealProjectedCircuit_resourceProfile U left right phases⟩

/-- Public-real projected-QSVT correctness target: the `|+⟩` block of the same
counted circuit equals the singular-value polynomial target
[GSLW19, BlockHam.tex:851-887]. -/
def RealProjectedQSVTBlockCorrectness {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (phases : List ℝ) : Prop :=
  projectedPhasePlusBlock (projectedOutputProjector left right L) right
      (sourceRealProjectedCircuit U left right phases).matrix =
    singularValuePolynomial right L P (projectedUnitaryBlock left right U)

-- CSLib weak-linter exception: this sanity-case proof intentionally expands
-- the source alternating modulation before applying the averaging identity.
set_option linter.flexible false in
/-- Degree-one base case for the public-real projected QSVT circuit. -/
theorem realProjectedQSVTBlockCorrectness_X_single_zero {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) :
    RealProjectedQSVTBlockCorrectness U left right 1 (Polynomial.X : Polynomial ℂ) [0] := by
  unfold RealProjectedQSVTBlockCorrectness
  change projectedPhasePlusBlock (projectedOutputProjector left right 1) right
      (sourceRealProjectedGate U left right [0]) =
    singularValuePolynomial right 1 (Polynomial.X : Polynomial ℂ)
      (projectedUnitaryBlock left right U)
  rw [projectedPhasePlusBlock_sourceRealProjectedGate]
  simp [negPhases, sourceAlternatingPhaseModulation, sourcePhaseProjector,
    projectedOutputProjector, sourcePhaseSignal, singularValuePolynomial_X_one,
    projectedUnitaryBlock]
  have havg :
      (2 : ℂ)⁻¹ • (U : HilbertOperator (Qubits N)) +
          (2 : ℂ)⁻¹ • (U : HilbertOperator (Qubits N)) =
        (U : HilbertOperator (Qubits N)) := by
    ext i j
    simp [smul_eq_mul]
    ring
  rw [havg]

-- CSLib weak-linter exception: this sanity-case proof intentionally expands
-- the source alternating modulation before applying the averaging identity.
set_option linter.flexible false in
/-- Degree-zero real-projected sanity case. -/
theorem realProjectedQSVTBlockCorrectness_one_nil {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) :
    RealProjectedQSVTBlockCorrectness U left right 0 (Polynomial.C 1 : Polynomial ℂ) [] := by
  unfold RealProjectedQSVTBlockCorrectness
  change projectedPhasePlusBlock (projectedOutputProjector left right 0) right
      (sourceRealProjectedGate U left right []) =
    singularValuePolynomial right 0 (Polynomial.C 1 : Polynomial ℂ)
      (projectedUnitaryBlock left right U)
  rw [projectedPhasePlusBlock_sourceRealProjectedGate]
  simp [negPhases, sourceAlternatingPhaseModulation, projectedOutputProjector,
    singularValuePolynomial, evenSingularValuePolynomial, polynomialOperator,
    projectedUnitaryBlock, right.idempotent]
  have havg :
      (2 : ℂ)⁻¹ • (1 : HilbertOperator (Qubits N)) +
          (2 : ℂ)⁻¹ • (1 : HilbertOperator (Qubits N)) =
        (1 : HilbertOperator (Qubits N)) := by
    ext i j
    simp [smul_eq_mul]
    ring
  rw [havg, Matrix.mul_one, right.idempotent]

/-- Transfer two source-level singular-value transformations, for `Φ` and
`-Φ`, into the controlled real-polynomial projected-QSVT endpoint.  The remaining
polynomial-side condition is exactly the averaged target supplied by the
matching-parity real-polynomial corollary [GSLW19, BlockHam.tex:851-887]. -/
theorem realProjectedQSVTBlockCorrectness_of_source_average {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (L : ℕ) (P Pneg Preal : Polynomial ℂ) (phases : List ℝ)
    (hpos : SourceProjectedQSVTBlockCorrectness U left right L P phases)
    (hneg : SourceProjectedQSVTBlockCorrectness U left right L Pneg (negPhases phases))
    (havg :
      (1 / 2 : ℂ) •
          singularValuePolynomial right L P (projectedUnitaryBlock left right U) +
        (1 / 2 : ℂ) •
          singularValuePolynomial right L Pneg (projectedUnitaryBlock left right U) =
        singularValuePolynomial right L Preal (projectedUnitaryBlock left right U)) :
    RealProjectedQSVTBlockCorrectness U left right L Preal phases := by
  unfold RealProjectedQSVTBlockCorrectness
  change projectedPhasePlusBlock (projectedOutputProjector left right L) right
      (sourceRealProjectedGate U left right phases) =
    singularValuePolynomial right L Preal (projectedUnitaryBlock left right U)
  rw [projectedPhasePlusBlock_sourceRealProjectedGate]
  unfold SourceProjectedQSVTBlockCorrectness sourceProjectedBlock at hpos hneg
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hpos, hneg, havg]

/-- Same-circuit realization package for the public-real projected QSVT endpoint.
The block equality and both resource records are attached to one
`sourceRealProjectedCircuit`. -/
structure RealProjectedQSVTRealization {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (target : HilbertOperator (Qubits N)) where
  /-- Projected phase list used by the public-real QSVT circuit. -/
  phases : List ℝ
  length_eq : phases.length = L
  /-- Counted circuit carrying the projected-QSVT block equality. -/
  circuit : Circuit (Qubits (1 + N))
  circuit_eq : circuit = sourceRealProjectedCircuit U left right phases
  block_eq : projectedPhasePlusBlock (projectedOutputProjector left right L) right
    circuit.matrix = target
  resources_exact : ProjectedResourceProfile.HasExactCounts
    (ProjectedResourceProfile.ofLength L) L
  circuit_resources : ResourceProfile.HasExactCounts circuit.resources L 0 L 0

namespace RealProjectedQSVTRealization

/-- Build the public-real realization package from a proved block equality for
the canonical source-aligned circuit. -/
noncomputable def ofBlockCorrectness {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ)
    (target : HilbertOperator (Qubits N))
    (hblock : projectedPhasePlusBlock
      (projectedOutputProjector left right phases.length) right
      (sourceRealProjectedCircuit U left right phases).matrix = target) :
    RealProjectedQSVTRealization U left right phases.length target where
  phases := phases
  length_eq := rfl
  circuit := sourceRealProjectedCircuit U left right phases
  circuit_eq := rfl
  block_eq := hblock
  resources_exact := ProjectedResourceProfile.ofLength_hasExactCounts phases.length
  circuit_resources := sourceRealProjectedCircuit_resourceProfile U left right phases

end RealProjectedQSVTRealization

/-- A typed circuit node for one projector-controlled phase block. -/
noncomputable def projectorPhaseCircuit {N : Nat} (phi : ℝ)
    (P : OrthogonalProjector N) : Circuit (Qubits (1 + N)) :=
  Circuit.ofGate "qsvt-projector-phase" (projectorPhaseGate phi P)
    { ResourceProfile.zero with elementaryGates := 1 } 1 0

@[simp]
theorem projectorPhaseCircuit_matrix {N : Nat} (phi : ℝ)
    (P : OrthogonalProjector N) :
    ((projectorPhaseCircuit phi P).matrix : HilbertOperator (Qubits (1 + N))) =
      projectorPhaseGate phi P :=
  rfl

/-- A typed circuit node for one signal-oracle use in the alternating sequence. -/
def liftSignalCircuit {N : Nat} (U : Gate (Qubits N)) : Circuit (Qubits (1 + N)) :=
  Circuit.ofGate "qsvt-signal" (liftSignalGate U)
    { ResourceProfile.zero with oracleQueries := 1 } 1 1

@[simp]
theorem liftSignalCircuit_matrix {N : Nat} (U : Gate (Qubits N)) :
    ((liftSignalCircuit U).matrix : HilbertOperator (Qubits (1 + N))) =
      liftSignalGate U :=
  rfl

/-- A typed circuit node for the source-aligned signal use in one projected-QSVT
phase slot.  The query counter is one whether the slot uses `U` or `U†`. -/
def liftSourcePhaseSignalCircuit {N : Nat} (U : Gate (Qubits N)) (remaining : ℕ) :
    Circuit (Qubits (1 + N)) :=
  Circuit.ofGate "qsvt-signal" (liftSourcePhaseSignal U remaining)
    { ResourceProfile.zero with oracleQueries := 1 } 1 1

@[simp]
theorem liftSourcePhaseSignalCircuit_matrix {N : Nat} (U : Gate (Qubits N))
    (remaining : ℕ) :
    ((liftSourcePhaseSignalCircuit U remaining).matrix : HilbertOperator (Qubits (1 + N))) =
      liftSourcePhaseSignal U remaining :=
  rfl

/-- Circuit-level implementation gadget for alternating phase modulation.  This
one-ancilla circuit implements the projector-controlled phase blocks used for
resource accounting; source-level correctness is carried separately by
`sourceAlternatingPhaseModulation` and `sourceRealProjectedCircuit`. -/
noncomputable def alternatingPhaseCircuit {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) : List ℝ → Circuit (Qubits (1 + N))
  | [] => Circuit.identity (Qubits (1 + N))
  | phi :: phases =>
      Circuit.seq
        (Circuit.seq
          (projectorPhaseCircuit phi (sourcePhaseProjector left right (phases.length + 1)))
          (liftSourcePhaseSignalCircuit U (phases.length + 1)))
        (alternatingPhaseCircuit U left right phases)

@[simp]
theorem alternatingPhaseCircuit_matrix {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) :
    ∀ phases : List ℝ,
      ((alternatingPhaseCircuit U left right phases).matrix :
          HilbertOperator (Qubits (1 + N))) =
        alternatingPhaseModulation U left right phases
  | [] => by
      simp [alternatingPhaseCircuit, alternatingPhaseModulation]
  | phi :: phases => by
      simp [alternatingPhaseCircuit, alternatingPhaseModulation,
        alternatingPhaseCircuit_matrix U left right phases]

/-- Coarse resource binding for the projected-QSVT alternating phase circuit:
the same `Circuit` history whose matrix is `alternatingPhaseModulation` records
one signal query and one controlled phase gate per phase slot.  The more
specific left/right projector-controlled-NOT counters are tracked by
`ProjectedResourceProfile`. -/
theorem alternatingPhaseCircuit_resourceProfile {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) :
    ∀ phases : List ℝ,
      ResourceProfile.HasExactCounts
        (alternatingPhaseCircuit U left right phases).resources
        phases.length 0 phases.length 0
  | [] => by
      simp [alternatingPhaseCircuit, ResourceProfile.HasExactCounts,
        Circuit.identity, ResourceProfile.zero]
  | _ :: phases => by
      have htail := alternatingPhaseCircuit_resourceProfile U left right phases
      simp [alternatingPhaseCircuit, ResourceProfile.HasExactCounts,
        projectorPhaseCircuit, liftSourcePhaseSignalCircuit, Circuit.seq, Circuit.ofGate,
        Circuit.atom, ResourceProfile.sequential, ResourceProfile.zero] at htail ⊢
      omega

/-- Implementation-gadget word bundling the projector-controlled phase circuit
with specialized counters.  It is kept as a resource implementation witness;
the public-real projected theorem uses `sourceRealProjectedCircuit` for the
same-circuit correctness carrier. -/
structure ProjectedQSVTWord {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) where
  /-- Implementation-gadget circuit for the alternating projected-QSVT sequence. -/
  circuit : Circuit (Qubits (1 + N))
  circuit_eq : circuit = alternatingPhaseCircuit U left right phases
  /-- Specialized projected-QSVT counters tied to the same phase list. -/
  resources : ProjectedResourceProfile
  resources_eq : resources = ProjectedResourceProfile.ofLength phases.length

attribute [-simp] ProjectedQSVTWord.mk.injEq
-- Generated structure lemma; keep the `simpNF` exception scoped to this
-- declaration rather than suppressing the linter for the file.
attribute [nolint simpNF] ProjectedQSVTWord.mk.injEq

/-- The canonical projected-QSVT word for a phase sequence. -/
noncomputable def projectedQSVTWord {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ProjectedQSVTWord U left right phases where
  circuit := alternatingPhaseCircuit U left right phases
  circuit_eq := rfl
  resources := ProjectedResourceProfile.ofLength phases.length
  resources_eq := rfl

theorem projectedQSVTWord_matrix {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((projectedQSVTWord U left right phases).circuit.matrix :
        HilbertOperator (Qubits (1 + N))) =
      alternatingPhaseModulation U left right phases := by
  simp [projectedQSVTWord]

theorem projectedQSVTWord_resources_exact {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ProjectedResourceProfile.HasExactCounts
      (projectedQSVTWord U left right phases).resources phases.length := by
  simp [projectedQSVTWord]

/-- The generic `Circuit.resources` counters of the projected word are derived
from the same circuit history as its matrix semantics. -/
theorem projectedQSVTWord_circuitResourceProfile {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ResourceProfile.HasExactCounts
      (projectedQSVTWord U left right phases).circuit.resources
      phases.length 0 phases.length 0 := by
  simpa [projectedQSVTWord] using
    alternatingPhaseCircuit_resourceProfile U left right phases

/-- Same-circuit binding for the projected QSVT word.  The matrix semantics and
the specialized resource counters are both derived from the same constructed
`Circuit`; this is the internal invariant needed by the public QSVT statements
[GSLW19, BlockHam.tex:883-887]. -/
theorem projectedQSVTWord_matrix_and_resources {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    ((projectedQSVTWord U left right phases).circuit.matrix :
        HilbertOperator (Qubits (1 + N))) =
          alternatingPhaseModulation U left right phases ∧
      ProjectedResourceProfile.HasExactCounts
        (projectedQSVTWord U left right phases).resources phases.length ∧
      ResourceProfile.HasExactCounts
        (projectedQSVTWord U left right phases).circuit.resources
        phases.length 0 phases.length 0 := by
  exact ⟨projectedQSVTWord_matrix U left right phases,
    projectedQSVTWord_resources_exact U left right phases,
    projectedQSVTWord_circuitResourceProfile U left right phases⟩

/-- Convert the reflection-QSP phase list into the projected-QSVT phase list
used by the source's singular-value transformation sequence.  For a source
certificate `(φ'_0, ..., φ'_d)`, the projected list is
`φ_1 := φ'_0 + φ'_d + (d-1)π/2` and
`φ_j := φ'_{j-1} - π/2` for `j ≥ 2` [GSLW19, BlockHam.tex:520-528]. -/
noncomputable def projectedPhasesFromQSPCertificate (φ₀ : ℝ) (φs : List ℝ) :
    List ℝ :=
  match φs.reverse with
  | [] => []
  | last :: reversedInit =>
      (φ₀ + last + (((φs.length - 1 : ℕ) : ℝ) * (Real.pi / 2))) ::
        (reversedInit.reverse.map fun φ => φ - Real.pi / 2)

theorem projectedPhasesFromQSPCertificate_length (φ₀ : ℝ) (φs : List ℝ) :
    (projectedPhasesFromQSPCertificate φ₀ φs).length = φs.length := by
  unfold projectedPhasesFromQSPCertificate
  cases hrev : φs.reverse with
  | nil =>
      have hlen := congrArg List.length hrev
      simp [List.length_reverse] at hlen
      simp [hlen]
  | cons last reversedInit =>
      have hlen := congrArg List.length hrev
      simp [List.length_reverse] at hlen ⊢
      omega

/-- The source phase conversion of [GSLW19, BlockHam.tex:523-528], restricted
to the `(0,0)` entry needed by the singular-value transformation proof: the
projected-QSVT `R` product is the raw `R` product with the terminal scalar phase
absorbed into its first phase. -/
theorem singularSignalRProduct_projectedPhases_zero_zero_eq_rawProduct
    (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    singularSignalRProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) x 0 0 =
      Complex.exp (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) * singularSignalRRawProduct φ₀ init x 0 0 := by
  rw [show projectedPhasesFromQSPCertificate φ₀ (init ++ [last]) =
      (φ₀ + last + (init.length : ℝ) * (Real.pi / 2)) ::
        init.map (fun φ => φ - Real.pi / 2) by
        induction init with
        | nil => simp [projectedPhasesFromQSPCertificate]
        | cons phi init ih =>
            simp [projectedPhasesFromQSPCertificate, List.reverse_append]]
  rw [singularSignalRProduct_first_phase_zero_zero
    (φ₀ + last + (init.length : ℝ) * (Real.pi / 2)) (φ₀ - Real.pi / 4)
    (init.map (fun φ => φ - Real.pi / 2)) x]
  have harg :
      ((((φ₀ + last + (init.length : ℝ) * (Real.pi / 2) : ℝ) : ℂ) -
          ((φ₀ - Real.pi / 4 : ℝ) : ℂ)) * Complex.I) =
        (((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) *
          Complex.I) := by
    have hreal :
        (((φ₀ + last + (init.length : ℝ) * (Real.pi / 2) : ℝ) : ℂ) -
          ((φ₀ - Real.pi / 4 : ℝ) : ℂ)) =
        ((last + init.length * (Real.pi / 2) + Real.pi / 4 : ℝ) : ℂ) := by
      norm_num
      ring
    exact congrArg (fun z : ℂ => z * Complex.I) hreal
  rw [harg]
  simp [singularSignalRRawProduct]

/-- The projected-QSVT phase conversion preserves the `(0,0)` scalar entry of
the source `W`-convention QSP certificate [GSLW19, BlockHam.tex:514-528]. -/
theorem singularSignalRProduct_projectedPhases_zero_zero_eq_qspW
    (φ₀ : ℝ) (init : List ℝ) (last x : ℝ) :
    singularSignalRProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) x 0 0 =
      qspW φ₀ (init ++ [last]) x 0 0 := by
  rw [singularSignalRProduct_projectedPhases_zero_zero_eq_rawProduct]
  rw [qspW_zero_zero_eq_rawProduct]

/-- Negating the source projected-QSVT phase list implements the coefficient
conjugate scalar polynomial on the local `R`-signal block.  This is the scalar
half of the real-polynomial averaging step in `cor:matchingParity`
[GSLW19, BlockHam.tex:851-887]. -/
theorem singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
    {d : Nat} {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last x : ℝ)
    (hφs : certificate.φs = init ++ [last])
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    singularSignalRProduct
        (negPhases
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) x 0 0 =
      (conjP P).eval (x : Complex) := by
  rw [singularSignalRProduct_negPhases_zero_zero]
  rw [hφs]
  rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
  have hq : qspW certificate.φ₀ (init ++ [last]) x 0 0 = P.eval (x : Complex) := by
    simpa [hφs] using certificate.qspW_zero_zero hx
  rw [hq]
  rw [conjP_eval_ofReal]
  rfl

-- CSLib weak-linter exception: this list-sum proof uses the existing
-- projected-phase definition shape; the `simp only` variant was brittle.
set_option linter.flexible false in
/-- Phase conversion for the nonempty reflection-QSP phase list.  The source's
projected-QSVT phases have the same scalar product as the `(0,0)` entry of the
corresponding `W`-convention QSP sequence at `x=1` [GSLW19,
BlockHam.tex:520-528,738-849]. -/
theorem phaseProduct_projectedPhases_append_singleton (φ₀ : ℝ)
    (init : List ℝ) (last : ℝ) :
    phaseProduct (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])) =
      Complex.exp (φ₀ * Complex.I) * phaseProduct (init ++ [last]) := by
  have hsum :
      (projectedPhasesFromQSPCertificate φ₀ (init ++ [last])).sum =
        φ₀ + (init ++ [last]).sum := by
    induction init with
    | nil =>
        simp [projectedPhasesFromQSPCertificate]
    | cons phi init ih =>
        simp [projectedPhasesFromQSPCertificate, List.reverse_append]
        rw [list_sum_map_sub_const]
        ring_nf
  rw [phaseProduct_eq_exp_sum, phaseProduct_eq_exp_sum, hsum]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

/-- Nonempty phase-list specialization of the phase conversion: after
projecting a reflection-QSP phase certificate into the source projected-QSVT
phase list, the scalar phase product on a unit singular block is exactly the
certificate's target value at `x=1` [GSLW19, BlockHam.tex:520-528,768-849]. -/
theorem phaseProduct_projectedPhases_eq_certificate_eval_one {d : Nat}
    {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) :
    phaseProduct (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) =
      P.eval (1 : Complex) := by
  rw [hφs, phaseProduct_projectedPhases_append_singleton]
  rw [phaseProduct]
  rw [← qspW_one_zero_zero_eq_phaseProduct]
  simpa [hφs] using certificate.qspW_zero_zero (x := 1) (by norm_num)

theorem phaseProduct_negProjectedPhases_eq_conjP_eval_one {d : Nat}
    {P Q : Polynomial Complex}
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) :
    phaseProduct
        (negPhases
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) =
      (conjP P).eval (1 : Complex) := by
  rw [phaseProduct_negPhases]
  rw [phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]
  simpa using (conjP_eval_ofReal P 1).symm

namespace SourceUnitSingularBlock

/-- Unit singular block, even output side: a nonempty phase certificate drives
the source alternating phase sequence by the scalar `P(1)` on the right vector
[GSLW19, BlockHam.tex:655-671,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    (sourceAlternatingPhaseModulation U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (1 : Complex) • block.rightVec := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact, phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]

/-- Unit singular block, odd output side: a nonempty phase certificate drives
the source alternating phase sequence by the scalar `P(1)` on the left vector
[GSLW19, BlockHam.tex:655-671,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    (sourceAlternatingPhaseModulation U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (1 : Complex) • block.leftVec := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact, phaseProduct_projectedPhases_eq_certificate_eval_one certificate init last hφs]

/-- Unit singular block, even output side after the source projected block:
projecting preserves the right-vector component [GSLW19, BlockHam.tex:655-671,
768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (1 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (1 : Complex) • block.rightVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_even certificate init last hφs hd]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Unit singular block, odd output side after the source projected block:
projecting preserves the left-vector component [GSLW19, BlockHam.tex:655-671,
768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (1 : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (1 : Complex) • block.leftVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_odd certificate init last hφs hd]
  rw [HilbertOperator.applyVec_smul, block.left_support]

/-- Unit singular block, even output side for the negated projected phase list:
the scalar is `(conjP P)(1)`, matching the second half of the source real
averaging construction [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (1 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (1 : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact, phaseProduct_negProjectedPhases_eq_conjP_eval_one certificate init last hφs]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Unit singular block, odd output side for the negated projected phase list
[GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceUnitSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (1 : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (1 : Complex) • block.leftVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact, phaseProduct_negProjectedPhases_eq_conjP_eval_one certificate init last hφs]
  rw [HilbertOperator.applyVec_smul, block.left_support]

end SourceUnitSingularBlock

namespace SourceTwoDimensionalSingularBlock

/-- Nontrivial singular block, even output side: the projected-QSVT phase list
drives the right singular vector with scalar `P(σ)` on the right-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    (sourceAlternatingPhaseModulation U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (block.sigma : Complex) • block.rightVec +
        singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.sigma 1 0 • block.rightPerp := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.sigma 0 0 =
        P.eval (block.sigma : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using
      certificate.qspW_zero_zero (x := block.sigma) block.sigma_mem_unitInterval
  rw [hentry]

/-- Nontrivial singular block, odd output side: the projected-QSVT phase list
drives the right singular vector with scalar `P(σ)` on the left-vector
component [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceAlternating_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    (sourceAlternatingPhaseModulation U left right
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec =
      P.eval (block.sigma : Complex) • block.leftVec +
        singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.sigma 1 0 • block.leftPerp := by
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          block.sigma 0 0 =
        P.eval (block.sigma : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using
      certificate.qspW_zero_zero (x := block.sigma) block.sigma_mem_unitInterval
  rw [hentry]

/-- Nontrivial singular block, even output side after the source projected block:
the perpendicular component is removed by the output projector, leaving the
desired scalar `P(σ)` action [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (block.sigma : Complex) • block.rightVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_even certificate init last hφs hd]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- Nontrivial singular block, odd output side after the source projected block:
the perpendicular component is removed by the output projector, leaving the
desired scalar `P(σ)` action [GSLW19, BlockHam.tex:655-735,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (block.sigma : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (block.sigma : Complex) • block.leftVec
  rw [block.sourceAlternating_projectedPhases_applyVec_rightVec_odd certificate init last hφs hd]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

/-- Nontrivial singular block, even output side for the negated projected phase
list.  The perpendicular component is again removed by the output projector,
leaving `(conjP P)(σ)` [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (block.sigma : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (block.sigma : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          block.sigma 0 0 =
        (conjP P).eval (block.sigma : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last block.sigma hφs block.sigma_mem_unitInterval
  rw [hentry]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.right_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right block.right_perp_support]
  simp

/-- Nontrivial singular block, odd output side for the negated projected phase
list [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceTwoDimensionalSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (block.sigma : Complex) • block.leftVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (block.sigma : Complex) • block.leftVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          block.sigma 0 0 =
        (conjP P).eval (block.sigma : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last block.sigma hφs block.sigma_mem_unitInterval
  rw [hentry]
  rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
    HilbertOperator.applyVec_smul, block.left_support,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

end SourceTwoDimensionalSingularBlock

namespace SourceRightKernelSingularBlock

/-- Right-kernel block, even output side after projection: the scalar is the
source QSP value `P(0)` [GSLW19, BlockHam.tex:599-611,655-716,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      P.eval (0 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) =
    P.eval (0 : Complex) • block.rightVec
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 0 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
          0 0 0 =
        P.eval (0 : Complex) := by
    rw [hφs]
    rw [singularSignalRProduct_projectedPhases_zero_zero_eq_qspW]
    simpa [hφs] using certificate.qspW_zero_zero (x := 0) (by norm_num)
  rw [hentry]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Right-kernel block, odd output side after projection: the local vector lies
in the left complement, so the output projector removes it [GSLW19,
BlockHam.tex:599-611,655-716,768-849]. -/
theorem sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        block.rightVec =
      0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).applyVec
        block.rightVec) = 0
  have hlen :
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length % 2 = 1 := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).2 hlen
  rw [hact]
  rw [HilbertOperator.applyVec_smul,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

/-- Right-kernel block, even output side for the negated projected phase list:
the scalar is `(conjP P)(0)` [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.φs = init ++ [last]) (hd : d % 2 = 0) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      (conjP P).eval (0 : Complex) • block.rightVec := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = right := by
    simpa using projectedOutputProjector_of_even left right (L := d) hd
  rw [hp]
  change HilbertOperator.applyVec right.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) =
    (conjP P).eval (0 : Complex) • block.rightVec
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 0 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).1 hlen
  rw [hact]
  have hentry :
      singularSignalRProduct
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          0 0 0 =
        (conjP P).eval (0 : Complex) :=
    singularSignalRProduct_negProjectedPhases_zero_zero_eq_conjP
      certificate init last 0 hφs (by norm_num)
  rw [hentry]
  rw [HilbertOperator.applyVec_smul, block.right_support]

/-- Right-kernel block, odd output side for the negated projected phase list:
the local vector lies in the left complement, so the output projector removes
it [GSLW19, BlockHam.tex:851-887]. -/
theorem sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
    {N d : Nat} {P Q : Polynomial Complex}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hd : d % 2 = 1) :
    HilbertOperator.applyVec
        (sourceProjectedBlock (projectedOutputProjector left right d) right
          (sourceAlternatingPhaseModulation U left right
            (negPhases
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
        block.rightVec =
      0 := by
  unfold sourceProjectedBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  have hp : projectedOutputProjector left right d = left := by
    simpa using projectedOutputProjector_of_odd left right (L := d) (by omega : d % 2 ≠ 0)
  rw [hp]
  change HilbertOperator.applyVec left.op
      ((sourceAlternatingPhaseModulation U left right
          (negPhases
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).applyVec
        block.rightVec) = 0
  have hlen :
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)).length % 2 = 1 := by
    rw [negPhases_length, projectedPhasesFromQSPCertificate_length,
      certificate.length_eq, hd]
  have hact :=
    (block.sourceAlternating_applyVec_rightVec_singularSignalRProduct_zero
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))).2 hlen
  rw [hact]
  rw [HilbertOperator.applyVec_smul,
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      left block.left_perp_support]
  simp

theorem projectedUnitaryBlock_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) block.rightVec = 0 := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support]
  change HilbertOperator.applyVec left.op (U.applyVec block.rightVec) = 0
  rw [block.U_right]
  exact OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
    left block.left_perp_support

theorem gram_applyVec_rightVec {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        block.rightVec =
      (0 : Complex) • block.rightVec := by
  rw [HilbertOperator.mul_applyVec, block.projectedUnitaryBlock_applyVec_rightVec]
  simp [HilbertOperator.applyVec]

theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      P.eval (0 : Complex) • block.rightVec := by
  unfold singularValuePolynomial evenSingularValuePolynomial
  rw [if_pos hL]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, block.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (0 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.right_support]
  have heven := evenSquareQuotient_eval_sq_of_hasParity hL hP (0 : Complex)
  have heven0 :
      (evenSquareQuotient P).eval (0 : Complex) = P.eval (0 : Complex) := by
    simpa using heven
  rw [heven0]

theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (block : SourceRightKernelSingularBlock U left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (_hP : HasParity P L) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U))
        block.rightVec =
      0 := by
  unfold singularValuePolynomial oddSingularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  rw [if_neg hnot]
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U)
      (0 : Complex) block.rightVec block.gram_applyVec_rightVec,
    HilbertOperator.applyVec_smul, block.projectedUnitaryBlock_applyVec_rightVec]
  simp

end SourceRightKernelSingularBlock

/- The singular-value theorem will be finished by proving
`SourceProjectedQSVTBlockCorrectness` directly from the source invariant-block
decomposition.  A previous matrix-entry-shaped interface was deliberately
removed here: individual standard-basis entries are not, in general, evaluations
of one singular value. -/

/-- Correct source-facing assembly point for `lemma:singInvDec` followed by
`thm:singValTransformation`: the local singular-block decomposition is recorded
separately from the final block equality.  Unlike a standard matrix-entry
interface, this shape matches the source proof, which works in the invariant
singular-vector blocks before assembling the operator equality [GSLW19,
BlockHam.tex:655-736,768-849]. -/
structure SourceSingularInvariantBlockAssembly {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate :
      ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) where
  /-- Source singular-invariant decomposition used for the blockwise proof. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  block_correctness :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

/-- Once the invariant-block assembly proves the projected block equality, it
feeds the source-level QSVT target directly.  The remaining hard work is to
construct the assembly from the blockwise scalar-QSP proof, not from standard
matrix entries [GSLW19, BlockHam.tex:655-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_invariantBlockAssembly {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate :
      ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (assembly : SourceSingularInvariantBlockAssembly U left right certificate) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  assembly.block_correctness

/-- Extensional assembly contract for the final step of
`thm:singValTransformation`: a source invariant-vector family is sufficient if
it spans by operator action and each vector satisfies the local projected-QSVT
action equality [GSLW19, BlockHam.tex:655-736,768-849]. -/
structure SourceProjectedQSVTSpanningFamily {N d : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (P : Polynomial ℂ) (phases : List ℝ) where
  /-- Index type for source invariant vectors. -/
  ι : Type
  /-- Source invariant vector selected by an index. -/
  vec : ι -> StateVector (Qubits N)
  ext :
    ∀ {A B : HilbertOperator (Qubits N)},
      (∀ i : ι, HilbertOperator.applyVec A (vec i) =
        HilbertOperator.applyVec B (vec i)) -> A = B
  action_eq :
    ∀ i : ι,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right phases))
          (vec i) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec i)

/-- Basis-span form of the source invariant-vector family.  Instead of asking
for an abstract operator-extensionality proof, it records a finite family of
vectors and a decomposition of every Gram-eigenbasis vector into that family.
This is the form closest to `lemma:singInvDec` when zero singular subspaces are
split into projector and complement parts [GSLW19, BlockHam.tex:583-613,
655-736,768-849]. -/
structure SourceProjectedQSVTBasisSpanFamily {N d : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (P : Polynomial ℂ) (phases : List ℝ) where
  /-- Index type for the source vectors spanning the Gram eigenbasis. -/
  ι : Type
  /-- Source vector selected by an index. -/
  vec : ι -> StateVector (Qubits N)
  /-- Finite linear combination of source vectors for each Gram-eigenbasis vector. -/
  combination : (Qubits N).Index -> List (ℂ × ι)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          StateVector (Qubits N)) =
        ((combination i).map fun term => term.1 • vec term.2).sum
  action_eq :
    ∀ i : ι,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right phases))
          (vec i) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec i)

/-- A basis-span source family gives the abstract spanning-family contract. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfBasisSpanFamily {N d : Nat}
    {P : Polynomial ℂ} {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    {phases : List ℝ}
    (family : SourceProjectedQSVTBasisSpanFamily (d := d) U left right P phases) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P phases where
  ι := family.ι
  vec := family.vec
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [family.basis_eq i]
    exact hilbertOperator_applyVec_eq_on_list_linearCombination family.vec h
      (family.combination i)
  action_eq := family.action_eq

/-- Convert a source invariant-vector spanning family into the global projected
QSVT block equality.  The remaining source work is to build this family from
`lemma:singInvDec`'s unit, nontrivial, kernel, and complement sectors. -/
theorem sourceProjectedQSVTBlockCorrectness_of_spanningFamily {N d : Nat}
    {P : Polynomial ℂ} (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (phases : List ℝ)
    (family : SourceProjectedQSVTSpanningFamily (d := d) U left right P phases) :
    SourceProjectedQSVTBlockCorrectness U left right d P phases := by
  unfold SourceProjectedQSVTBlockCorrectness
  exact family.ext family.action_eq

/-- Basis-span source families prove the global projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily {N d : Nat}
    {P : Polynomial ℂ} (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (phases : List ℝ)
    (family : SourceProjectedQSVTBasisSpanFamily (d := d) U left right P phases) :
    SourceProjectedQSVTBlockCorrectness U left right d P phases :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right phases
    (sourceProjectedQSVTSpanningFamilyOfBasisSpanFamily (d := d) family)

/-- The tagged source-side input vectors from `lemma:singInvDec`: right singular
vectors for unit, nontrivial, and right-kernel sectors, and right-complement
vectors for the nontrivial, left-kernel, and fully complementary sectors
[GSLW19, BlockHam.tex:583-613,655-736]. -/
inductive SourceSingularInvariantVector {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (decomposition : SourceSingularInvariantDecomposition U left right) : Type where
  | unit : Fin decomposition.unitBlockCount -> SourceSingularInvariantVector decomposition
  | twoRight :
      Fin decomposition.twoDimensionalBlockCount -> SourceSingularInvariantVector decomposition
  | twoRightPerp :
      Fin decomposition.twoDimensionalBlockCount -> SourceSingularInvariantVector decomposition
  | rightKernel :
      Fin decomposition.rightKernelBlockCount -> SourceSingularInvariantVector decomposition
  | leftKernel :
      Fin decomposition.leftKernelBlockCount -> SourceSingularInvariantVector decomposition
  | complement :
      Fin decomposition.complementBlockCount -> SourceSingularInvariantVector decomposition
deriving Fintype

namespace SourceSingularInvariantVector

/-- The actual source input vector represented by a sector tag. -/
def vec {N : Nat} {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right} :
    SourceSingularInvariantVector decomposition -> StateVector (Qubits N)
  | unit i => (decomposition.unitBlock i).rightVec
  | twoRight i => (decomposition.twoDimensionalBlock i).rightVec
  | twoRightPerp i => (decomposition.twoDimensionalBlock i).rightPerp
  | rightKernel i => (decomposition.rightKernelBlock i).rightVec
  | leftKernel i => (decomposition.leftKernelBlock i).rightPerp
  | complement i => (decomposition.complementBlock i).rightPerp

end SourceSingularInvariantVector

/-- Source-side local invariant vectors, carrying the actual block certificate
instead of a count-indexed decomposition.  This is the direct Lean analogue of
the block list produced by `lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,
655-736]. -/
inductive SourceSingularInvariantLocalVector {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) : Type where
  | unit : SourceUnitSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | twoRight : SourceTwoDimensionalSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | twoRightPerp : SourceTwoDimensionalSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | rightKernel : SourceRightKernelSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | leftKernel : SourceLeftKernelSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | complement : SourceComplementSingularBlock U left right ->
      SourceSingularInvariantLocalVector U left right
  | inputComplement (rightPerp : StateVector (Qubits N))
      (right_perp_support :
        HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
          rightPerp) :
      SourceSingularInvariantLocalVector U left right

namespace SourceSingularInvariantLocalVector

/-- The source input vector represented by a local block tag. -/
def vec {N : Nat} {U : Gate (Qubits N)} {left right : OrthogonalProjector N} :
    SourceSingularInvariantLocalVector U left right -> StateVector (Qubits N)
  | unit block => block.rightVec
  | twoRight block => block.rightVec
  | twoRightPerp block => block.rightPerp
  | rightKernel block => block.rightVec
  | leftKernel block => block.rightPerp
  | complement block => block.rightPerp
  | inputComplement rightPerp _ => rightPerp

/-- Forget a count-indexed source sector tag into the corresponding local block
tag.  This lets the source direct-sum theorem feed the later local-sector
coverage interface without duplicating action proofs. -/
def ofDecompositionVector {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right} :
    SourceSingularInvariantVector decomposition ->
      SourceSingularInvariantLocalVector U left right
  | SourceSingularInvariantVector.unit i =>
      SourceSingularInvariantLocalVector.unit (decomposition.unitBlock i)
  | SourceSingularInvariantVector.twoRight i =>
      SourceSingularInvariantLocalVector.twoRight (decomposition.twoDimensionalBlock i)
  | SourceSingularInvariantVector.twoRightPerp i =>
      SourceSingularInvariantLocalVector.twoRightPerp (decomposition.twoDimensionalBlock i)
  | SourceSingularInvariantVector.rightKernel i =>
      SourceSingularInvariantLocalVector.rightKernel (decomposition.rightKernelBlock i)
  | SourceSingularInvariantVector.leftKernel i =>
      SourceSingularInvariantLocalVector.leftKernel (decomposition.leftKernelBlock i)
  | SourceSingularInvariantVector.complement i =>
      SourceSingularInvariantLocalVector.complement (decomposition.complementBlock i)

@[simp]
theorem vec_ofDecompositionVector {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right}
    (tag : SourceSingularInvariantVector decomposition) :
    vec (ofDecompositionVector (U := U) (left := left) (right := right) tag) =
      SourceSingularInvariantVector.vec tag := by
  cases tag <;> rfl

/-- Local source-sector action equality for every invariant vector in
`lemma:singInvDec`, after the W-to-R phase conversion has produced the projected
phase list [GSLW19, BlockHam.tex:655-736,768-849]. -/
theorem action_eq {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    ∀ tag : SourceSingularInvariantLocalVector U left right,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
          (vec tag) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
          (vec tag) := by
  intro tag
  cases tag with
  | unit block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · rw [
          SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        rw [
          SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | twoRight block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | twoRightPerp block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
            block.rightPerp block.right_perp_support
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | rightKernel block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block P hd hP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd block certificate hdodd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block P hdodd hP]
  | leftKernel block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (sourceAlternatingPhaseModulation U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | complement block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp = 0 :=
          SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (sourceAlternatingPhaseModulation U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P block.right_perp_support]
  | inputComplement rightPerp hright_perp =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
            rightPerp hright_perp
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
              rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) P hright_perp]

/-- Local source-sector action equality for the negated projected phase list.
This is the source-level half of the `U_{-Φ}` branch used in
`cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
theorem action_eq_negProjectedPhases {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    ∀ tag : SourceSingularInvariantLocalVector U left right,
      HilbertOperator.applyVec
          (sourceProjectedBlock (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
          (vec tag) =
        HilbertOperator.applyVec
          (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
          (vec tag) := by
  intro tag
  cases tag with
  | unit block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · rw [
          SourceUnitSingularBlock.sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        rw [
          SourceUnitSingularBlock.sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | twoRight block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceTwoDimensionalSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd
            block certificate init last hφs hdodd,
          SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | twoRightPerp block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            block.rightPerp block.right_perp_support
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | rightKernel block =>
      dsimp [vec]
      by_cases hd : d % 2 = 0
      · open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_even
            block certificate init last hφs hd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
            block (conjP P) hd hP.conjP]
      · have hdodd : d % 2 = 1 := by omega
        open SourceRightKernelSingularBlock in
        rw [
          sourceProjectedBlock_negProjectedPhases_applyVec_rightVec_odd block certificate hdodd,
          SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
            block (conjP P) hdodd hP.conjP]
  | leftKernel block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (sourceAlternatingPhaseModulation U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | complement block =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            block.rightPerp = 0 :=
          SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
            block
            (sourceAlternatingPhaseModulation U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              block.rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) block.right_perp_support]
  | inputComplement rightPerp hright_perp =>
      dsimp [vec]
      calc
        HilbertOperator.applyVec
            (sourceProjectedBlock (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (negPhases
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))))
            rightPerp = 0 :=
          sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
            (projectedOutputProjector left right d) right
            (sourceAlternatingPhaseModulation U left right
              (negPhases
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
            rightPerp hright_perp
        _ =
            HilbertOperator.applyVec
              (singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U))
              rightPerp := by
          rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
            (left := left) (right := right) (U := U) (conjP P) hright_perp]

end SourceSingularInvariantLocalVector

/-- Basis-span coverage using directly carried source local blocks. -/
structure SourceSingularInvariantLocalBasisSpanCoverage {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Linear-combination coverage of every Gram-eigenbasis vector by local sectors. -/
  combination :
    (Qubits N).Index -> List (ℂ × SourceSingularInvariantLocalVector U left right)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          StateVector (Qubits N)) =
        ((combination i).map fun term =>
          term.1 • SourceSingularInvariantLocalVector.vec term.2).sum

/-- Coverage by an orthonormal basis whose vectors are all source local sectors.
This is the closest Lean interface to the source proof after the orthogonality
checks in Table 2 and the final orthogonal-complement construction
[GSLW19, BlockHam.tex:615-736]. -/
structure SourceSingularInvariantLocalOrthonormalBasisCoverage {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Index type for the orthonormal source-sector basis. -/
  ι : Type
  /-- Finiteness instance for the orthonormal source-sector basis. -/
  fintype : Fintype ι
  /-- Orthonormal basis whose vectors are tagged by source sectors. -/
  basis : OrthonormalBasis ι ℂ (StateVector (Qubits N))
  /-- Source-sector tag attached to each basis vector. -/
  tag : ι -> SourceSingularInvariantLocalVector U left right
  tag_vec_eq : ∀ i : ι, SourceSingularInvariantLocalVector.vec (tag i) = basis i

/-- Count-indexed source sectors form an orthonormal direct-sum decomposition.
This is the precise Lean obligation left by the orthogonality table and final
orthogonal-complement paragraph of `lemma:singInvDec` [GSLW19,
BlockHam.tex:615-736]. -/
structure SourceSingularInvariantOrthonormalDecomposition {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) where
  /-- Count-indexed source singular-invariant sector decomposition. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  orthonormal :
    Orthonormal ℂ
      (SourceSingularInvariantVector.vec (decomposition := decomposition))
  spans :
    ⊤ ≤ Submodule.span ℂ
      (Set.range
        (SourceSingularInvariantVector.vec (decomposition := decomposition)))

/-- An orthonormal source direct-sum decomposition supplies the local-sector
orthonormal coverage interface used by projected QSVT. -/
noncomputable def SourceSingularInvariantOrthonormalDecomposition.toLocalCoverage
    {N : Nat} {U : Gate (Qubits N)} {left right : OrthogonalProjector N}
    (coverage :
      SourceSingularInvariantOrthonormalDecomposition U left right) :
    SourceSingularInvariantLocalOrthonormalBasisCoverage U left right where
  ι := SourceSingularInvariantVector coverage.decomposition
  fintype := inferInstance
  basis := OrthonormalBasis.mk coverage.orthonormal coverage.spans
  tag := SourceSingularInvariantLocalVector.ofDecompositionVector
  tag_vec_eq := by
    intro i
    rw [SourceSingularInvariantLocalVector.vec_ofDecompositionVector]
    exact (OrthonormalBasis.coe_mk coverage.orthonormal coverage.spans).symm ▸ rfl

/-- An orthonormal source local-sector basis gives the generic spanning-family
contract for projected QSVT. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfLocalOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) := by
  letI : Fintype coverage.ι := coverage.fintype
  refine
    { ι := coverage.ι
      vec := fun i => coverage.basis i
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis coverage.basis h
  · intro i
    rw [← coverage.tag_vec_eq i]
    exact SourceSingularInvariantLocalVector.action_eq U left right certificate hP
      init last hφs (coverage.tag i)

/-- An orthonormal source local-sector basis proves the source-level projected
QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_localOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTSpanningFamilyOfLocalOrthonormalBasisCoverage
      U left right certificate hP coverage init last hφs)

/-- A source orthonormal direct-sum decomposition proves the source-level
projected QSVT block equality.  This is the compact handoff target for
`lemma:singInvDec` [GSLW19, BlockHam.tex:615-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_orthonormalDecomposition
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localOrthonormalBasisCoverage
    U left right certificate hP coverage.toLocalCoverage init last hφs

/-- The same source orthonormal direct-sum decomposition also proves the
negated-phase source-level block equality for the coefficient-conjugate
polynomial.  This is the local-sector lift needed by the averaging step in
`cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def
    sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfLocalOrthonormalBasisCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalOrthonormalBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) := by
  letI : Fintype coverage.ι := coverage.fintype
  refine
    { ι := coverage.ι
      vec := fun i => coverage.basis i
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis coverage.basis h
  · intro i
    rw [← coverage.tag_vec_eq i]
    exact SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs (coverage.tag i)

/-- Negated-phase source block equality for a completed orthonormal source
direct-sum decomposition [GSLW19, BlockHam.tex:615-736,851-887]. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_orthonormalDecomposition
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfLocalOrthonormalBasisCoverage
      U left right certificate hP coverage.toLocalCoverage init last hφs)

/-- The local source-sector vector attached to a nonzero Gram eigenbasis vector:
it is either the unit singular block or the right vector of a two-dimensional
singular block, according to the source `σ=1` / `0<σ<1` split
[GSLW19, BlockHam.tex:583-613,655-735]. -/
noncomputable def sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalVector U left right :=
  match projectedUnitaryBlockNonzeroClassifiedSingularBlock left right U i hlambda with
  | SourceNonzeroClassifiedSingularBlock.unitBlock block =>
      SourceSingularInvariantLocalVector.unit block
  | SourceNonzeroClassifiedSingularBlock.twoDimensionalBlock block =>
      SourceSingularInvariantLocalVector.twoRight block

/-- The nonzero-sector local vector is definitionally the corresponding Gram
eigenbasis vector. -/
theorem sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
          left right U i hlambda) =
      (projectedUnitaryBlockGramEigenbasis left right U i :
        StateVector (Qubits N)) := by
  unfold sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
  unfold projectedUnitaryBlockNonzeroClassifiedSingularBlock
  by_cases hsigma :
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma = 1
  · simp [SourceSingularInvariantLocalVector.vec,
      projectedUnitaryBlockUnitSingularBlock,
      projectedUnitaryBlockNonzeroSingularPair,
      projectedUnitaryBlockRightSingularVector,
      show projectedUnitaryBlockSingularValue left right U i = 1 by
        simpa [projectedUnitaryBlockNonzeroSingularPair] using hsigma]
  · simp [SourceSingularInvariantLocalVector.vec,
      projectedUnitaryBlockTwoDimensionalSingularBlock,
      projectedUnitaryBlockNonzeroSingularPair,
      projectedUnitaryBlockRightSingularVector,
      show ¬ projectedUnitaryBlockSingularValue left right U i = 1 by
        intro h
        exact hsigma (by
          simpa [projectedUnitaryBlockNonzeroSingularPair] using h)]

/-- If every Gram eigenvalue is nonzero, the source direct-sum coverage is
generated by the nonzero singular sectors alone.  The zero-eigenvalue version
adds right-kernel, left-kernel, and fully complementary sectors. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfNoZeroGramEigenvalues
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (hlambda :
      ∀ i : (Qubits N).Index,
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right where
  combination := fun i =>
    [(1,
      sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
        left right U i (hlambda i))]
  basis_eq := by
    intro i
    simp [sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
      left right U i (hlambda i)]

/-- The right-projector component of a zero Gram eigenbasis vector is a
right-kernel sector vector in `lemma:singInvDec` [GSLW19, BlockHam.tex:599-611,
655-716]. -/
noncomputable def sourceRightKernelLocalVectorOfZeroGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector U left right :=
  SourceSingularInvariantLocalVector.rightKernel
    (sourceRightKernelSingularBlockOfProjectedBlockEqZero U left right
      (HilbertOperator.applyVec right.op
        (projectedUnitaryBlockGramEigenbasis left right U i : StateVector (Qubits N)))
      (by
        rw [← HilbertOperator.mul_applyVec, right.idempotent])
      (by
        rw [projectedUnitaryBlock_applyVec_projector_applyVec]
        exact projectedUnitaryBlock_applyVec_rightSingularVector_eq_zero_of_eigenvalue_zero
          left right U i hlambda))

/-- The zero-eigenvalue right-kernel local vector is the right-projector
component of the Gram eigenbasis vector. -/
theorem sourceRightKernelLocalVectorOfZeroGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hlambda) =
      HilbertOperator.applyVec right.op
        (projectedUnitaryBlockGramEigenbasis left right U i : StateVector (Qubits N)) := by
  rfl

/-- A right-complement vector whose image has no left-projector component is a
fully complementary local sector of `lemma:singInvDec` [GSLW19,
BlockHam.tex:607-613,718-735]. -/
noncomputable def sourceComplementLocalVectorOfRightComplementProjectedZero
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (rightPerp : StateVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceSingularInvariantLocalVector U left right :=
  SourceSingularInvariantLocalVector.complement
    (sourceComplementSingularBlockOfRightComplementProjectedZero
      U left right rightPerp hright_perp hleft_zero)

/-- The fully complementary local vector is definitionally the supplied
right-complement vector. -/
theorem sourceComplementLocalVectorOfRightComplementProjectedZero_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (rightPerp : StateVector (Qubits N))
    (hright_perp :
      HilbertOperator.applyVec (OrthogonalProjector.complement right) rightPerp =
        rightPerp)
    (hleft_zero : HilbertOperator.applyVec left.op (U.applyVec rightPerp) = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceComplementLocalVectorOfRightComplementProjectedZero
          left right U rightPerp hright_perp hleft_zero) =
      rightPerp := by
  rfl

/-- The left-projector component of a zero output-side Gram eigenbasis vector is
a left-kernel sector of `lemma:singInvDec` [GSLW19, BlockHam.tex:599-611,
655-716]. -/
noncomputable def sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector U left right :=
  let hleft_zero :=
    projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_eq_zero_of_eigenvalue_zero
      left right U i hlambda
  SourceSingularInvariantLocalVector.leftKernel
    (sourceLeftKernelSingularBlockOfProjectedBlockConjTransposeEqZero
      U left right
      (HilbertOperator.applyVec left.op
        (projectedUnitaryBlockLeftGramEigenbasis left right U i :
          StateVector (Qubits N)))
      (by
        rw [← HilbertOperator.mul_applyVec, left.idempotent])
      (by
        rw [projectedUnitaryBlock_conjTranspose_applyVec_projector_applyVec]
        exact hleft_zero))

/-- The zero output-side Gram local vector is the `U†`-preimage of the
left-projector component of the output eigenbasis vector. -/
theorem sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis_vec
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i = 0) :
    SourceSingularInvariantLocalVector.vec
        (sourceLeftKernelLocalVectorOfZeroLeftGramEigenbasis left right U i hlambda) =
      U.conjTranspose.applyVec
        (HilbertOperator.applyVec left.op
          (projectedUnitaryBlockLeftGramEigenbasis left right U i :
            StateVector (Qubits N))) := by
  rfl

/-- Reduce full local coverage to the remaining decomposition of the
right-projector complement in the zero Gram eigenspaces.  Nonzero eigenvectors
are handled by the unit/two-dimensional split, while zero eigenvectors first
contribute their `Π`-supported right-kernel component [GSLW19,
BlockHam.tex:583-613,655-736]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (zeroComplementCombination :
      ∀ i : (Qubits N).Index,
        (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 ->
          List (ℂ × SourceSingularInvariantLocalVector U left right))
    (zeroComplement_basis_eq :
      ∀ (i : (Qubits N).Index)
        (hlambda :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              StateVector (Qubits N)) =
          ((zeroComplementCombination i hlambda).map fun term =>
            term.1 • SourceSingularInvariantLocalVector.vec term.2).sum) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right where
  combination := fun i =>
    if hlambda :
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0 then
      [(1,
        sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
          left right U i hlambda)]
    else
      have hzero_complex :
          ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) = 0 :=
        not_not.mp hlambda
      have hzero :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
        Complex.ofReal_eq_zero.mp hzero_complex
      [(1, sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
        zeroComplementCombination i hzero
  basis_eq := by
    intro i
    by_cases hlambda :
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0
    · simp [hlambda,
        sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis_vec
          left right U i hlambda]
    · have hzero_complex :
          ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) = 0 :=
        not_not.mp hlambda
      have hzero :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
        Complex.ofReal_eq_zero.mp hzero_complex
      calc
        (projectedUnitaryBlockGramEigenbasis left right U i :
            StateVector (Qubits N)) =
            HilbertOperator.applyVec right.op
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  StateVector (Qubits N)) +
              HilbertOperator.applyVec (OrthogonalProjector.complement right)
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  StateVector (Qubits N)) := by
              exact (orthogonalProjector_applyVec_add_complement_applyVec right
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  StateVector (Qubits N))).symm
        _ =
            (([(1,
              sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
                zeroComplementCombination i hzero).map
                  fun term : ℂ × SourceSingularInvariantLocalVector U left right =>
                  term.1 • SourceSingularInvariantLocalVector.vec term.2).sum := by
              simp [sourceRightKernelLocalVectorOfZeroGramEigenbasis_vec
                left right U i hzero, zeroComplement_basis_eq i hzero]
        _ =
            ((if hlambda :
                ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0 then
              [(1,
                sourceSingularInvariantLocalVectorOfNonzeroGramEigenbasis
                  left right U i hlambda)]
            else
              have hzero_complex :
                  ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) = 0 :=
                not_not.mp hlambda
              have hzero :
                  (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 :=
                Complex.ofReal_eq_zero.mp hzero_complex
              [(1, sourceRightKernelLocalVectorOfZeroGramEigenbasis left right U i hzero)] ++
                zeroComplementCombination i hzero).map
                  fun term : ℂ × SourceSingularInvariantLocalVector U left right =>
                    term.1 • SourceSingularInvariantLocalVector.vec term.2).sum := by
              simp [hlambda]

/-- Projected-QSVT local coverage obtained directly from the Gram eigenbasis.
For a zero Gram eigenvector, only its `Π`-supported part needs the source
right-kernel block.  Its `Πᗮ` part is an input-complement vector, and therefore
both the projected source block and the target `P^{(SV)}` annihilate it.  This
is the projected-theorem specialization of the source direct-sum split in
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-613,655-736]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfProjectorComplementSplit
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right :=
  sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit left right U
    (fun i _ =>
      [(1,
        SourceSingularInvariantLocalVector.inputComplement
          (HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              StateVector (Qubits N)))
          (by
            rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq]))])
    (by
      intro i hlambda
      simp [SourceSingularInvariantLocalVector.vec])

/-- Special zero-complement coverage when every zero-eigenvalue
right-complement component is fully complementary.  The general source proof
adds the left-kernel part before applying this fully-complementary case
[GSLW19, BlockHam.tex:607-613,718-735]. -/
noncomputable def sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementFullyComplementary
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (hleft_zero :
      ∀ (i : (Qubits N).Index)
        (_ :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec left.op
            (U.applyVec
              (HilbertOperator.applyVec (OrthogonalProjector.complement right)
                (projectedUnitaryBlockGramEigenbasis left right U i :
                  StateVector (Qubits N)))) = 0) :
    SourceSingularInvariantLocalBasisSpanCoverage U left right :=
  sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit left right U
    (fun i hlambda =>
      [(1,
        sourceComplementLocalVectorOfRightComplementProjectedZero left right U
          (HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              StateVector (Qubits N)))
          (by
            rw [← HilbertOperator.mul_applyVec, OrthogonalProjector.complement_sq])
          (hleft_zero i hlambda))])
    (by
      intro i hlambda
      simp [sourceComplementLocalVectorOfRightComplementProjectedZero_vec])

/-- Direct local-block coverage feeds the generic basis-span family used by the
global projected-QSVT theorem. -/
noncomputable def sourceProjectedQSVTBasisSpanFamilyOfLocalCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBasisSpanFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) where
  ι := SourceSingularInvariantLocalVector U left right
  vec := SourceSingularInvariantLocalVector.vec
  combination := coverage.combination
  basis_eq := coverage.basis_eq
  action_eq :=
    SourceSingularInvariantLocalVector.action_eq U left right certificate hP init last hφs

/-- Local-block basis-span coverage proves the source-level projected-QSVT block
equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTBasisSpanFamilyOfLocalCoverage U left right certificate hP
      coverage init last hφs)

/-- Direct local-block coverage for the negated projected phase list.  This is
the local form of the `U_{-\Phi}` branch used in the real-polynomial averaging
step of `cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def sourceProjectedQSVTBasisSpanFamilyNegProjectedPhasesOfLocalCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBasisSpanFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) where
  ι := SourceSingularInvariantLocalVector U left right
  vec := SourceSingularInvariantLocalVector.vec
  combination := coverage.combination
  basis_eq := coverage.basis_eq
  action_eq :=
    SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs

/-- Local-block basis-span coverage proves the negated-phase source-level
projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_localBasisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_basisSpanFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTBasisSpanFamilyNegProjectedPhasesOfLocalCoverage
      U left right certificate hP coverage init last hφs)

/-- Source projected-QSVT in the special case where the Gram spectrum has no
zero eigenvalues.  This packages the nonzero part of `lemma:singInvDec`; the
general theorem adds the zero-sector right-kernel, left-kernel, and fully
complementary blocks [GSLW19, BlockHam.tex:583-613,655-736,768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_noZeroGramEigenvalues
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (hlambda :
      ∀ i : (Qubits N).Index,
        ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage U left right
    certificate hP
    (sourceSingularInvariantLocalBasisSpanCoverageOfNoZeroGramEigenvalues
      left right U hlambda)
    init last hφs

/-- Source projected-QSVT reduced to the final zero-complement decomposition
piece of `lemma:singInvDec`. -/
theorem sourceProjectedQSVTBlockCorrectness_of_zeroComplementSplit
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (zeroComplementCombination :
      ∀ i : (Qubits N).Index,
        (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 ->
          List (ℂ × SourceSingularInvariantLocalVector U left right))
    (zeroComplement_basis_eq :
      ∀ (i : (Qubits N).Index)
        (hlambda :
          (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0),
        HilbertOperator.applyVec (OrthogonalProjector.complement right)
            (projectedUnitaryBlockGramEigenbasis left right U i :
              StateVector (Qubits N)) =
          ((zeroComplementCombination i hlambda).map fun term =>
            term.1 • SourceSingularInvariantLocalVector.vec term.2).sum)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage U left right
    certificate hP
    (sourceSingularInvariantLocalBasisSpanCoverageOfZeroComplementSplit
      left right U zeroComplementCombination zeroComplement_basis_eq)
    init last hφs

/-- Coverage contract for the source invariant decomposition: the tagged
source-side vectors are extensionally complete for operator equalities.  This
is the direct-sum/spanning obligation left by `lemma:singInvDec`
[GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantCoverage {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the coverage proof. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  ext :
    ∀ {A B : HilbertOperator (Qubits N)},
      (∀ tag : SourceSingularInvariantVector decomposition,
        HilbertOperator.applyVec A (SourceSingularInvariantVector.vec tag) =
          HilbertOperator.applyVec B (SourceSingularInvariantVector.vec tag)) ->
      A = B

/-- A concrete way to prove `SourceSingularInvariantCoverage`: classify every
Gram-eigenbasis vector into one of the source singular-invariant sector tags.
This is the Lean form of the source direct-sum classification in
`lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantBasisCoverage {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the basis classification. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  /-- Sector tag assigned to each Gram-eigenbasis vector. -/
  tagOfBasis :
    (Qubits N).Index -> SourceSingularInvariantVector decomposition
  tag_vec_eq :
    ∀ i : (Qubits N).Index,
      SourceSingularInvariantVector.vec (tagOfBasis i) =
        (projectedUnitaryBlockGramEigenbasis left right U i :
          StateVector (Qubits N))

namespace SourceSingularInvariantBasisCoverage

/-- A Gram-eigenbasis sector classification gives the extensional source
coverage required by the projected-QSVT assembly theorem. -/
noncomputable def toCoverage {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (coverage : SourceSingularInvariantBasisCoverage U left right) :
    SourceSingularInvariantCoverage U left right where
  decomposition := coverage.decomposition
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [← coverage.tag_vec_eq i]
    exact h (coverage.tagOfBasis i)

end SourceSingularInvariantBasisCoverage

/-- A flexible basis-level coverage witness: each Gram-eigenbasis vector may be
a finite linear combination of source singular-invariant sector vectors.  This
matches the source direct-sum construction in the zero-singular-value sectors,
where a Gram basis vector is split into its right-projector and complementary
parts [GSLW19, BlockHam.tex:583-613,655-736]. -/
structure SourceSingularInvariantBasisSpanCoverage {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Source singular-invariant sector decomposition used by the span coverage. -/
  decomposition : SourceSingularInvariantDecomposition U left right
  /-- Linear combination of source-sector vectors for each Gram-eigenbasis vector. -/
  combination :
    (Qubits N).Index -> List (ℂ × SourceSingularInvariantVector decomposition)
  basis_eq :
    ∀ i : (Qubits N).Index,
      (projectedUnitaryBlockGramEigenbasis left right U i :
          StateVector (Qubits N)) =
        ((combination i).map fun term =>
          term.1 • SourceSingularInvariantVector.vec term.2).sum

namespace SourceSingularInvariantBasisSpanCoverage

private theorem applyVec_eq_on_combination {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    {decomposition : SourceSingularInvariantDecomposition U left right}
    {A B : HilbertOperator (Qubits N)}
    (h :
      ∀ tag : SourceSingularInvariantVector decomposition,
        HilbertOperator.applyVec A (SourceSingularInvariantVector.vec tag) =
          HilbertOperator.applyVec B (SourceSingularInvariantVector.vec tag))
    (terms : List (ℂ × SourceSingularInvariantVector decomposition)) :
    HilbertOperator.applyVec A
        ((terms.map fun term => term.1 • SourceSingularInvariantVector.vec term.2).sum) =
      HilbertOperator.applyVec B
        ((terms.map fun term => term.1 • SourceSingularInvariantVector.vec term.2).sum) := by
  induction terms with
  | nil =>
      simp [HilbertOperator.applyVec]
  | cons term rest ih =>
      rcases term with ⟨c, tag⟩
      simp [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul, h tag, ih]

/-- A finite linear-combination classification of every Gram-eigenbasis vector
gives the extensional source coverage required by the projected-QSVT assembly
theorem. -/
noncomputable def toCoverage {N : Nat} {U : Gate (Qubits N)}
    {left right : OrthogonalProjector N}
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right) :
    SourceSingularInvariantCoverage U left right where
  decomposition := coverage.decomposition
  ext := by
    intro A B h
    apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis
      (projectedUnitaryBlockGramEigenbasis left right U)
    intro i
    rw [coverage.basis_eq i]
    exact applyVec_eq_on_combination h (coverage.combination i)

end SourceSingularInvariantBasisSpanCoverage

/-- A source invariant decomposition with extensional coverage supplies the
spanning family required for the global `thm:singValTransformation` equality,
provided each source sector is evaluated by the local block lemmas
[GSLW19, BlockHam.tex:655-736,768-849]. -/
noncomputable def sourceProjectedQSVTSpanningFamilyOfCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) := by
  refine
    { ι := SourceSingularInvariantVector coverage.decomposition
      vec := fun tag => SourceSingularInvariantVector.vec tag
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact coverage.ext h
  · intro tag
    cases tag with
    | unit i =>
        let block := coverage.decomposition.unitBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · rw [
            SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          rw [
            SourceUnitSingularBlock.sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
              block certificate init last hφs hdodd,
            SourceUnitSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | twoRight i =>
        let block := coverage.decomposition.twoDimensionalBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · open SourceTwoDimensionalSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceTwoDimensionalSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd
              block certificate init last hφs hdodd,
            SourceTwoDimensionalSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | twoRightPerp i =>
        let block := coverage.decomposition.twoDimensionalBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (sourceAlternatingPhaseModulation U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            sourceProjectedBlock_applyVec_eq_zero_of_input_complement_support
              (projectedOutputProjector left right d) right
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
              block.rightPerp block.right_perp_support
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
    | rightKernel i =>
        let block := coverage.decomposition.rightKernelBlock i
        dsimp [SourceSingularInvariantVector.vec]
        by_cases hd : d % 2 = 0
        · open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_even
              block certificate init last hφs hd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_even
              block P hd hP]
        · have hdodd : d % 2 = 1 := by omega
          open SourceRightKernelSingularBlock in
          rw [
            sourceProjectedBlock_projectedPhases_applyVec_rightVec_odd block certificate hdodd,
            SourceRightKernelSingularBlock.singularValuePolynomial_applyVec_rightVec_of_odd
              block P hdodd hP]
    | leftKernel i =>
        let block := coverage.decomposition.leftKernelBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (sourceAlternatingPhaseModulation U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceLeftKernelSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]
    | complement i =>
        let block := coverage.decomposition.complementBlock i
        dsimp [SourceSingularInvariantVector.vec]
        calc
          HilbertOperator.applyVec
              (sourceProjectedBlock (projectedOutputProjector left right d) right
                (sourceAlternatingPhaseModulation U left right
                  (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
              block.rightPerp = 0 :=
            SourceComplementSingularBlock.sourceProjectedBlock_applyVec_rightPerp_eq_zero
              block
              (sourceAlternatingPhaseModulation U left right
                (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
          _ =
              HilbertOperator.applyVec
                (singularValuePolynomial right d P (projectedUnitaryBlock left right U))
                block.rightPerp := by
            rw [singularValuePolynomial_applyVec_eq_zero_of_right_complement
              (left := left) (right := right) (U := U) P block.right_perp_support]

/-- Coverage plus the source sector-local action lemmas prove the global
source-level projected-QSVT block equality.  The remaining source obligation is
to construct `SourceSingularInvariantCoverage` from the spectral direct-sum
decomposition of `lemma:singInvDec` [GSLW19, BlockHam.tex:583-613,655-736,
768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_coverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
    (sourceProjectedQSVTSpanningFamilyOfCoverage U left right certificate hP
      coverage init last hφs)

/-- Basis-level sector classification is enough to prove the source-level
projected-QSVT block equality. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_coverage U left right certificate hP
    (SourceSingularInvariantBasisCoverage.toCoverage coverage) init last hφs

/-- Span-level sector classification is enough to prove the source-level
projected-QSVT block equality.  This is the interface used by the source
direct-sum proof because zero-singular-value Gram basis vectors split into
projector and complementary pieces [GSLW19, BlockHam.tex:583-613,655-736,
768-849]. -/
theorem sourceProjectedQSVTBlockCorrectness_of_basisSpanCoverage {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d P
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  sourceProjectedQSVTBlockCorrectness_of_coverage U left right certificate hP
    (SourceSingularInvariantBasisSpanCoverage.toCoverage coverage) init last hφs

/-- Coverage plus the local negated-phase action lemmas proves the
coefficient-conjugate source-level projected-QSVT block equality.  This is the
coverage-level `U_{-\Phi}` branch used by the averaging proof of
`cor:matchingParity` [GSLW19, BlockHam.tex:655-736,851-887]. -/
noncomputable def sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTSpanningFamily (d := d) U left right (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) := by
  refine
    { ι := SourceSingularInvariantVector coverage.decomposition
      vec := fun tag => SourceSingularInvariantVector.vec tag
      ext := ?_
      action_eq := ?_ }
  · intro A B h
    exact coverage.ext h
  · intro tag
    rw [← SourceSingularInvariantLocalVector.vec_ofDecompositionVector tag]
    exact SourceSingularInvariantLocalVector.action_eq_negProjectedPhases
      U left right certificate hP init last hφs
      (SourceSingularInvariantLocalVector.ofDecompositionVector tag)

/-- Coverage-level negated-phase source block equality for the
coefficient-conjugate polynomial [GSLW19, BlockHam.tex:655-736,851-887]. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_coverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_of_spanningFamily U left right
    (negPhases
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (sourceProjectedQSVTSpanningFamilyNegProjectedPhasesOfCoverage
      U left right certificate hP coverage init last hφs)

/-- Span-level sector classification is also enough for the negated-phase
branch used in the real-polynomial averaging proof. -/
theorem sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_basisSpanCoverage
    {N d : Nat} {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last]) :
    SourceProjectedQSVTBlockCorrectness U left right d (conjP P)
      (negPhases
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :=
  sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_coverage
    U left right certificate hP
    (SourceSingularInvariantBasisSpanCoverage.toCoverage coverage)
    init last hφs

/-- The source-aligned real-projected circuit determined by a reflection-QSP
phase certificate. -/
noncomputable def sourceRealProjectedCircuitOfPhaseCertificate {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    Circuit (Qubits (1 + N)) :=
  sourceRealProjectedCircuit U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

theorem sourceRealProjectedCircuitOfPhaseCertificate_resources {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ResourceProfile.HasExactCounts
      (sourceRealProjectedCircuitOfPhaseCertificate U left right certificate).resources
      d 0 d 0 := by
  simpa [sourceRealProjectedCircuitOfPhaseCertificate,
    projectedPhasesFromQSPCertificate_length, certificate.length_eq] using
    sourceRealProjectedCircuit_resourceProfile U left right
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

theorem sourceRealProjectedCircuitOfPhaseCertificate_projectedResources {N d : Nat}
    {P Q : Polynomial ℂ} (_U : Gate (Qubits N))
    (_left _right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ProjectedResourceProfile.HasExactCounts
      (ProjectedResourceProfile.ofLength
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length) d := by
  simp [projectedPhasesFromQSPCertificate_length, certificate.length_eq]

theorem sourceRealProjectedCircuitOfPhaseCertificate_matrix_and_resources {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ((sourceRealProjectedCircuitOfPhaseCertificate U left right certificate).matrix :
        HilbertOperator (Qubits (1 + N))) =
          sourceRealProjectedGate U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) ∧
      ProjectedResourceProfile.HasExactCounts
        (ProjectedResourceProfile.ofLength
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs).length) d ∧
      ResourceProfile.HasExactCounts
        (sourceRealProjectedCircuitOfPhaseCertificate U left right certificate).resources
        d 0 d 0 := by
  exact ⟨rfl,
    sourceRealProjectedCircuitOfPhaseCertificate_projectedResources U left right certificate,
    sourceRealProjectedCircuitOfPhaseCertificate_resources U left right certificate⟩

namespace RealProjectedQSVTRealization

/-- Once the source singular-value transformation theorem supplies the block
equality for the projected phase list, the phase certificate yields a same-circuit
public-real projected-QSVT realization. -/
noncomputable def ofPhaseCertificateWithBlockCorrectness {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hblock :
      RealProjectedQSVTBlockCorrectness U left right d P
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d P (projectedUnitaryBlock left right U)) where
  phases := projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs
  length_eq := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq]
  circuit := sourceRealProjectedCircuitOfPhaseCertificate U left right certificate
  circuit_eq := rfl
  block_eq := hblock
  resources_exact := ProjectedResourceProfile.ofLength_hasExactCounts d
  circuit_resources :=
    sourceRealProjectedCircuitOfPhaseCertificate_resources U left right certificate

/-- Build the public-real realization package from the two source-level
singular-value block equalities for `Φ` and `-Φ`, plus the averaged polynomial
identity supplied by the matching-parity real-polynomial theorem. -/
noncomputable def ofPhaseCertificateSourceAverage {N d : Nat}
    {P Q Pneg Preal : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hpos :
      SourceProjectedQSVTBlockCorrectness U left right d P
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (hneg :
      SourceProjectedQSVTBlockCorrectness U left right d Pneg
        (negPhases (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)))
    (havg :
      (1 / 2 : ℂ) •
          singularValuePolynomial right d P (projectedUnitaryBlock left right U) +
        (1 / 2 : ℂ) •
          singularValuePolynomial right d Pneg (projectedUnitaryBlock left right U) =
        singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) where
  phases := projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs
  length_eq := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq]
  circuit := sourceRealProjectedCircuitOfPhaseCertificate U left right certificate
  circuit_eq := rfl
  block_eq :=
    realProjectedQSVTBlockCorrectness_of_source_average
      U left right d P Pneg Preal
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
      hpos hneg havg
  resources_exact := ProjectedResourceProfile.ofLength_hasExactCounts d
  circuit_resources :=
    sourceRealProjectedCircuitOfPhaseCertificate_resources U left right certificate

/-- Matching-parity projected QSVT from source phase certificates and the
source invariant direct-sum decomposition.  The positive and negative phase
certificates use the same constructed real-projected circuit; the negative
certificate is connected by the displayed `negPhases` equality.  This packages
the circuit/resource part of `cor:matchingParity` [GSLW19,
BlockHam.tex:851-887]. -/
noncomputable def ofPhaseCertificatesAndOrthonormalDecomposition {N d : Nat}
    {P Q Pneg Qneg Preal : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (negativeCertificate :
      ReflectionQSPPhaseSynthesis.PhaseCertificate d Pneg Qneg)
    (hP : HasParity P d) (hPneg : HasParity Pneg d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last])
    (negativeInit : List ℝ) (negativeLast : ℝ)
    (hφsNeg : negativeCertificate.φs = negativeInit ++ [negativeLast])
    (hnegativePhases :
      projectedPhasesFromQSPCertificate
          negativeCertificate.φ₀ negativeCertificate.φs =
        negPhases
          (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs))
    (havg :
      (1 / 2 : ℂ) •
          singularValuePolynomial right d P (projectedUnitaryBlock left right U) +
        (1 / 2 : ℂ) •
          singularValuePolynomial right d Pneg (projectedUnitaryBlock left right U) =
        singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) :=
  ofPhaseCertificateSourceAverage U left right certificate
    (sourceProjectedQSVTBlockCorrectness_of_orthonormalDecomposition
      U left right certificate hP coverage init last hφs)
    (by
      simpa [hnegativePhases] using
        sourceProjectedQSVTBlockCorrectness_of_orthonormalDecomposition
          U left right negativeCertificate hPneg coverage
          negativeInit negativeLast hφsNeg)
    havg

/-- Matching-parity projected QSVT from one source phase certificate.  The
second branch of the same counted circuit uses the negated projected phase list,
which the source averaging construction identifies with the coefficient
conjugate polynomial [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def ofPhaseCertificateAndConjugateOrthonormalDecomposition {N d : Nat}
    {P Q Preal : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hP : HasParity P d)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ) (hφs : certificate.φs = init ++ [last])
    (havg :
      (1 / 2 : ℂ) •
          singularValuePolynomial right d P (projectedUnitaryBlock left right U) +
        (1 / 2 : ℂ) •
          singularValuePolynomial right d (conjP P) (projectedUnitaryBlock left right U) =
        singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d Preal (projectedUnitaryBlock left right U)) :=
  ofPhaseCertificateSourceAverage U left right certificate
    (sourceProjectedQSVTBlockCorrectness_of_orthonormalDecomposition
      U left right certificate hP coverage init last hφs)
    (sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_orthonormalDecomposition
      U left right certificate hP coverage init last hφs)
    havg

/-- Real matching-parity projected QSVT from the source real-polynomial phase
certificate.  This is the direct `cor:realP` to `cor:matchingParity` handoff:
the completion polynomial `P` and its coefficient conjugate are averaged back
to the original real target, while both branches are carried by the same
counted source-projected circuit [GSLW19, BlockHam.tex:544-557,851-887]. -/
noncomputable def ofRealBoundedPhaseCertificateAndOrthonormalDecomposition
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.certificate.φs = init ++ [last]) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  ofPhaseCertificateAndConjugateOrthonormalDecomposition U left right
    certificate.certificate certificate.completion.qsp_pair.parP
    coverage init last hφs
    (singularValuePolynomial_average_of_polynomial_average right d
      certificate.completion.P (conjP certificate.completion.P)
      (realPolynomialToComplex PRe) (projectedUnitaryBlock left right U)
      certificate.completion.average_conj_eq)

/-- Positive-degree version of
`ofRealBoundedPhaseCertificateAndOrthonormalDecomposition` that extracts the
final source phase slot from the phase certificate itself. -/
noncomputable def ofRealBoundedPhaseCertificateAndOrthonormalDecompositionOfPositiveDegree
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantOrthonormalDecomposition U left right)
    (hd : 0 < d) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  let split := certificate.certificate.exists_init_last_of_pos hd
  let init : List ℝ := Classical.choose split
  let last : ℝ := Classical.choose (Classical.choose_spec split)
  have hφs : certificate.certificate.φs = init ++ [last] :=
    Classical.choose_spec (Classical.choose_spec split)
  ofRealBoundedPhaseCertificateAndOrthonormalDecomposition
    U left right certificate coverage init last hφs

/-- Real matching-parity projected QSVT from the flexible source basis-span
coverage interface.  This is the form closest to the source direct-sum proof:
zero-singular-value Gram vectors may be finite linear combinations of
right-kernel, left-kernel, and complementary source sectors [GSLW19,
BlockHam.tex:583-613,655-736,851-887]. -/
noncomputable def ofRealBoundedPhaseCertificateAndBasisSpanCoverage
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.certificate.φs = init ++ [last]) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  ofPhaseCertificateSourceAverage U left right certificate.certificate
    (sourceProjectedQSVTBlockCorrectness_of_basisSpanCoverage
      U left right certificate.certificate certificate.completion.qsp_pair.parP
      coverage init last hφs)
    (sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_basisSpanCoverage
      U left right certificate.certificate certificate.completion.qsp_pair.parP
      coverage init last hφs)
    (singularValuePolynomial_average_of_polynomial_average right d
      certificate.completion.P (conjP certificate.completion.P)
      (realPolynomialToComplex PRe) (projectedUnitaryBlock left right U)
      certificate.completion.average_conj_eq)

/-- Positive-degree basis-span version, extracting the final source phase slot
from the phase certificate itself. -/
noncomputable def ofRealBoundedPhaseCertificateAndBasisSpanCoverageOfPositiveDegree
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (hd : 0 < d) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  let split := certificate.certificate.exists_init_last_of_pos hd
  let init : List ℝ := Classical.choose split
  let last : ℝ := Classical.choose (Classical.choose_spec split)
  have hφs : certificate.certificate.φs = init ++ [last] :=
    Classical.choose_spec (Classical.choose_spec split)
  ofRealBoundedPhaseCertificateAndBasisSpanCoverage
    U left right certificate coverage init last hφs

/-- Real matching-parity projected QSVT from the source real-polynomial phase
certificate and the local projected source coverage.  The local coverage is
enough for the projected theorem because input-complement vectors are
annihilated by both sides of the projected equality [GSLW19,
BlockHam.tex:599-613,655-736,851-887]. -/
noncomputable def ofRealBoundedPhaseCertificateAndLocalBasisSpanCoverage
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (init : List ℝ) (last : ℝ)
    (hφs : certificate.certificate.φs = init ++ [last]) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  ofPhaseCertificateSourceAverage U left right certificate.certificate
    (sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage
      U left right certificate.certificate certificate.completion.qsp_pair.parP
      coverage init last hφs)
    (sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_localBasisSpanCoverage
      U left right certificate.certificate certificate.completion.qsp_pair.parP
      coverage init last hφs)
    (singularValuePolynomial_average_of_polynomial_average right d
      certificate.completion.P (conjP certificate.completion.P)
      (realPolynomialToComplex PRe) (projectedUnitaryBlock left right U)
      certificate.completion.average_conj_eq)

/-- Positive-degree local-coverage version, extracting the final source phase
slot from the phase certificate itself. -/
noncomputable def ofRealBoundedPhaseCertificateAndLocalBasisSpanCoverageOfPositiveDegree
    {N d : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe)
    (coverage : SourceSingularInvariantLocalBasisSpanCoverage U left right)
    (hd : 0 < d) :
    RealProjectedQSVTRealization U left right d
      (singularValuePolynomial right d (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  let split := certificate.certificate.exists_init_last_of_pos hd
  let init : List ℝ := Classical.choose split
  let last : ℝ := Classical.choose (Classical.choose_spec split)
  have hφs : certificate.certificate.φs = init ++ [last] :=
    Classical.choose_spec (Classical.choose_spec split)
  ofRealBoundedPhaseCertificateAndLocalBasisSpanCoverage
    U left right certificate coverage init last hφs

end RealProjectedQSVTRealization

/-- Projected real-polynomial QSVT assuming the source direct-sum coverage
promised by `thm:singValTransformation`.  The phase certificate is chosen from
the completed Lemma-6-through-Corollary-10 real-polynomial QSP chain; the same
constructed projected circuit supplies both correctness and resources
[GSLW19, BlockHam.tex:544-557,583-613,655-736,851-887]. -/
noncomputable def realProjectedQSVTOfMatchingParityAndBasisSpanCoverage
    {N L : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (coverage : SourceSingularInvariantBasisSpanCoverage U left right)
    (hL : 0 < L) :
    RealProjectedQSVTRealization U left right L
      (singularValuePolynomial right L (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses hP
  RealProjectedQSVTRealization.ofRealBoundedPhaseCertificateAndBasisSpanCoverageOfPositiveDegree
    U left right certificate coverage hL

/-- Projected real-polynomial QSVT from the source matching-parity hypotheses.
This is the current Lean form of `cor:matchingParity`: Lemma 6 through
Corollary 10 supply the phase certificate, while the projected form of
`thm:singValTransformation` supplies the same-circuit block equality and exact
resources [GSLW19, BlockHam.tex:544-557,599-613,655-736,851-887]. -/
noncomputable def realProjectedQSVTOfMatchingParity
    {N L : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hL : 0 < L) :
    RealProjectedQSVTRealization U left right L
      (singularValuePolynomial right L (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) :=
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses hP
  open RealProjectedQSVTRealization in
  ofRealBoundedPhaseCertificateAndLocalBasisSpanCoverageOfPositiveDegree
    U left right certificate
    (sourceSingularInvariantLocalBasisSpanCoverageOfProjectorComplementSplit left right U)
    hL

namespace Decomposition.Projected

/-- Projected real-polynomial QSVT in the source statement form: the same
constructed circuit supplies the singular-value block equality and the exact
resource counters [GSLW19, BlockHam.tex:544-557,747-887]. -/
theorem sourceMain {N L : Nat} {PRe : Polynomial ℝ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (hL : 0 < L) :
    ∃ realization :
        RealProjectedQSVTRealization U left right L
          (singularValuePolynomial right L (realPolynomialToComplex PRe)
            (projectedUnitaryBlock left right U)),
      ProjectedResourceProfile.HasExactCounts
        (ProjectedResourceProfile.ofLength L) L ∧
        ResourceProfile.HasExactCounts realization.circuit.resources L 0 L 0 := by
  let realization := realProjectedQSVTOfMatchingParity U left right hP hL
  refine ⟨realization, ?_, ?_⟩
  · exact ProjectedResourceProfile.ofLength_hasExactCounts L
  · exact realization.circuit_resources

end Decomposition.Projected

/-- Construct the projected-QSVT word from a reflection-QSP phase certificate.
The phase certificate supplies the source phase list; the resulting word's
matrix and resource counters are then both read from the same `Circuit`
history [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def projectedQSVTWordOfPhaseCertificate {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ProjectedQSVTWord U left right
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  projectedQSVTWord U left right
    (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

theorem projectedQSVTWordOfPhaseCertificate_resources_exact {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ProjectedResourceProfile.HasExactCounts
      (projectedQSVTWordOfPhaseCertificate U left right certificate).resources d := by
  simpa [projectedQSVTWordOfPhaseCertificate,
    projectedPhasesFromQSPCertificate_length, certificate.length_eq] using
    projectedQSVTWord_resources_exact U left right
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

theorem projectedQSVTWordOfPhaseCertificate_circuitResourceProfile {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ResourceProfile.HasExactCounts
      (projectedQSVTWordOfPhaseCertificate U left right certificate).circuit.resources
      d 0 d 0 := by
  simpa [projectedQSVTWordOfPhaseCertificate,
    projectedPhasesFromQSPCertificate_length, certificate.length_eq] using
    projectedQSVTWord_circuitResourceProfile U left right
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)

theorem projectedQSVTWordOfPhaseCertificate_matrix_and_resources {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ((projectedQSVTWordOfPhaseCertificate U left right certificate).circuit.matrix :
        HilbertOperator (Qubits (1 + N))) =
          alternatingPhaseModulation U left right
            (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) ∧
      ProjectedResourceProfile.HasExactCounts
        (projectedQSVTWordOfPhaseCertificate U left right certificate).resources d ∧
      ResourceProfile.HasExactCounts
        (projectedQSVTWordOfPhaseCertificate U left right certificate).circuit.resources
        d 0 d 0 := by
  exact ⟨by
      simp [projectedQSVTWordOfPhaseCertificate, projectedQSVTWord_matrix],
    projectedQSVTWordOfPhaseCertificate_resources_exact U left right certificate,
    projectedQSVTWordOfPhaseCertificate_circuitResourceProfile U left right certificate⟩

/-- Implementation-gadget projected block target.  This is retained for local
sanity checks of the projector-controlled implementation, but the source-level
public theorem target is `RealProjectedQSVTBlockCorrectness` above. -/
def ProjectedQSVTBlockCorrectness {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (phases : List ℝ) (word : ProjectedQSVTWord U left right phases) : Prop :=
  projectedPhasePlusBlock (projectedOutputProjector left right L) right
      word.circuit.matrix =
    singularValuePolynomial right L P (projectedUnitaryBlock left right U)

/-- Degree-one base case of the projected singular-value theorem: the one-slot
sequence with phase `0` realizes `P(X)=X`, hence the original projected block
`Π_left U Π_right`.  This is the smallest nontrivial instance of the source
singular-value transformation theorem [GSLW19, BlockHam.tex:747-887]. -/
theorem projectedQSVTBlockCorrectness_X_single_zero {N : Nat}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N) :
    ProjectedQSVTBlockCorrectness U left right 1 (Polynomial.X : Polynomial ℂ) [0]
      (projectedQSVTWord U left right [0]) := by
  unfold ProjectedQSVTBlockCorrectness
  have hgate :
      (projectedQSVTWord U left right [0]).circuit.matrix =
        alternatingPhaseModulation U left right [0] := by
    apply Gate.ext
    intro i j
    rw [projectedQSVTWord_matrix]
  rw [hgate]
  simp [projectedOutputProjector, alternatingPhaseModulation, liftSourcePhaseSignal,
    sourcePhaseSignal, singularValuePolynomial_X_one]

/-- A projected-QSVT endpoint package whose correctness block equality and
resource counters are read from the same `ProjectedQSVTWord`.  This is the
internal shape used before the public statement names the target as
`P^{(SV)}(A)` [GSLW19, BlockHam.tex:851-887]. -/
structure ProjectedQSVTRealization {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (target : HilbertOperator (Qubits N)) where
  /-- Projected phase list used by the realization word. -/
  phases : List ℝ
  length_eq : phases.length = L
  /-- Projected-QSVT word carrying both circuit and specialized counters. -/
  word : ProjectedQSVTWord U left right phases
  block_eq :
    projectedPhasePlusBlock (projectedOutputProjector left right L) right
      word.circuit.matrix = target
  resources_exact : ProjectedResourceProfile.HasExactCounts word.resources L
  circuit_resources : ResourceProfile.HasExactCounts word.circuit.resources L 0 L 0

namespace ProjectedQSVTRealization

/-- Build a realization package from a canonical word once the projected block
correctness equality has been proved for that same word. -/
noncomputable def ofWord {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ)
    (target : HilbertOperator (Qubits N))
    (hblock :
      projectedPhasePlusBlock (projectedOutputProjector left right phases.length) right
        (projectedQSVTWord U left right phases).circuit.matrix = target) :
    ProjectedQSVTRealization U left right phases.length target where
  phases := phases
  length_eq := rfl
  word := projectedQSVTWord U left right phases
  block_eq := hblock
  resources_exact := projectedQSVTWord_resources_exact U left right phases
  circuit_resources := projectedQSVTWord_circuitResourceProfile U left right phases

/-- A phase certificate already determines a concrete projected-QSVT circuit and
the exact resource counters of that same circuit.  This constructor deliberately
uses the circuit block itself as the target; the source theorem later supplies
the separate equality identifying this block with `P^{(SV)}(A)` [GSLW19,
BlockHam.tex:851-887]. -/
noncomputable def ofPhaseCertificate {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right certificate).circuit.matrix) where
  phases := projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs
  length_eq := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq]
  word := projectedQSVTWordOfPhaseCertificate U left right certificate
  block_eq := rfl
  resources_exact := projectedQSVTWordOfPhaseCertificate_resources_exact U left right certificate
  circuit_resources :=
    projectedQSVTWordOfPhaseCertificate_circuitResourceProfile U left right certificate

/-- Once the source singular-value theorem identifies the projected block with
`P^{(SV)}(Π_left U Π_right)`, the phase certificate yields the final
same-circuit realization package. -/
noncomputable def ofPhaseCertificateWithBlockCorrectness {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q)
    (hblock :
      ProjectedQSVTBlockCorrectness U left right d P
        (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs)
        (projectedQSVTWordOfPhaseCertificate U left right certificate)) :
    ProjectedQSVTRealization U left right d
      (singularValuePolynomial right d P (projectedUnitaryBlock left right U)) where
  phases := projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs
  length_eq := by
    rw [projectedPhasesFromQSPCertificate_length, certificate.length_eq]
  word := projectedQSVTWordOfPhaseCertificate U left right certificate
  block_eq := hblock
  resources_exact := projectedQSVTWordOfPhaseCertificate_resources_exact U left right certificate
  circuit_resources :=
    projectedQSVTWordOfPhaseCertificate_circuitResourceProfile U left right certificate

theorem ofPhaseCertificate_resources_exact {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ProjectedResourceProfile.HasExactCounts
      (ofPhaseCertificate U left right certificate).word.resources d :=
  projectedQSVTWordOfPhaseCertificate_resources_exact U left right certificate

theorem ofPhaseCertificate_circuit_resources {N d : Nat} {P Q : Polynomial ℂ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    ResourceProfile.HasExactCounts
      (ofPhaseCertificate U left right certificate).word.circuit.resources
      d 0 d 0 :=
  projectedQSVTWordOfPhaseCertificate_circuitResourceProfile U left right certificate

/-- Real-polynomial QSP completion data produces the same-circuit projected
QSVT realization whose block is later identified with `P^{(SV)}(A)` by the
projected singular-value theorem [GSLW19, BlockHam.tex:544-557,851-887]. -/
noncomputable def ofRealBoundedPhaseCertificate {N d : Nat} {PRe : Polynomial ℝ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (certificate :
      ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right
          certificate.certificate).circuit.matrix) :=
  ofPhaseCertificate U left right certificate.certificate

/-- A source root-class factorization of `1 - P_re^2` determines the same
projected-QSVT circuit package as the corresponding real-bounded phase
certificate.  The correctness block and all resource counters still come from
the constructed `Circuit`; this declaration only composes the source-aligned
completion handoff with the projected-QSVT word constructor [GSLW19,
BlockHam.tex:436-480,544-557,851-887]. -/
noncomputable def ofSourceRootClassFactorization {N d : Nat} {PRe : Polynomial ℝ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe)
    (roots :
      Complement.Interval.SourceRootClassFactorization
        (ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity.squareTarget PRe) d) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right
          (open ReflectionQSPPhaseSynthesis in
            chooseRealBoundedPhaseCertificateOfSourceRootClassFactorization hP roots
          ).certificate).circuit.matrix) :=
  ofRealBoundedPhaseCertificate U left right
    (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceRootClassFactorization
      hP roots)

/-- Boundary-case projected-QSVT realization when the source square target
`1 - P_re^2` is constant.  This composes the interval-square base case with the
same-circuit projected-QSVT word constructor [GSLW19, BlockHam.tex:436-480,
544-557,851-887]. -/
noncomputable def ofSquareTargetNatDegreeZero {N d : Nat} {PRe : Polynomial ℝ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe)
    (hdeg :
      (ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity.squareTarget PRe).natDegree = 0) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right
          (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSquareTargetNatDegreeZero
            hP hdeg).certificate).circuit.matrix) :=
  ofRealBoundedPhaseCertificate U left right
    (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSquareTargetNatDegreeZero
      hP hdeg)

/-- Completed source-root coverage determines the same-circuit projected-QSVT
realization.  This is the final handoff shape expected after the general
root-grouping proof is complete [GSLW19, BlockHam.tex:436-480,544-557,851-887]. -/
noncomputable def ofSourceRootClassCoverage {N d : Nat} {PRe : Polynomial ℝ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity.squareTarget PRe)}
    (coverage : Complement.Interval.SourceRootClassCoverage data d) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right
          (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceRootClassCoverage
            hP coverage).certificate).circuit.matrix) :=
  ofRealBoundedPhaseCertificate U left right
    (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceRootClassCoverage
      hP coverage)

/-- Final source-root product identity plus the source degree bound determine
the same-circuit projected-QSVT realization.  This is the handoff shape used
once the root-class grouping proof from [GSLW19, BlockHam.tex:469-480] is
complete; correctness and resources still come from the same constructed
`Circuit` [GSLW19, BlockHam.tex:544-557,851-887]. -/
noncomputable def ofSourceRootProductAndDegreeLe {N d : Nat} {PRe : Polynomial ℝ}
    (U : Gate (Qubits N)) (left right : OrthogonalProjector N)
    (hP : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe)
    {data :
      Complement.Interval.SourceRootProductData
        (ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity.squareTarget PRe)}
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity.squareTarget PRe =
        Polynomial.C constant *
          (Polynomial.X : Polynomial ℝ) ^ (2 * data.zeroRootPairs) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              Complement.Interval.DegreeParityFactorCertificate.interiorRealRootPair) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              Complement.Interval.DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              Complement.Interval.DegreeParityFactorCertificate.imaginaryRoot) *
          Complement.Interval.DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              Complement.Interval.DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree_le : data.rootClassDegree ≤ d) :
    ProjectedQSVTRealization U left right d
      (projectedPhasePlusBlock (projectedOutputProjector left right d) right
        (projectedQSVTWordOfPhaseCertificate U left right
          (open ReflectionQSPPhaseSynthesis in
            chooseRealBoundedPhaseCertificateOfSourceRootProductAndDegreeLe
              hP constant constant_nonnegative hproduct hdegree_le
          ).certificate).circuit.matrix) :=
  ofRealBoundedPhaseCertificate U left right
    (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceRootProductAndDegreeLe
      hP constant constant_nonnegative hproduct hdegree_le)

end ProjectedQSVTRealization

end QSVT

namespace QSVT.Decomposition

/-- Namespace-local spelling of projected-QSVT resource counters. -/
abbrev ProjectedResourceProfile :=
  QuantumAlg.QSP.MultiQubit.QSVT.ProjectedResourceProfile

/-- Namespace-local spelling of the public-real projected-QSVT realization. -/
abbrev RealProjectedQSVTRealization {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (target : HilbertOperator (Qubits N)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.RealProjectedQSVTRealization U left right L target

/-- Namespace-local spelling of an implementation-gadget projected-QSVT word. -/
abbrev ProjectedQSVTWord {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :=
  QuantumAlg.QSP.MultiQubit.QSVT.ProjectedQSVTWord U left right phases

/-- Namespace-local spelling of an internal projected-QSVT realization. -/
abbrev ProjectedQSVTRealization {N : Nat} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N) (L : ℕ) (target : HilbertOperator (Qubits N)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.ProjectedQSVTRealization U left right L target

/-- Namespace-local constructor for a projected-QSVT word from a phase certificate. -/
noncomputable abbrev projectedQSVTWordOfPhaseCertificate {N d : Nat}
    {P Q : Polynomial ℂ} (U : Gate (Qubits N))
    (left right : OrthogonalProjector N)
    (certificate : ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q) :
    QuantumAlg.QSP.MultiQubit.QSVT.ProjectedQSVTWord U left right
      (projectedPhasesFromQSPCertificate certificate.φ₀ certificate.φs) :=
  QuantumAlg.QSP.MultiQubit.QSVT.projectedQSVTWordOfPhaseCertificate
    U left right certificate

end QSVT.Decomposition

end QSP.MultiQubit

end QuantumAlg

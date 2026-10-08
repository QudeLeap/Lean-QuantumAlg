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
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Intrinsic branch averages and scalar block encodings

These operator identities express selector averaging and complex reconstruction
[GSLW19, BlockHam.tex:851-887,1939-1957]. They do not attach resource claims to
abstract direct sums. Actual native implementations establish their own costs.
-/

section
namespace QuantumAlg.QSP.MultiQubit.QSVT
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- Lift a metadata-free signal unitary to the phase-ancilla plus signal
space used in alternating phase modulation. -/
def liftSignalOperator {N : Nat} (U : UnitaryOperator (Qubits N)) :
    UnitaryOperator (Qubits (1 + N)) :=
  (1 : UnitaryOperator (Qubits 1)).tensor U

/-- Relative metadata-free branch unitary used by a controlled direct sum. -/
def phaseRelativeOperator {N : Nat} (V0 V1 : UnitaryOperator (Qubits N)) :
    UnitaryOperator (Qubits N) :=
  V1 * V0.dagger

/-- Controlled direct sum as a metadata-free unitary. -/
noncomputable def phaseControlledDirectSumOperator {N : Nat}
    (V0 V1 : UnitaryOperator (Qubits N)) : UnitaryOperator (Qubits (1 + N)) :=
  UnitaryOperator.controlledQubits (phaseRelativeOperator V0 V1) *
    liftSignalOperator V0

theorem phaseControlledDirectSum_eq_tensor_decomp {N : Nat}
    (V0 V1 : UnitaryOperator (Qubits N)) :
    (phaseControlledDirectSumOperator V0 V1 : HilbertOperator (Qubits (1 + N))) =
      HilbertOperator.tensor HilbertOperator.proj0 (V0 : HilbertOperator (Qubits N)) +
        HilbertOperator.tensor HilbertOperator.proj1 (V1 : HilbertOperator (Qubits N)) := by
  have hV0 :
      (V0 : HilbertOperator (Qubits N)).conjTranspose *
          (V0 : HilbertOperator (Qubits N)) =
        1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp V0.property
  have htail :
      ((phaseRelativeOperator V0 V1 : HilbertOperator (Qubits N)) *
        (V0 : HilbertOperator (Qubits N))) =
        (V1 : HilbertOperator (Qubits N)) := by
    calc
      ((phaseRelativeOperator V0 V1 : HilbertOperator (Qubits N)) *
          (V0 : HilbertOperator (Qubits N))) =
          ((V1 : HilbertOperator (Qubits N)) *
            (V0 : HilbertOperator (Qubits N)).conjTranspose) *
              (V0 : HilbertOperator (Qubits N)) := by
          simp [phaseRelativeOperator, UnitaryOperator.coe_dagger]
      _ = (V1 : HilbertOperator (Qubits N)) *
            ((V0 : HilbertOperator (Qubits N)).conjTranspose *
              (V0 : HilbertOperator (Qubits N))) := by
          rw [Matrix.mul_assoc]
      _ = (V1 : HilbertOperator (Qubits N)) := by
          rw [hV0, Matrix.mul_one]
  change (UnitaryOperator.controlledQubits (phaseRelativeOperator V0 V1) :
      HilbertOperator (Qubits (1 + N))) *
      HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
        (V0 : HilbertOperator (Qubits N)) =
      HilbertOperator.tensor HilbertOperator.proj0 (V0 : HilbertOperator (Qubits N)) +
        HilbertOperator.tensor HilbertOperator.proj1 (V1 : HilbertOperator (Qubits N))
  rw [UnitaryOperator.coe_controlledQubits, Matrix.add_mul,
    HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
    Matrix.one_mul, htail]
  simp

/-- The `|+⟩` block of a controlled direct sum is the arithmetic average of its
two branches.  This is the elementary controlled-sum calculation used by the
real-polynomial projected-QSVT corollary [GSLW19, BlockHam.tex:851-887]. -/
theorem phasePlusBlock_phaseControlledDirectSum {N : Nat}
    (V0 V1 : UnitaryOperator (Qubits N)) :
    phasePlusBlock (phaseControlledDirectSumOperator V0 V1) =
      ((1 / 2 : ℂ) • (V0 : HilbertOperator (Qubits N)) +
        (1 / 2 : ℂ) • (V1 : HilbertOperator (Qubits N))) := by
  ext i j
  rw [phasePlusBlock]
  rw [phaseControlledDirectSum_eq_tensor_decomp]
  simp only [HilbertOperator.tensor_apply, HilbertOperator.proj0, HilbertOperator.proj1,
    Nat.reducePow, NormalizedVector.ketPlus_apply, Matrix.add_apply,
    Equiv.symm_apply_apply, Fin.sum_univ_two, Fin.isValue, one_div,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.smul_apply, smul_eq_mul, one_mul, zero_mul, add_zero, zero_add]
  have hstar : (starRingEnd ℂ) NormalizedVector.invSqrt2 = NormalizedVector.invSqrt2 :=
    NormalizedVector.star_invSqrt2
  rw [hstar]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [show NormalizedVector.invSqrt2 * (V0 : HilbertOperator (Qubits N)) i j *
        NormalizedVector.invSqrt2 = (2 : ℂ)⁻¹ * (V0 : HilbertOperator (Qubits N)) i j by
      rw [mul_assoc, NormalizedVector.invSqrt2_mul_mul_invSqrt2]]
  rw [show NormalizedVector.invSqrt2 * (V1 : HilbertOperator (Qubits N)) i j *
        NormalizedVector.invSqrt2 = (2 : ℂ)⁻¹ * (V1 : HilbertOperator (Qubits N)) i j by
      rw [mul_assoc, NormalizedVector.invSqrt2_mul_mul_invSqrt2]]

/-- Metadata-free selector average of two branch unitary operators. -/
noncomputable def averageProjectedBlockOperator {a n : Nat}
    (V0 V1 : UnitaryOperator (Qubits (a + n))) :
    UnitaryOperator (Qubits ((1 + a) + n)) :=
  reassociatePhaseAncillaOperator (m := a) (n := n)
    (phaseHadamardWrapperOperator (phaseControlledDirectSumOperator V0 V1))

/-- The projected block of the metadata-free selector average is the
arithmetic average of the projected branch blocks. -/
theorem projectedBlock_averageProjectedBlockOperator {a n : Nat}
    (V0 V1 : UnitaryOperator (Qubits (a + n))) :
    projectedBlock (1 + a) n
        (averageProjectedBlockOperator (a := a) (n := n) V0 V1 :
          HilbertOperator (Qubits ((1 + a) + n))) =
      (1 / 2 : ℂ) • projectedBlock a n (V0 : HilbertOperator (Qubits (a + n))) +
        (1 / 2 : ℂ) • projectedBlock a n
          (V1 : HilbertOperator (Qubits (a + n))) := by
  unfold averageProjectedBlockOperator
  rw [projectedBlock_reassociatedPhaseHadamardWrapper,
    phasePlusBlock_phaseControlledDirectSum]
  ext i j
  simp [projectedBlock, Matrix.add_apply, Matrix.smul_apply]

/-- Averaging two intrinsic unitary block encodings yields the averaged target. -/
theorem exactBlockEncoding_averageProjectedBlockOperator {a n : Nat}
    {V0 V1 : UnitaryOperator (Qubits (a + n))}
    {A0 A1 : HilbertOperator (Qubits n)}
    (h0 : ExactBlockEncoding a n V0 A0)
    (h1 : ExactBlockEncoding a n V1 A1) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockOperator (a := a) (n := n) V0 V1)
      ((1 / 2 : ℂ) • A0 + (1 / 2 : ℂ) • A1) := by
  constructor
  intro i j
  have hblock := projectedBlock_averageProjectedBlockOperator (a := a) (n := n) V0 V1
  have hentry := congrFun (congrFun hblock i) j
  simpa [h0.projected_block_eq, h1.projected_block_eq,
    Matrix.add_apply, Matrix.smul_apply] using hentry

/-- Metadata-free selector average of four branch unitary operators. -/
noncomputable def fourWayAverageProjectedBlockOperator {a n : Nat}
    (V00 V01 V10 V11 : UnitaryOperator (Qubits (a + n))) :
    UnitaryOperator (Qubits ((1 + (1 + a)) + n)) :=
  averageProjectedBlockOperator (a := 1 + a) (n := n)
    (averageProjectedBlockOperator (a := a) (n := n) V00 V01)
    (averageProjectedBlockOperator (a := a) (n := n) V10 V11)

theorem projectedBlock_fourWayAverageProjectedBlockOperator {a n : Nat}
    (V00 V01 V10 V11 : UnitaryOperator (Qubits (a + n))) :
    projectedBlock (1 + (1 + a)) n
        (fourWayAverageProjectedBlockOperator (a := a) (n := n) V00 V01 V10 V11 :
          HilbertOperator (Qubits ((1 + (1 + a)) + n))) =
      (1 / 4 : ℂ) • projectedBlock a n (V00 : HilbertOperator (Qubits (a + n))) +
        (1 / 4 : ℂ) • projectedBlock a n (V01 : HilbertOperator (Qubits (a + n))) +
      ((1 / 4 : ℂ) • projectedBlock a n (V10 : HilbertOperator (Qubits (a + n))) +
        (1 / 4 : ℂ) • projectedBlock a n
          (V11 : HilbertOperator (Qubits (a + n)))) := by
  unfold fourWayAverageProjectedBlockOperator
  rw [projectedBlock_averageProjectedBlockOperator,
    projectedBlock_averageProjectedBlockOperator,
    projectedBlock_averageProjectedBlockOperator]
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- Averaging four intrinsic unitary block encodings yields their four-way mean. -/
theorem exactBlockEncoding_fourWayAverageProjectedBlockOperator {a n : Nat}
    {V00 V01 V10 V11 : UnitaryOperator (Qubits (a + n))}
    {A00 A01 A10 A11 : HilbertOperator (Qubits n)}
    (h00 : ExactBlockEncoding a n V00 A00)
    (h01 : ExactBlockEncoding a n V01 A01)
    (h10 : ExactBlockEncoding a n V10 A10)
    (h11 : ExactBlockEncoding a n V11 A11) :
    ExactBlockEncoding (1 + (1 + a)) n
      (fourWayAverageProjectedBlockOperator (a := a) (n := n) V00 V01 V10 V11)
      ((1 / 4 : ℂ) • A00 + (1 / 4 : ℂ) • A01 +
        ((1 / 4 : ℂ) • A10 + (1 / 4 : ℂ) • A11)) := by
  constructor
  intro i j
  have hblock :=
    projectedBlock_fourWayAverageProjectedBlockOperator (a := a) (n := n)
      V00 V01 V10 V11
  have hentry := congrFun (congrFun hblock i) j
  simpa [h00.projected_block_eq, h01.projected_block_eq,
    h10.projected_block_eq, h11.projected_block_eq,
    Matrix.add_apply, Matrix.smul_apply] using hentry

/-- Global phase scaling of an intrinsic carrier scales its projected block by
the same phase. -/
theorem exactBlockEncoding_phaseScaledOperator {a n : Nat}
    {V : UnitaryOperator (Qubits (a + n))}
    {A : HilbertOperator (Qubits n)} (ζ : ℂ)
    (hζ : Complex.normSq ζ = 1) (h : ExactBlockEncoding a n V A) :
    ExactBlockEncoding a n (phaseScaledOperator ζ hζ V) (ζ • A) := by
  constructor
  intro i j
  simp [projectedBlock, phaseScaledOperatorRaw, Matrix.smul_apply,
    h.block_entry i j]

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
  change projectedBlock (1 + m) n
      (reassociatePhaseAncillaOperator (m := m) (n := n)
        (diagonalScalarDilationOperator (n := m + n) (fun _ => c) (fun _ => hc)) :
        HilbertOperator (Qubits ((1 + m) + n))) i j =
    (c • (1 : HilbertOperator (Qubits n))) i j
  rw [projectedBlock_reassociatePhaseAncillaOperator]
  unfold projectedBlock ancillaBlock diagonalScalarDilationOperator
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

/-- Intrinsic-unitary four-branch construction for a complex polynomial. -/
theorem exactBlockEncoding_complexFourPartAverageProjectedBlockOperator {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    {VReEven VReOdd VImEven VImOdd : UnitaryOperator (Qubits (a + n))}
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
      (fourWayAverageProjectedBlockOperator (a := a) (n := n)
        VReEven VReOdd
        (phaseScaledOperator Complex.I complex_normSq_I VImEven)
        (phaseScaledOperator Complex.I complex_normSq_I VImOdd))
      ((1 / 4 : ℂ) • polynomialOperator P A) := by
  have hImEvenScaled := exactBlockEncoding_phaseScaledOperator
    Complex.I complex_normSq_I hImEven
  have hImOddScaled := exactBlockEncoding_phaseScaledOperator
    Complex.I complex_normSq_I hImOdd
  have hAvg := exactBlockEncoding_fourWayAverageProjectedBlockOperator
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

/-- Intrinsic-unitary version of the real even/odd selector average. -/
theorem exactBlockEncoding_realEvenOddDoubleAverageProjectedBlockOperator {a n : Nat}
    (PRe : Polynomial ℝ) (A : HilbertOperator (Qubits n))
    {VEven VOdd : UnitaryOperator (Qubits (a + n))}
    (hEven : ExactBlockEncoding a n VEven
      (polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialEvenPart PRe)) A))
    (hOdd : ExactBlockEncoding a n VOdd
      (polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialOddPart PRe)) A)) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockOperator (a := a) (n := n) VEven VOdd)
      (polynomialOperator (realPolynomialToComplex PRe) A) := by
  have hAvg := exactBlockEncoding_averageProjectedBlockOperator
    (a := a) (n := n) hEven hOdd
  have htarget := polynomialOperator_real_evenOdd_double_average_recompose PRe A
  constructor
  intro i j
  exact (hAvg.block_entry i j).trans (congrFun (congrFun htarget i) j)

/-- Intrinsic-unitary version of the complex even/odd selector average. -/
theorem exactBlockEncoding_complexEvenOddDoubleAverageProjectedBlockOperator {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    {VEven VOdd : UnitaryOperator (Qubits (a + n))}
    (hEven : ExactBlockEncoding a n VEven
      (polynomialOperator ((2 : ℂ) • complexPolynomialEvenPart P) A))
    (hOdd : ExactBlockEncoding a n VOdd
      (polynomialOperator ((2 : ℂ) • complexPolynomialOddPart P) A)) :
    ExactBlockEncoding (1 + a) n
      (averageProjectedBlockOperator (a := a) (n := n) VEven VOdd)
      (polynomialOperator P A) := by
  have hAvg := exactBlockEncoding_averageProjectedBlockOperator
    (a := a) (n := n) hEven hOdd
  have htarget := polynomialOperator_complex_evenOdd_double_average_recompose P A
  constructor
  intro i j
  exact (hAvg.block_entry i j).trans (congrFun (congrFun htarget i) j)

end QuantumAlg.QSP.MultiQubit.QSVT
end

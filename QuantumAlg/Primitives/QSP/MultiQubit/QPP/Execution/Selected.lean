/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Complement
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Native
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Signal
public import QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Signal

/-!
# Independent complete QPP target

Laurent complement synthesis selects the phases using only the bounded
polynomial. The target is their mathematical product of rotations and
controlled source operators, with no execution or accounting metadata
[WZYW23, arxiv_v3.tex:635-666,2446-2465].
-/

namespace QuantumAlg.QSP.MultiQubit.QPP.Execution
noncomputable section

/-- Source polynomial synthesis precedes both the operator and its execution. -/
def phases {L : Nat} {coeff : Fin (2 * L + 1) → ℂ}
    (source : TrigonometricPolynomialBound L coeff) :
    GeneratedPairCertificate L coeff source.toBoundedLaurentPolynomial.complement.complement :=
  Classical.choice (generatedPairCertificate_nonempty L coeff source.toBoundedLaurentPolynomial)

lemma phases_matrix {L : Nat} {coeff : Fin (2 * L + 1) → ℂ}
    (source : TrigonometricPolynomialBound L coeff) (x : ℝ) :
    qspYZZYZ (phases source).φ (phases source).θ₀ (phases source).φ₀
        (phases source).ps x =
      qspMatYZ (2 * L) (laurentCoeffPolynomial L coeff)
        source.toBoundedLaurentPolynomial.complement.complement x := by
  simpa [(phases source).length_eq, (phases source).first_eq,
    (phases source).second_eq] using
    qspYZZYZ_eq_qspMatYZ_generatedPair (phases source).φ (phases source).θ₀
      (phases source).φ₀ (phases source).ps x

/-- A metadata-free alternating controlled source factor. -/
def sourceStep {n : Nat} (U : UnitaryOperator (Qubits n)) (index : Nat)
    (angles : ℝ × ℝ) : UnitaryOperator (Qubits (1 + n)) :=
  (if index % 2 = 0 then UnitaryOperator.controlledQubitsOnZero U⁻¹
    else UnitaryOperator.controlledQubits U) *
    (rotYOp angles.1 * rotZStdOp angles.2).tensor (1 : UnitaryOperator (Qubits n))

/-- The complete mathematical QPP operator selected solely from source phase synthesis. -/
public def target {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    UnitaryOperator (Qubits (1 + n)) :=
  let data := phases source
  data.ps.zipIdx.foldl (fun accumulated item => accumulated * sourceStep U item.2 item.1)
    ((rotZStdOp data.φ * (rotYOp data.θ₀ * rotZStdOp data.φ₀)).tensor
      (1 : UnitaryOperator (Qubits n)))

/-- The actual native word realizes the already selected phases. -/
public def word (n : Nat) {L : Nat}
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model n) (Native.layout n) :=
  Native.circuit n (phases source).φ (phases source).θ₀ (phases source).φ₀ (phases source).ps

private lemma sourceStep_realized {n : Nat} (U : UnitaryOperator (Qubits n))
    (index : Nat) (angles : ℝ × ℝ) :
    ((Native.step n index angles).binaryMatrix (QPPOracle.interpretation U))
      = sourceStep U index angles := by
  rw [Native.step_binaryMatrix]
  by_cases even : index % 2 = 0
  · rw [Native.oracle_binaryMatrix_even U even, sourceStep, if_pos even]
  · rw [Native.oracle_binaryMatrix_odd U even, sourceStep, if_neg even]

/-- Full operator equality retains every phase and every input basis vector. -/
public lemma qpp_word_target {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    ((word n source).binaryMatrix (QPPOracle.interpretation U)) = target U source := by
  simp only [word, target, Native.circuit_binaryMatrix, Native.initial_binaryMatrix,
    sourceStep_realized]

/-- The original projected-block equality holds for the same chosen native word. -/
public lemma qpp_word_projectedBlock {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    projectedBlock 1 n (((word n source).binaryMatrix (QPPOracle.interpretation U)) :
      HilbertOperator (Qubits (1 + n))) =
      unitaryLaurentPolynomial L U coeff := by
  exact projectedBlock_qppAlternatingControlledCircuit_eq_unitaryLaurentPolynomial
    L U coeff (phaseDecomposition U) (phases source).φ (phases source).θ₀
      (phases source).φ₀ (phases source).ps (phases source).length_eq
      source.toBoundedLaurentPolynomial.complement.complement (phases_matrix source)

/-- The independent full target has exactly the source polynomial as its zero-ancilla block. -/
public lemma qpp_target_projectedBlock {n L : Nat} (U : UnitaryOperator (Qubits n))
    {coeff : Fin (2 * L + 1) → ℂ} (source : TrigonometricPolynomialBound L coeff) :
    projectedBlock 1 n (target U source : HilbertOperator (Qubits (1 + n))) =
      unitaryLaurentPolynomial L U coeff := by
  rw [← qpp_word_target U source]
  exact qpp_word_projectedBlock U source

end
end QuantumAlg.QSP.MultiQubit.QPP.Execution

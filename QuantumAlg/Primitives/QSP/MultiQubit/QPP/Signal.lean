/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Components.Oracle.QPP
import all QuantumAlg.Components.Oracle.QPP
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Pair
import all QuantumAlg.Primitives.QSP.SingleQubit.Fourier

/-!
# QPP alternating circuits

YZZYZ and alternating controlled-unitary QPP words, typed circuits, and exact
strict-event resource accounting.  Every public resource fact is read from the same
`UnitaryCircuit` whose matrix supplies the semantic statement.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

private theorem qpp_phaseGateOnZeroOp_applyVec_eq_smul_rotZStdOp
    (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOnZeroOp (-θ)).applyVec ψ =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ).applyVec ψ := by
  change HilbertOperator.applyVec
    (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1)) ψ =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        HilbertOperator.applyVec (rotZStdOp θ : HilbertOperator (Qubits 1)) ψ
  rw [phaseGateOnZeroOp_signal, HilbertOperator.smul_applyVec]

private theorem qpp_phaseGateOp_applyVec_eq_smul_rotZStdOp
    (θ : ℝ) (ψ : HilbertVector (Qubits 1)) :
    (phaseGateOp θ).applyVec ψ =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ).applyVec ψ := by
  change HilbertOperator.applyVec
    (phaseGateOp θ : HilbertOperator (Qubits 1)) ψ =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        HilbertOperator.applyVec (rotZStdOp θ : HilbertOperator (Qubits 1)) ψ
  rw [phaseGateOp_signal, HilbertOperator.smul_applyVec]

/-- Exact native resources for a QPP word with `steps` controlled queries. -/
public def QPP.HasExactResourceCounts (U : UnitaryOperator (Qubits n)) (steps : ℕ)
    (resources : ResourcePool (.quantum AlgorithmGate.model (QPPOracle.model U))) : Prop :=
  QPP.Native.queryCount U resources = steps ∧
    QPP.Native.rotationCount U resources = 2 * steps + 3

/-! ### Circuit construction helpers -/

/-- Coercing a fold of certified operators exposes the corresponding raw
matrix fold without introducing a parallel proof payload. -/
private theorem unitaryFold_coe {R : Register} {α : Type}
    (schedule : List α) (start : UnitaryOperator R)
    (step : α → UnitaryOperator R) :
    ((schedule.foldl (fun accumulated item => accumulated * step item) start :
      UnitaryOperator R) : HilbertOperator R) =
      schedule.foldl
        (fun accumulated item => accumulated * (step item : HilbertOperator R))
        (start : HilbertOperator R) := by
  induction schedule generalizing start with
  | nil => rfl
  | cons item tail ih =>
      simp only [List.foldl_cons]
      simpa using ih (start * step item)

/-- Choose exactly the granted source query required by this step's parity. -/
def qppAlternatingOracleGate (U : UnitaryOperator (Qubits n)) (j : ℕ) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  QPP.Native.oracle U j

theorem qppAlternatingOracleGate_matrix_of_even
    (U : UnitaryOperator (Qubits n)) {j : ℕ} (hj : j % 2 = 0) :
    (qppAlternatingOracleGate U j).binaryMatrix =
      UnitaryOperator.controlledQubitsOnZero U⁻¹ :=
  QPP.Native.oracle_binaryMatrix_even U hj

theorem qppAlternatingOracleGate_matrix_of_odd
    (U : UnitaryOperator (Qubits n)) {j : ℕ} (hj : j % 2 ≠ 0) :
    (qppAlternatingOracleGate U j).binaryMatrix =
      UnitaryOperator.controlledQubits U :=
  QPP.Native.oracle_binaryMatrix_odd U hj

/-- Three actual front rotations on the existing signal ancilla. -/
def qppAlternatingInitialGate (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  QPP.Native.initial U φ θ₀ φ₀

/-- Metadata-free binary matrix of the same actual step circuit. -/
def qppAlternatingStepGate (U : UnitaryOperator (Qubits n)) (j : ℕ)
    (p : ℝ × ℝ) : UnitaryOperator (Qubits (1 + n)) :=
  (QPP.Native.step U j p).binaryMatrix

@[simp] theorem qppAlternatingInitialGate_operator
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    ((qppAlternatingInitialGate U φ θ₀ φ₀).binaryMatrix :
      HilbertOperator (Qubits (1 + n))) =
      HilbertOperator.tensor
        ((qspYZZYZInitialCircuit φ θ₀ φ₀).binaryMatrix : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits n)) := by
  rw [qppAlternatingInitialGate, QPP.Native.initial_binaryMatrix,
    qspYZZYZInitialCircuit_matrix]
  rfl

@[simp] theorem qppAlternatingStepGate_operator
    (U : UnitaryOperator (Qubits n)) (j : ℕ) (p : ℝ × ℝ) :
    (qppAlternatingStepGate U j p : HilbertOperator (Qubits (1 + n))) =
      ((qppAlternatingOracleGate U j).binaryMatrix :
        HilbertOperator (Qubits (1 + n))) *
        ((QPP.Native.processingPair U p).binaryMatrix :
          HilbertOperator (Qubits (1 + n))) := by
  rw [qppAlternatingStepGate, QPP.Native.step_binaryMatrix,
    QPP.Native.processingPair_binaryMatrix]
  rfl

/-! ### Direct YZZYZ QPP and eigenspace decomposition -/

/-- The mathematical YZZYZ QPP word.  Its typed realization below carries all
execution and resource metadata. -/
def qppYZZYZ (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryOperator (Qubits (1 + n)) :=
  ps.foldl
    (fun W p =>
      W * (UnitaryOperator.controlledQubits U *
        (rotYOp p.1 * rotZStdOp p.2).tensor
          (1 : UnitaryOperator (Qubits n))))
    ((rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)).tensor
      (1 : UnitaryOperator (Qubits n)))

@[simp] theorem qppYZZYZ_nil (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    qppYZZYZ U φ θ₀ φ₀ [] =
      (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)).tensor
        (1 : UnitaryOperator (Qubits n)) := rfl

theorem qppYZZYZ_concat (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    qppYZZYZ U φ θ₀ φ₀ (ps ++ [p]) =
      qppYZZYZ U φ θ₀ φ₀ ps *
        (UnitaryOperator.controlledQubits U *
          (rotYOp p.1 * rotZStdOp p.2).tensor
            (1 : UnitaryOperator (Qubits n))) := by
  simp [qppYZZYZ, List.foldl_append]

/-- Typed circuit whose matrix is the YZZYZ QPP word. -/
def qppYZZYZCircuit (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  QPP.Native.directCircuit U φ θ₀ φ₀ ps

@[simp] theorem qppYZZYZCircuit_matrix (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    (qppYZZYZCircuit U φ θ₀ φ₀ ps).binaryMatrix =
      qppYZZYZ U φ θ₀ φ₀ ps := by
  simp only [qppYZZYZCircuit, QPP.Native.directCircuit_binaryMatrix,
    QPP.Native.directStep_binaryMatrix, QPP.Native.initial_binaryMatrix, qppYZZYZ]

/-- Eigenspace decomposition of direct-controlled YZZYZ QPP. -/
theorem QPP.eigenstate_decomposition (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length •
          HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ)
        (u : HilbertVector (Qubits n)) := by
  induction ps using List.reverseRecOn generalizing ψ with
  | nil =>
      rw [qppYZZYZ_nil, qspYZZYZ_nil, List.length_nil, pow_zero, one_smul,
        UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec]
      change HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
              ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
                (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))) ψ)
          (u : HilbertVector (Qubits n)) =
        HilbertVector.tensor
          (HilbertOperator.applyVec
            ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
              ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
                (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))) ψ)
          (u : HilbertVector (Qubits n))
      rfl
  | append_singleton ps p ih =>
      rw [qppYZZYZ_concat, UnitaryOperator.mul_applyVec,
        UnitaryOperator.mul_applyVec, UnitaryOperator.tensor_applyVec_tensor,
        UnitaryOperator.one_applyVec]
      have hsignal :
          (UnitaryOperator.controlledQubits U).applyVec
              (HilbertVector.tensor
                ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ)
                (u : HilbertVector (Qubits n))) =
            HilbertVector.tensor
              (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
                (rotZStdOp θ).applyVec
                  ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ))
              (u : HilbertVector (Qubits n)) := by
        exact QPP.eigenstate_reductionVec U u θ hu
          ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ)
      rw [hsignal, ih, qspYZZYZ_concat, List.length_append,
        List.length_singleton]
      congr 1
      change
        (Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ ps.length •
            HilbertOperator.applyVec
              (qspYZZYZ φ θ₀ φ₀ ps θ : HilbertOperator (Qubits 1))
              (Complex.exp ((θ / 2 : ℝ) * Complex.I) •
                HilbertOperator.applyVec
                  (rotZStdOp θ : HilbertOperator (Qubits 1))
                  (HilbertOperator.applyVec
                    ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                      (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)) =
          (Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ (ps.length + 1) •
            HilbertOperator.applyVec
              ((qspYZZYZ φ θ₀ φ₀ ps θ : HilbertOperator (Qubits 1)) *
                ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
                  ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                    (rotZStdOp p.2 : HilbertOperator (Qubits 1))))) ψ
      rw [HilbertOperator.applyVec_smul, smul_smul, ← pow_succ,
        ← HilbertOperator.mul_applyVec, ← HilbertOperator.mul_applyVec, mul_assoc]

/-- Every admissible single-qubit QSP transform is realized on an eigenspace. -/
theorem QPP.realizes_target (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n))
    (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
      ∀ ψ : NormalizedVector (Qubits 1),
        (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L •
              HilbertOperator.applyVec (qspMatYZ L A B θ)
                (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main L A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [QPP.eigenstate_decomposition U u θ hu, hlen]
  have happly := congrArg
    (fun M : HilbertOperator (Qubits 1) =>
      HilbertOperator.applyVec M (ψ : HilbertVector (Qubits 1))) (hmat θ)
  exact congrArg
    (fun v : HilbertVector (Qubits 1) =>
      HilbertVector.tensor
        ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L • v)
        (u : HilbertVector (Qubits n))) happly

/-! ### Exact resources of the typed words -/

/-- The direct word's exact counts come from its actual native circuit ledger. -/
theorem qppYZZYZCircuit_resources_exact (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    QPP.HasExactResourceCounts U ps.length
      (qppYZZYZCircuit U φ θ₀ φ₀ ps).eventCost := by
  simpa only [QPP.HasExactResourceCounts, qppYZZYZCircuit] using
    QPP.Native.directCircuit_counts U φ θ₀ φ₀ ps

/-- The direct YZZYZ correctness theorem paired with resources from the same
typed circuit. -/
theorem qpp_realizes_target_with_resources (U : UnitaryOperator (Qubits n))
    (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair L A B) :
    ∃ (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)), ps.length = L ∧
      (∀ ψ : NormalizedVector (Qubits 1),
        (qppYZZYZ U φ θ₀ φ₀ ps).applyVec
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            ((Complex.exp ((θ / 2 : ℝ) * Complex.I)) ^ L •
              HilbertOperator.applyVec (qspMatYZ L A B θ)
                (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n))) ∧
      QPP.HasExactResourceCounts U L
        (qppYZZYZCircuit U φ θ₀ φ₀ ps).eventCost := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hcorrect⟩ :=
    QPP.realizes_target U u θ hu L A B h
  refine ⟨φ, θ₀, φ₀, ps, hlen, hcorrect, ?_⟩
  simpa [hlen] using qppYZZYZCircuit_resources_exact U φ θ₀ φ₀ ps

/-! ### Alternating source convention -/

/-- Typed circuit for the alternating controlled-`U†` / controlled-`U` word. -/
def qppAlternatingControlledCircuit (U : UnitaryOperator (Qubits n))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    UnitaryCircuit AlgorithmGate.model (QPPOracle.model U)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  QPP.Native.circuit U φ θ₀ φ₀ ps

/-- The empty alternating schedule evaluates the three-gate initial circuit. -/
@[simp] theorem qppAlternatingControlledCircuit_nil_matrix
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    (qppAlternatingControlledCircuit U φ θ₀ φ₀ []).binaryMatrix =
      (qppAlternatingInitialGate U φ θ₀ φ₀).binaryMatrix := rfl

/-- Exact controlled queries and one-qubit gates of the alternating circuit. -/
theorem qppAlternatingControlledCircuit_resources_exact
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    QPP.HasExactResourceCounts U ps.length
      (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).eventCost := by
  simpa only [QPP.HasExactResourceCounts, qppAlternatingControlledCircuit] using
    QPP.Native.circuit_counts U φ θ₀ φ₀ ps

/-! ### Alternating eigenspace semantics -/

/-- One source-aligned alternating step reduces to the corresponding one-qubit
phase signal on an eigenstate. -/
theorem QPP.qppAlternatingStep_eigenstate_reductionVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (j : ℕ) (p : ℝ × ℝ) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingStepGate U j p).applyVec
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        (HilbertOperator.applyVec
          (if j % 2 = 0 then
            (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
          else (phaseGateOp θ : HilbertOperator (Qubits 1)))
          (HilbertOperator.applyVec
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ))
        (u : HilbertVector (Qubits n)) := by
  change HilbertOperator.applyVec
      (qppAlternatingStepGate U j p : HilbertOperator (Qubits (1 + n)))
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) = _
  rw [qppAlternatingStepGate_operator, HilbertOperator.mul_applyVec,
    QPP.Native.processingPair_binaryMatrix, UnitaryOperator.coe_tensor,
    HilbertOperator.tensor_applyVec_tensor]
  have hunit : HilbertOperator.applyVec
      ((1 : UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n))
      (u : HilbertVector (Qubits n)) = (u : HilbertVector (Qubits n)) := by
    change (1 : UnitaryOperator (Qubits n)).applyVec
      (u : HilbertVector (Qubits n)) = _
    exact UnitaryOperator.one_applyVec _
  rw [hunit]
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, qppAlternatingOracleGate_matrix_of_even U hj]
    exact QPP.controlledOnZero_conjTranspose_apply_eigenstate_phaseVec
      U u θ hu
      (HilbertOperator.applyVec
        ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
          (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)
  · rw [if_neg hj, qppAlternatingOracleGate_matrix_of_odd U hj]
    exact controlled_apply_eigenstate_phaseVec U u θ hu
      (HilbertOperator.applyVec
        ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
          (rotZStdOp p.2 : HilbertOperator (Qubits 1))) ψ)

/-- The one-qubit signal step induced on an eigenspace. -/
def qppAlternatingSignalStep (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) :
    UnitaryOperator (Qubits 1) :=
  (if j % 2 = 0 then
      phaseGateOnZeroOp (-θ)
    else phaseGateOp θ) *
    (rotYOp p.1 * rotZStdOp p.2)

/-- Global phase of the `j`-th alternating signal block. -/
def qppAlternatingStepScalar (θ : ℝ) (j : ℕ) : ℂ :=
  if j % 2 = 0 then Complex.exp (-(θ / 2 : ℝ) * Complex.I)
  else Complex.exp ((θ / 2 : ℝ) * Complex.I)

/-- Product of alternating-step global phases, beginning at `start`. -/
def qppAlternatingSignalScalarFrom (θ : ℝ) (start : ℕ) :
    List (ℝ × ℝ) → ℂ
  | [] => 1
  | _ :: rest => qppAlternatingStepScalar θ start *
      qppAlternatingSignalScalarFrom θ (start + 1) rest

/-- Total global phase of a zero-based alternating signal sequence. -/
def qppAlternatingSignalScalar (θ : ℝ) (ps : List (ℝ × ℝ)) : ℂ :=
  qppAlternatingSignalScalarFrom θ 0 ps

theorem QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step
    (θ : ℝ) (j : ℕ) (p : ℝ × ℝ) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalStep θ j p).applyVec ψ =
      qppAlternatingStepScalar θ j •
        HilbertOperator.applyVec
          ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
            ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
              (rotZStdOp p.2 : HilbertOperator (Qubits 1)))) ψ := by
  rw [qppAlternatingSignalStep, UnitaryOperator.mul_applyVec]
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, qppAlternatingStepScalar, if_pos hj]
    change (phaseGateOnZeroOp (-θ)).applyVec
        ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) =
      Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ * (rotYOp p.1 * rotZStdOp p.2)).applyVec ψ
    have hnegHalf :
        Complex.exp (((-θ) / 2 : ℝ) * Complex.I) =
          Complex.exp (-(θ / 2 : ℝ) * Complex.I) := by
      congr 1
      push_cast
      ring_nf
    calc
      _ = Complex.exp (((-θ) / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) := by
        rw [hnegHalf]
        exact qpp_phaseGateOnZeroOp_applyVec_eq_smul_rotZStdOp θ _
      _ = Complex.exp (-(θ / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) := by rw [hnegHalf]
      _ = _ := congrArg
        (fun v : HilbertVector (Qubits 1) =>
          Complex.exp (-(θ / 2 : ℝ) * Complex.I) • v)
        (UnitaryOperator.mul_applyVec (rotZStdOp θ)
          (rotYOp p.1 * rotZStdOp p.2) ψ).symm
  · rw [if_neg hj, qppAlternatingStepScalar, if_neg hj]
    change (phaseGateOp θ).applyVec
        ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) =
      Complex.exp ((θ / 2 : ℝ) * Complex.I) •
        (rotZStdOp θ * (rotYOp p.1 * rotZStdOp p.2)).applyVec ψ
    calc
      _ = Complex.exp ((θ / 2 : ℝ) * Complex.I) •
          (rotZStdOp θ).applyVec
            ((rotYOp p.1 * rotZStdOp p.2).applyVec ψ) :=
        qpp_phaseGateOp_applyVec_eq_smul_rotZStdOp θ _
      _ = _ := congrArg
        (fun v : HilbertVector (Qubits 1) =>
          Complex.exp ((θ / 2 : ℝ) * Complex.I) • v)
        (UnitaryOperator.mul_applyVec (rotZStdOp θ)
          (rotYOp p.1 * rotZStdOp p.2) ψ).symm

/-- Alternating one-qubit signal word on one eigenphase. -/
def qppAlternatingSignalGate (θ φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) : UnitaryOperator (Qubits 1) :=
  ps.zipIdx.foldl
    (fun W jp => W * qppAlternatingSignalStep θ jp.2 jp.1)
    (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀))

theorem qppAlternatingSignalGate_eq_foldlIdx
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) :
    qppAlternatingSignalGate θ φ θ₀ φ₀ ps =
      ps.foldlIdx (fun j W p => W * qppAlternatingSignalStep θ j p)
        (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀)) 0 := by
  rw [qppAlternatingSignalGate, List.foldlIdx_eq_foldl_zipIdx]

@[simp]
theorem coe_qppAlternatingSignalGate (θ φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps :
      HilbertOperator (Qubits 1)) =
      ps.zipIdx.foldl
        (fun W jp => W *
          (qppAlternatingSignalStep θ jp.2 jp.1 :
            HilbertOperator (Qubits 1)))
        ((rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀) :
          UnitaryOperator (Qubits 1)) : HilbertOperator (Qubits 1)) := by
  exact unitaryFold_coe ps.zipIdx
    (rotZStdOp φ * (rotYOp θ₀ * rotZStdOp φ₀))
    (fun jp => qppAlternatingSignalStep θ jp.2 jp.1)

theorem QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ)
    (W Q : HilbertOperator (Qubits 1)) (c : ℂ)
    (hW : ∀ ψ : HilbertVector (Qubits 1),
      HilbertOperator.applyVec W ψ = c • HilbertOperator.applyVec Q ψ)
    (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        (ps.foldlIdx
          (fun j W p => W *
            (qppAlternatingSignalStep θ j p : HilbertOperator (Qubits 1)))
          W start) ψ =
      (c * qppAlternatingSignalScalarFrom θ start ps) •
        HilbertOperator.applyVec
          (ps.foldl
            (fun Q p => Q *
              ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
                ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                  (rotZStdOp p.2 : HilbertOperator (Qubits 1))))) Q) ψ := by
  induction ps generalizing start W Q c ψ with
  | nil => simpa [qppAlternatingSignalScalarFrom] using hW ψ
  | cons p ps ih =>
      simp only [List.foldlIdx_cons, List.foldl_cons,
        qppAlternatingSignalScalarFrom]
      have hnext := ih (start + 1)
        (W * (qppAlternatingSignalStep θ start p :
          HilbertOperator (Qubits 1)))
        (Q * ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
          ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
            (rotZStdOp p.2 : HilbertOperator (Qubits 1)))))
        (c * qppAlternatingStepScalar θ start)
        (by
          intro ψ'
          rw [HilbertOperator.mul_applyVec]
          change HilbertOperator.applyVec W
            ((qppAlternatingSignalStep θ start p).applyVec ψ') = _
          rw [QPP.qppAlternatingSignalStep_applyVec_eq_scalar_yzzyz_step,
            HilbertOperator.applyVec_smul, hW, HilbertOperator.mul_applyVec]
          rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
            HilbertOperator.mul_applyVec]
          simp only [smul_smul]
          rw [mul_comm (qppAlternatingStepScalar θ start) c]
          exact congrArg
            (fun v : HilbertVector (Qubits 1) =>
              (c * qppAlternatingStepScalar θ start) •
                HilbertOperator.applyVec Q
                  (HilbertOperator.applyVec
                    (rotZStdOp θ : HilbertOperator (Qubits 1)) v))
            (HilbertOperator.mul_applyVec
              (rotYOp p.1 : HilbertOperator (Qubits 1))
              (rotZStdOp p.2 : HilbertOperator (Qubits 1)) ψ').symm) ψ
      simpa [mul_assoc] using hnext

theorem qppAlternatingStepScalar_mul_succ (θ : ℝ) (j : ℕ) :
    qppAlternatingStepScalar θ j * qppAlternatingStepScalar θ (j + 1) = 1 := by
  unfold qppAlternatingStepScalar
  by_cases hj : j % 2 = 0
  · have hj1 : (j + 1) % 2 ≠ 0 := by omega
    rw [if_pos hj, if_neg hj1, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]
  · have hj1 : (j + 1) % 2 = 0 := by omega
    rw [if_neg hj, if_pos hj1, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]

theorem qppAlternatingSignalScalarFrom_eq_if_length_mod
    (θ : ℝ) (ps : List (ℝ × ℝ)) (start : ℕ) :
    qppAlternatingSignalScalarFrom θ start ps =
      if ps.length % 2 = 0 then 1 else qppAlternatingStepScalar θ start := by
  induction ps generalizing start with
  | nil => simp [qppAlternatingSignalScalarFrom]
  | cons p rest ih =>
      rw [qppAlternatingSignalScalarFrom, ih (start + 1)]
      by_cases hrest : rest.length % 2 = 0
      · have htotal : (rest.length + 1) % 2 ≠ 0 := by omega
        simp [hrest, htotal]
      · have htotal : (rest.length + 1) % 2 = 0 := by omega
        simp [hrest, htotal, qppAlternatingStepScalar_mul_succ θ start]

theorem qppAlternatingSignalScalar_eq_one_of_even_length
    (θ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (h : ps.length = 2 * L) : qppAlternatingSignalScalar θ ps = 1 := by
  have hmod : ps.length % 2 = 0 := by rw [h]; omega
  simp [qppAlternatingSignalScalar,
    qppAlternatingSignalScalarFrom_eq_if_length_mod θ ps 0, hmod]

theorem QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      qppAlternatingSignalScalar θ ps •
        HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ := by
  have h := QPP.qppAlternatingSignal_fold_applyVec_eq_scalar_yzzyz_fold
    θ ps 0
    ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
    ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
    (1 : ℂ) (by intro ψ'; simp) ψ
  change HilbertOperator.applyVec
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps : HilbertOperator (Qubits 1)) ψ = _
  rw [List.foldlIdx_eq_foldl_zipIdx] at h
  rw [coe_qppAlternatingSignalGate]
  change HilbertOperator.applyVec
      (ps.zipIdx.foldl
        (fun W jp => W *
          (qppAlternatingSignalStep θ jp.2 jp.1 : HilbertOperator (Qubits 1)))
        ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
          ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
            (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))) ψ =
    qppAlternatingSignalScalar θ ps •
      HilbertOperator.applyVec
        (ps.foldl
          (fun Q p => Q *
            ((rotZStdOp θ : HilbertOperator (Qubits 1)) *
              ((rotYOp p.1 : HilbertOperator (Qubits 1)) *
                (rotZStdOp p.2 : HilbertOperator (Qubits 1)))))
          ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
            ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
              (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))) ψ
  simpa only [qppAlternatingSignalScalar, one_mul] using h

theorem QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length
    (θ φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (hps : ps.length = 2 * L) (ψ : HilbertVector (Qubits 1)) :
    (qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ =
      HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ := by
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_scalar_yzzyz]
  rw [qppAlternatingSignalScalar_eq_one_of_even_length θ ps hps]
  simp

private theorem qppAlternatingControlledCircuit_algebraic_matrix
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ)
    (ps : List (ℝ × ℝ)) :
    (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).binaryMatrix =
      ps.zipIdx.foldl
        (fun W jp => W *
          qppAlternatingStepGate U jp.2 jp.1)
        (qppAlternatingInitialGate U φ θ₀ φ₀).binaryMatrix := by
  rw [qppAlternatingControlledCircuit, QPP.Native.circuit_binaryMatrix]
  rfl

/-- Source-aligned eigenspace decomposition of the alternating circuit. -/
theorem QPP.qppAlternating_eigenstate_decompositionVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℝ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).binaryMatrix :
          HilbertOperator (Qubits (1 + n)))
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        ((qppAlternatingSignalGate θ φ θ₀ φ₀ ps).applyVec ψ)
        (u : HilbertVector (Qubits n)) := by
  let schedule := ps.zipIdx
  let initialSignal : HilbertOperator (Qubits 1) :=
    (rotZStdOp φ : HilbertOperator (Qubits 1)) *
      ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
        (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))
  let initialGate : HilbertOperator (Qubits (1 + n)) :=
    (qppAlternatingInitialGate U φ θ₀ φ₀).binaryMatrix
  have hfold : ∀ (schedule : List ((ℝ × ℝ) × ℕ))
      (W : HilbertOperator (Qubits (1 + n)))
      (S : HilbertOperator (Qubits 1)),
      (∀ ψ : HilbertVector (Qubits 1),
        HilbertOperator.applyVec W
            (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor (HilbertOperator.applyVec S ψ)
            (u : HilbertVector (Qubits n))) →
      ∀ ψ : HilbertVector (Qubits 1),
        HilbertOperator.applyVec
            (schedule.foldl
              (fun W jp => W *
                (qppAlternatingStepGate U jp.2 jp.1 :
                  HilbertOperator (Qubits (1 + n)))) W)
            (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            (HilbertOperator.applyVec
              (schedule.foldl
                (fun S jp => S *
                  (qppAlternatingSignalStep θ jp.2 jp.1 :
                    HilbertOperator (Qubits 1))) S) ψ)
            (u : HilbertVector (Qubits n)) := by
    intro schedule
    induction schedule with
    | nil => intro W S hbase ψ; exact hbase ψ
    | cons jp rest ih =>
        intro W S hbase ψ
        apply ih
        intro ψ'
        rw [HilbertOperator.mul_applyVec]
        have hstep := QPP.qppAlternatingStep_eigenstate_reductionVec
          U u θ hu jp.2 jp.1 ψ'
        change HilbertOperator.applyVec
            (qppAlternatingStepGate U jp.2 jp.1 :
              HilbertOperator (Qubits (1 + n)))
            (HilbertVector.tensor ψ' (u : HilbertVector (Qubits n))) = _ at hstep
        rw [show HilbertOperator.applyVec
            (qppAlternatingStepGate U jp.2 jp.1 :
              HilbertOperator (Qubits (1 + n)))
              (HilbertVector.tensor ψ' (u : HilbertVector (Qubits n))) =
            HilbertVector.tensor
              (HilbertOperator.applyVec
                (qppAlternatingSignalStep θ jp.2 jp.1 :
                  HilbertOperator (Qubits 1)) ψ')
              (u : HilbertVector (Qubits n)) by
          by_cases hj : jp.2 % 2 = 0
          · calc
              _ = HilbertVector.tensor
                    (HilbertOperator.applyVec
                      (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
                      (HilbertOperator.applyVec
                        ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                          (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ'))
                    (u : HilbertVector (Qubits n)) := by
                      simpa only [if_pos hj] using hstep
                _ = _ := by
                      rw [qppAlternatingSignalStep, if_pos hj]
                      exact congrArg
                        (fun v : HilbertVector (Qubits 1) =>
                          HilbertVector.tensor v (u : HilbertVector (Qubits n)))
                        (HilbertOperator.mul_applyVec
                          (phaseGateOnZeroOp (-θ) : HilbertOperator (Qubits 1))
                          ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                            (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ').symm
          · calc
              _ = HilbertVector.tensor
                    (HilbertOperator.applyVec
                      (phaseGateOp θ : HilbertOperator (Qubits 1))
                      (HilbertOperator.applyVec
                        ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                          (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ'))
                    (u : HilbertVector (Qubits n)) := by
                      simpa only [if_neg hj] using hstep
                _ = _ := by
                      rw [qppAlternatingSignalStep, if_neg hj]
                      exact congrArg
                        (fun v : HilbertVector (Qubits 1) =>
                          HilbertVector.tensor v (u : HilbertVector (Qubits n)))
                        (HilbertOperator.mul_applyVec
                          (phaseGateOp θ : HilbertOperator (Qubits 1))
                          ((rotYOp jp.1.1 : HilbertOperator (Qubits 1)) *
                            (rotZStdOp jp.1.2 : HilbertOperator (Qubits 1))) ψ').symm]
        rw [hbase, HilbertOperator.mul_applyVec]
  have hbase : ∀ ψ : HilbertVector (Qubits 1),
      HilbertOperator.applyVec initialGate
          (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
        HilbertVector.tensor (HilbertOperator.applyVec initialSignal ψ)
          (u : HilbertVector (Qubits n)) := by
    intro ψ
    dsimp [initialGate, initialSignal]
    rw [qppAlternatingInitialGate_operator,
      qspYZZYZInitialCircuit_matrix,
      HilbertOperator.tensor_applyVec_tensor,
      HilbertOperator.one_applyVec]
  change HilbertOperator.applyVec
      ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).binaryMatrix :
        HilbertOperator (Qubits (1 + n)))
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor
      (HilbertOperator.applyVec
        (qppAlternatingSignalGate θ φ θ₀ φ₀ ps :
          HilbertOperator (Qubits 1)) ψ)
      (u : HilbertVector (Qubits n))
  rw [qppAlternatingControlledCircuit_algebraic_matrix]
  rw [unitaryFold_coe, coe_qppAlternatingSignalGate]
  let controlledFold : HilbertOperator (Qubits (1 + n)) :=
    ps.zipIdx.foldl
      (fun W jp => W *
        (qppAlternatingStepGate U jp.2 jp.1 :
          HilbertOperator (Qubits (1 + n))))
      ((qppAlternatingInitialGate U φ θ₀ φ₀).binaryMatrix :
        HilbertOperator (Qubits (1 + n)))
  let signalFold : HilbertOperator (Qubits 1) :=
    ps.zipIdx.foldl
      (fun S jp => S *
        (qppAlternatingSignalStep θ jp.2 jp.1 : HilbertOperator (Qubits 1)))
      ((rotZStdOp φ : HilbertOperator (Qubits 1)) *
        ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
          (rotZStdOp φ₀ : HilbertOperator (Qubits 1))))
  change HilbertOperator.applyVec controlledFold
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor (HilbertOperator.applyVec signalFold ψ)
      (u : HilbertVector (Qubits n))
  have h := hfold schedule initialGate initialSignal hbase ψ
  change HilbertOperator.applyVec controlledFold
      (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
    HilbertVector.tensor (HilbertOperator.applyVec signalFold ψ)
      (u : HilbertVector (Qubits n)) at h
  exact h

theorem QPP.qppAlternating_eigenstate_decomposition_evenVec
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ)) {L : ℕ}
    (hps : ps.length = 2 * L) (ψ : HilbertVector (Qubits 1)) :
    HilbertOperator.applyVec
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).binaryMatrix :
          HilbertOperator (Qubits (1 + n)))
        (HilbertVector.tensor ψ (u : HilbertVector (Qubits n))) =
      HilbertVector.tensor
        (HilbertOperator.applyVec (qspYZZYZ φ θ₀ φ₀ ps θ) ψ)
        (u : HilbertVector (Qubits n)) := by
  rw [QPP.qppAlternating_eigenstate_decompositionVec U u θ hu]
  rw [QPP.qppAlternatingSignalGate_applyVec_eq_yzzyz_of_even_length
    θ φ θ₀ φ₀ ps hps]

theorem QPP.alternating_realizes_target_on_eigenstate
    (U : UnitaryOperator (Qubits n)) (u : NormalizedVector (Qubits n)) (θ : ℝ)
    (hu : U.applyVec (u : HilbertVector (Qubits n)) =
      Complex.exp ((θ : ℂ) * Complex.I) • (u : HilbertVector (Qubits n)))
    (L : ℕ) (A B : Polynomial ℂ) (h : IsYZPair (2 * L) A B) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ), ps.length = 2 * L ∧
      ∀ ψ : NormalizedVector (Qubits 1),
        HilbertOperator.applyVec
            ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).binaryMatrix :
              HilbertOperator (Qubits (1 + n)))
            (HilbertVector.tensor (ψ : HilbertVector (Qubits 1))
              (u : HilbertVector (Qubits n))) =
          HilbertVector.tensor
            (HilbertOperator.applyVec (qspMatYZ (2 * L) A B θ)
              (ψ : HilbertVector (Qubits 1)))
            (u : HilbertVector (Qubits n)) := by
  obtain ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩ :=
    (TrigonometricQuantumSignalProcessing.main (2 * L) A B).mp h
  refine ⟨φ, θ₀, φ₀, ps, hlen, fun ψ => ?_⟩
  rw [QPP.qppAlternating_eigenstate_decomposition_evenVec
    U u θ hu φ θ₀ φ₀ ps hlen]
  exact congrArg
    (fun v : HilbertVector (Qubits 1) =>
      HilbertVector.tensor v (u : HilbertVector (Qubits n)))
    (congrArg
      (fun M : HilbertOperator (Qubits 1) =>
        HilbertOperator.applyVec M (ψ : HilbertVector (Qubits 1))) (hmat θ))


end

end QSP.MultiQubit

end QuantumAlg

end

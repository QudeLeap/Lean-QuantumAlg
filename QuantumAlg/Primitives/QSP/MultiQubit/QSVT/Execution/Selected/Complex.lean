/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Real
public import QuantumAlg.Components.Oracle.BlockEncoding
public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Regroup
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Matrix
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Gates
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Depth
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Word
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Block
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Normalized
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Depth

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected

import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Certificate

/-!
# Independently selected complex Hermitian target

Polynomial-only synthesis selects real angles and a list before any encoded
operator. One certificate covers every Hermitian block encoding. The full
operator is an intrinsic four-branch average. Its
width is fixed by the degree boundary before any executable word is chosen.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected
open SharedFour Gate.Toffoli
noncomputable section

/-- Mathematical four-branch phase data, containing no circuit or resource witness. -/
public structure ComplexPhases where
  /-- Shared phase slots for the four mathematical polynomial branches. -/
  phases : List ((ℝ × ℝ) × (ℝ × ℝ))
  /-- Unmatched phase of the longer real branch. -/
  realAngle : ℝ
  /-- Unmatched phase of the longer imaginary branch. -/
  imaginaryAngle : ℝ
  /-- Scalar initialization of the shorter real branch. -/
  realConstant : ℝ
  /-- Scalar initialization of the shorter imaginary branch. -/
  imaginaryConstant : ℝ

/-- A mathematical initialized branch on the original source register. -/
public def initializedOperator {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (phases : List ℝ) (constant : ℝ) : UnitaryOperator (Qubits (1 + (m + n))) :=
  phaseControlledDirectSumOperator
      (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) phases)
      (Native.sourceWord U (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n) (negPhases phases)) *
    (rotZOp (Real.arccos constant)).tensor 1

/-- The complete mathematical four-branch average, including the imaginary relative phase. -/
public def complexPhaseOperator {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (data : ComplexPhases) : UnitaryOperator (Qubits (1 + (1 + (1 + (m + n))))) :=
  threeAverage
    (initializedOperator U (data.phases.map fun a => a.1.1) data.realConstant)
    (initializedOperator U (data.realAngle :: data.phases.map fun a => a.1.2) 1)
    (phaseScaledOperator Complex.I complex_normSq_I
      (initializedOperator U (data.phases.map fun a => a.2.1) data.imaginaryConstant))
    (phaseScaledOperator Complex.I complex_normSq_I
      (initializedOperator U (data.imaginaryAngle :: data.phases.map fun a => a.2.2) 1))

private lemma complexWord_operator {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (data : ComplexPhases) :
    ((KnownZero.Total.Four.complexWord (m := m) (n := n) data.phases data.realAngle
      data.imaginaryAngle
      data.realConstant data.imaginaryConstant).binaryMatrix
        (UnitarySource.interpretation U true true false)) = complexPhaseOperator U data := by
  rw [KnownZero.Total.Four.totalComplexWord_average_operator]
  simp only [KnownZero.Total.Four.initializedBranch, KnownZero.Total.totalCircuit_matrix,
    Native.circuit_source_operator, Shared.constantInitial,
    Gate.singleQubitAt_first_binaryMatrix, complexPhaseOperator, initializedOperator]

/-- Pure mathematical correctness and length certificate for four-branch synthesis. -/
public def ComplexPhaseCertificate {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (A : HilbertOperator (Qubits n)) (P : Polynomial ℂ) (L : Nat)
    (data : ComplexPhases) : Prop :=
  data.phases.length = L - 1 ∧
    ExactBlockEncoding (1 + (1 + (1 + m))) n
      (reassociateThree (complexPhaseOperator U data)) ((1 / 4 : ℂ) • polynomialOperator P A)

private lemma complex_phase_certificate_exists {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L) (positive : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ data : ComplexPhases, data.phases.length = L - 1 ∧
      ∀ (m n : Nat) (U : UnitaryOperator (Qubits (m + n)))
        (A : HilbertOperator (Qubits n)), ExactBlockEncoding m n U A → A.IsHermitian →
          ComplexPhaseCertificate U A P L data := by
  obtain ⟨phases, ra, ia, rc, ic, length, correct⟩ :=
    KnownZero.Total.Four.exists_total_complex_polynomial_execution P degree positive bounded
  refine ⟨⟨phases, ra, ia, rc, ic⟩, length, ?_⟩
  intro m n U A encoding hermitian
  obtain ⟨block, _⟩ := correct m n U A encoding hermitian
  refine ⟨length, ?_⟩
  have matrix := complexWord_operator U (⟨phases, ra, ia, rc, ic⟩ : ComplexPhases)
  change ((KnownZero.Total.Four.complexWord (m := m) (n := n) phases ra ia rc ic).binaryMatrix
    (UnitarySource.interpretation U true true false)) = _ at matrix
  rw [matrix] at block
  exact ⟨fun row column => congrFun (congrFun block row) column⟩

/-- Select phases solely from the polynomial, uniformly over all encoded operators. -/
public def complexPhases {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L) (positive : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexPhases :=
  Classical.choose (complex_phase_certificate_exists P degree positive bounded)

lemma complexPhases_length {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L) (positive : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    (complexPhases P degree positive bounded).phases.length = L - 1 :=
  (Classical.choose_spec (complex_phase_certificate_exists P degree positive bounded)).1

lemma complexPhases_correct {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L) (positive : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ComplexPhaseCertificate U A P L
      (complexPhases P degree positive bounded) :=
  (Classical.choose_spec (complex_phase_certificate_exists P degree positive bounded)).2
    m n U A encoding hermitian

/-- Public ancilla width, determined before any source interpretation. -/
@[expose, implicit_reducible] public def complexAncillas (m L : Nat) : Nat :=
  match L with
  | 0 => 1 + m
  | _ + 1 => 1 + (1 + (1 + m))

/-- Full independent target, with one added ancilla at zero degree and three otherwise. -/
public def complexTarget {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n)))
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    UnitaryOperator (Qubits (complexAncillas m L + n)) :=
  match L, degree with
  | 0, _ =>
    scalarDilationWithSourceAncillas (m := m) (n := n)
      ((1 / 4 : ℂ) * P.coeff 0) (Scalar.quarter_coefficient_bound P bounded)
  | k + 1, degree =>
    reassociateThree (m := m) (n := n)
      (complexPhaseOperator U (complexPhases P degree (Nat.succ_pos k) bounded))

/-- The chosen width is a closed function of the source width and the degree boundary. -/
public lemma complexTarget_width (m L : Nat) :
    complexAncillas m L = m + if L = 0 then 1 else 3 := by
  cases L <;> simp [complexAncillas] <;> omega

/-- The full independently selected target retains the source normalized polynomial block. -/
public lemma complexTarget_block {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ExactBlockEncoding (complexAncillas m L) n (complexTarget U P degree bounded)
      ((1 / 4 : ℂ) • polynomialOperator P A) := by
  cases L with
  | zero =>
    simp only [complexTarget, complexAncillas]
    rw [polynomialOperator_eq_scalar_one_of_natDegree_eq_zero P A
      (Nat.eq_zero_of_le_zero degree), smul_smul]
    exact exactBlockEncoding_scalarDilationWithSourceAncillas _ _
  | succ k =>
    exact (complexPhases_correct U A encoding hermitian P degree (Nat.succ_pos k) bounded).2

/-- Exact realization of the selected mathematical target with the original native budget. -/
lemma exists_complex_target_execution (m n : Nat) {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false)
        (QuantumSignature.qubits (complexAncillas m L + n)).canonicalPlacement.layout,
      (∀ U : UnitaryOperator (Qubits (m + n)),
        word.binaryMatrix (UnitarySource.interpretation U true true false) =
          complexTarget U P degree bounded) ∧
      word.eventCost = complexBudget m n L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 21) * L + 20) ∧
      nativeGateCount word.eventCost ≤ 15 * ((40 * m + 20) * L + 19) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
        (.gate .toffoli) word.eventCost = 0 := by
  cases L with
  | zero =>
    let word := Scalar.circuit (UnitarySource.model (m + n) true true false) m n
      ((1 / 4 : ℂ) * P.coeff 0) (Scalar.quarter_coefficient_bound P bounded)
    refine ⟨word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · intro U
      simpa only [complexTarget] using
        (show _ = scalarDilationWithSourceAncillas (m := m) (n := n) _ _ from by
          rw [regroup_one_binaryMatrix, Scalar.circuit_source_matrix])
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events]
      simp only [complexBudget, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth, Scalar.circuit_depth]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events,
        nativeGateCount_singleton_gate]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, Scalar.circuit_events]
      simp [ResourcePool.count, ResourcePool.singleton]
  | succ k =>
    let data := complexPhases P degree (Nat.succ_pos k) bounded
    let raw := KnownZero.Total.Four.complexWord (m := m) (n := n) data.phases data.realAngle
      data.imaginaryAngle
      data.realConstant data.imaginaryConstant
    have length : data.phases.length = (k + 1) - 1 :=
      complexPhases_length P degree (Nat.succ_pos k) bounded
    have events : raw.eventCost
      = KnownZero.Total.Four.complexBudget (m := m) (n := n) ((k + 1) - 1) := by
      rw [KnownZero.Total.Four.totalComplexWord_events, length]
    refine ⟨(expand raw).castQubitWidth (by simp only [complexAncillas]; omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro U
      have same : ((expand raw).binaryMatrix
        (UnitarySource.interpretation U true true false)) = complexPhaseOperator U data := by
        unfold UnitaryCircuit.binaryMatrix
        rw [toffoliExpansion_preserves_matrix]
        exact complexWord_operator U data
      rw [regroup_three_binaryMatrix, same]
      simp only [complexTarget, data]
    · rw [UnitaryCircuit.castQubitWidth_eventCost, toffoliExpansion_expanded_eventCost,
        events]
      simp only [complexBudget, Nat.succ_ne_zero, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth]
      apply (toffoliExpansion_depth_le raw).trans
      apply Nat.mul_le_mul_left 15
      have depth := KnownZero.Total.Four.totalComplexWord_depth_le (m := m) (n := n) data.phases
        data.realAngle data.imaginaryAngle data.realConstant data.imaginaryConstant
      simpa only [length, Nat.sub_add_cancel (Nat.succ_pos k)] using depth
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      apply (toffoliExpansion_native_gate_bound raw).trans
      apply Nat.mul_le_mul_left 15
      have bound := KnownZero.Total.Four.totalComplexBudget_native_gate_bound (m := m) (n := n)
        ((k + 1) - 1)
      rw [Nat.sub_add_cancel (Nat.succ_pos k)] at bound
      simpa only [events] using bound
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      exact toffoliExpansion_expanded_toffoli_count raw

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected

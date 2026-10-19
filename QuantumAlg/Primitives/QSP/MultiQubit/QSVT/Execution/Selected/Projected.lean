/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Balanced
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Constant

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Phases
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis

/-!
# Independently selected projected QSVT target

Pure polynomial synthesis selects the phases before circuit construction. The
full target includes the balanced odd-degree boundary factors, not only its
projected block. Native realization retains the original exact query budget.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected
noncomputable section

/-- Mathematical phase data selected solely from the polynomial source hypotheses. -/
public def realPhases {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) : List ℝ :=
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source
  projectedPhasesFromQSPCertificate certificate.certificate.φ₀ certificate.certificate.φs

lemma realPhases_length {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    (realPhases source).length = L := by
  exact (projectedPhasesFromQSPCertificate_length _ _).trans
    (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses
      source).certificate.length_eq

/-- Full mathematical operator for balanced phases, including the odd boundary factors. -/
public def balancedOperator {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (phases : List ℝ) :
    UnitaryOperator (Qubits (1 + N)) :=
  let unbalanced := phaseControlledDirectSumOperator (Native.sourceWord U left right phases)
    (Native.sourceWord U left right (negPhases phases))
  if phases.length % 2 = 0 then unbalanced
  else (OrthogonalProjector.controlledNotOp left)⁻¹ * unbalanced *
    OrthogonalProjector.controlledNotOp right

/-- Full target chosen from mathematical source phases and the constant coefficient. -/
public def projectedTarget {N L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    UnitaryOperator (Qubits (1 + N)) :=
  if L = 0 then (rotZOp (Real.arccos (P.coeff 0))).tensor 1
  else balancedOperator U left right (realPhases source)

private lemma balanced_realization (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P)
    (positive : 0 < L) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
        (ProjectorPhase.layout N),
      (∀ (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N),
        word.binaryMatrix (ProjectedSignal.interpretation U left right) =
          balancedOperator U left right (realPhases source) ∧
        projectedPhasePlusBlock (projectedOutputProjector left right L) right
            (word.binaryMatrix (ProjectedSignal.interpretation U left right)) =
          singularValuePolynomial right L (realPolynomialToComplex P)
            (projectedUnitaryBlock left right U)) ∧
      word.eventCost = Native.Balanced.budget (width := N) false L ∧
      word.evaluatedEventDepth (fun _ => 1) = 4 * L := by
  let phases := realPhases source
  have length : phases.length = L := realPhases_length source
  have block (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N) :
      projectedPhasePlusBlock (projectedOutputProjector left right L) right
        ((Native.circuit (width := N) false phases).binaryMatrix
          (ProjectedSignal.interpretation U left right)) =
        singularValuePolynomial right L (realPolynomialToComplex P)
          (projectedUnitaryBlock left right U) :=
    Native.circuit_of_real_certificate U left right false
      (ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source)
      positive
  by_cases even : L % 2 = 0
  · refine ⟨Native.circuit (width := N) false phases, ?_, ?_, ?_⟩
    · intro U left right
      refine ⟨?_, block U left right⟩
      change _ = balancedOperator U left right phases
      simpa only [balancedOperator, length, even, ↓reduceIte] using
        Native.circuit_source_operator U left right false phases
    · rw [Native.circuit_events, length,
        ← Native.Balanced.budget_eq_native_of_even (width := N) false L even]
    · rw [Native.circuit_depth, length]
  · cases phaseEq : phases with
    | nil => simp only [phaseEq, List.length_nil] at length; omega
    | cons angle tail =>
      have tailLength : tail.length + 1 = L := by simpa only [phaseEq, List.length_cons]
        using length
      have odd : (tail.length + 1) % 2 ≠ 0 := by omega
      have evenTail : tail.length % 2 = 0 := by omega
      refine ⟨Native.Balanced.oddCircuit (width := N) false angle tail, ?_, ?_, ?_⟩
      · intro U left right
        constructor
        · change _ = balancedOperator U left right phases
          rw [phaseEq, balancedOperator]
          simp only [List.length_cons, odd, ↓reduceIte]
          rw [← Native.circuit_source_operator U left right false,
            Native.Balanced.native_cons_matrix U left right false angle tail odd,
            inv_mul_cancel_left, Native.Balanced.oddCircuit_matrix]
        · rw [Native.Balanced.oddCircuit_projectedPhasePlusBlock U left right false
            angle tail odd]
          simpa only [phaseEq] using block U left right
      · rw [Native.Balanced.oddCircuit_events (width := N) false angle tail evenTail,
          tailLength]
      · rw [Native.Balanced.oddCircuit_depth (width := N) false angle tail, tailLength]

/-- Polynomial data chooses one fixed word before any source or projector interpretation. -/
lemma exists_projected_target_execution (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
        (ProjectorPhase.layout N),
      (∀ (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N),
        word.binaryMatrix (ProjectedSignal.interpretation U left right) =
          projectedTarget U left right source ∧
        projectedPhasePlusBlock (projectedOutputProjector left right L) right
            (word.binaryMatrix (ProjectedSignal.interpretation U left right)) =
          singularValuePolynomial right L (realPolynomialToComplex P)
            (projectedUnitaryBlock left right U)) ∧
      word.eventCost = projectedBudget N L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 4 * L + 1 := by
  by_cases zero : L = 0
  · subst L
    refine ⟨Shared.constantInitial (ProjectedSignal.model N) N (P.coeff 0),
      ?_, rfl, by change 1 ≤ 1; omega⟩
    intro U left right
    constructor
    · simp only [projectedTarget, ↓reduceIte, Shared.constantInitial,
        Gate.singleQubitAt_first_binaryMatrix]
    · have bound : |P.coeff 0| ≤ 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        exact source.bounded 0 (by constructor <;> norm_num)
      have degree : (realPolynomialToComplex P).natDegree = 0 := by
        rw [realPolynomialToComplex_natDegree]
        exact Nat.eq_zero_of_le_zero source.degree_le
      rw [projectedOutputProjector, projectedPhasePlusBlock,
        Shared.constantInitial_correct _ _ _ (abs_le.mp bound).1 (abs_le.mp bound).2,
        Native.singularValuePolynomial_constant right _ _ degree]
      simp only [Nat.zero_mod, ↓reduceIte, Matrix.mul_smul, mul_one, Matrix.smul_mul,
        right.idempotent]
      congr 1
      exact (Polynomial.coeff_map (p := P) (algebraMap ℝ ℂ) 0).symm
  · obtain ⟨word, semantic, cost, depth⟩ :=
      balanced_realization N source (Nat.pos_of_ne_zero zero)
    refine ⟨word, ?_, ?_, ?_⟩
    · intro U left right
      obtain ⟨matrix, block⟩ := semantic U left right
      refine ⟨?_, block⟩
      simpa only [projectedTarget, zero, ↓reduceIte] using matrix
    · simpa only [projectedBudget, zero, ↓reduceIte] using cost
    · rw [depth]
      omega

/-- The independently selected target has the original source polynomial block. -/
public lemma projectedTarget_block {N L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    projectedPhasePlusBlock (projectedOutputProjector left right L) right
        (projectedTarget U left right source) =
      singularValuePolynomial right L (realPolynomialToComplex P)
        (projectedUnitaryBlock left right U) := by
  obtain ⟨word, semantic, _, _⟩ := exists_projected_target_execution N source
  obtain ⟨matrix, block⟩ := semantic U left right
  simpa only [matrix] using block

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution.Selected

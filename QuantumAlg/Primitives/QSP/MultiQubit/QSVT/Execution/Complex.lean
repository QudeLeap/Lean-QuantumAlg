/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Regroup
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Certificate.Expanded
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Normalized
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Bounds

/-!
# Uniform actual execution for complex Hermitian QSVT

The standard block interface covers degree zero with one added ancilla and
positive degree with three added ancillas.
The specification budget depends on the source width and polynomial degree,
not on the synthesized phases or the selected implementation.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution
open Gate.Toffoli
noncomputable section

/-- Independent coordinate budget, including the native constant-polynomial case. -/
def complexBudget {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (UnitarySource.model U true true false)) :=
  if L = 0 then ResourcePool.singleton (.gate .singleQubit)
  else expandedBudget (UnitarySource.model U true true false)
    (KnownZero.Total.Four.complexBudget U (L - 1))

/-- Every permitted degree admits a standard-interface word with exact native accounting. -/
theorem exists_complex_execution {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ a : Nat, m ≤ a ∧ a ≤ m + 3 ∧
      ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false)
          (QuantumSignature.qubits (a + n)).canonicalPlacement.layout,
        ExactBlockEncoding a n word.binaryMatrix ((1 / 4 : ℂ) • polynomialOperator P A) ∧
        word.eventCost = complexBudget U L ∧
        word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 21) * L + 20) ∧
        nativeGateCount word.eventCost ≤ 15 * ((40 * m + 20) * L + 19) ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
          (.gate .toffoli) word.eventCost = 0 := by
  by_cases zero : L = 0
  · subst L
    obtain ⟨word, block, cost, depth⟩ := Scalar.exists_normalized_constant_execution
      (m := m) (UnitarySource.model U true true false) P A (Nat.eq_zero_of_le_zero degree) bounded
    refine ⟨1 + m, by omega, by omega,
      word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regroup_one_binaryMatrix]
      exact block
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp only [complexBudget, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth, depth]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost, nativeGateCount_singleton_gate]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp [ResourcePool.count, ResourcePool.singleton]
  · obtain ⟨word, block, cost, depth, gates, toffoli⟩ :=
      KnownZero.Total.Four.exists_total_complex_expanded_execution U A encoding hermitian
        P degree (Nat.pos_of_ne_zero zero) bounded
    refine ⟨1 + (1 + (1 + m)), by omega, by omega,
      word.castQubitWidth (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · rw [regroup_three_binaryMatrix]
      exact block
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp only [complexBudget, zero, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth]
      exact depth
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      exact gates
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      exact toffoli

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution

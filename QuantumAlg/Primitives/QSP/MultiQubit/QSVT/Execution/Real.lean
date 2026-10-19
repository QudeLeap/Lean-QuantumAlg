/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Oracle.UnitarySource.Model

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Regroup
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Certificate.Expanded
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Real
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Bounds

/-!
# Uniform actual execution for real matching-parity QSVT

The same standard block interface covers degree zero and positive degree.
The specification budget depends on the source width and polynomial degree,
not on the synthesized phases or the selected implementation.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution
open Gate.Toffoli
noncomputable section

/-- Independent coordinate budget, including the native constant-polynomial case. -/
public def realBudget (m n L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false)) :=
  if L = 0 then ResourcePool.singleton (.gate .singleQubit)
  else expandedBudget (UnitarySource.model (m + n) false true false)
    (KnownZero.Total.budget (m := m) (n := n) false L + 2 • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
      (.gate .singleQubit))

/-- Every permitted degree admits a standard-interface word with exact native accounting. -/
lemma exists_real_execution {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
        (QuantumSignature.qubits ((1 + m) + n)).canonicalPlacement.layout,
      ExactBlockEncoding (1 + m) n (word.binaryMatrix
        (UnitarySource.interpretation U false true false))
        (polynomialOperator (realPolynomialToComplex P) A) ∧
      word.eventCost = realBudget m n L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 4) * L + 2) ∧
      nativeGateCount word.eventCost ≤ 15 * ((40 * m + 3) * L + 2) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .toffoli) word.eventCost = 0 := by
  by_cases zero : L = 0
  · subst L
    obtain ⟨word, block, cost, depth⟩ := Scalar.exists_real_constant_execution
      (m := m) (UnitarySource.model (m + n) false true false) P A source
    refine ⟨word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regroup_one_binaryMatrix]
      exact block (UnitarySource.interpretation U false true false)
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp only [realBudget, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth, depth]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost, nativeGateCount_singleton_gate]
      omega
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp [ResourcePool.count, ResourcePool.singleton]
  · obtain ⟨word, block, cost, depth, gates, toffoli⟩ :=
      KnownZero.Total.exists_total_real_expanded_execution U A encoding hermitian source
        (Nat.pos_of_ne_zero zero)
    refine ⟨word.castQubitWidth (Nat.add_assoc 1 m n).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regroup_one_binaryMatrix]
      exact block
    · rw [UnitaryCircuit.castQubitWidth_eventCost, cost]
      simp only [realBudget, zero, ↓reduceIte]
    · rw [UnitaryCircuit.castQubitWidth_evaluatedEventDepth]
      exact depth
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      exact gates
    · rw [UnitaryCircuit.castQubitWidth_eventCost]
      exact toffoli

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution

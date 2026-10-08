/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Balanced
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Constant
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Balanced
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement

/-!
# Uniform projected QSVT execution

The model grants the original source and projector accesses. Constant degree
uses just one native rotation. Positive degree retains the actual alternating
query word and its exact occurrence budget, without assuming a native
implementation of either arbitrary projector.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution
noncomputable section

/-- Independent projected-word budget for every degree, including the constant boundary. -/
public def projectedBudget {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (ProjectedSignal.model U left right)) :=
  if L = 0 then ResourcePool.singleton (.gate .singleQubit)
  else Native.Balanced.budget U left right false L

/-- All matching-parity source inputs admit one actual projected execution. -/
theorem exists_projected_execution {N L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right)
        (ProjectorPhase.layout N),
      projectedPhasePlusBlock (projectedOutputProjector left right L) right word.binaryMatrix =
        singularValuePolynomial right L (realPolynomialToComplex P)
          (projectedUnitaryBlock left right U) ∧
      word.eventCost = projectedBudget U left right L ∧
      word.evaluatedEventDepth (fun _ => 1) ≤ 4 * L + 1 := by
  by_cases zero : L = 0
  · subst L
    obtain ⟨word, block, cost, depth⟩ := Native.exists_native_constant_word U left right source
    refine ⟨word, ?_, ?_, ?_⟩
    · exact block
    · simpa only [projectedBudget, ↓reduceIte] using cost
    · rw [depth]
  · obtain ⟨word, block, cost, depth⟩ :=
      Native.Balanced.exists_real_word U left right false source (Nat.pos_of_ne_zero zero)
    refine ⟨word, block, ?_, ?_⟩
    · rw [cost]
      simp only [projectedBudget, zero, ↓reduceIte]
    · rw [depth]
      omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution

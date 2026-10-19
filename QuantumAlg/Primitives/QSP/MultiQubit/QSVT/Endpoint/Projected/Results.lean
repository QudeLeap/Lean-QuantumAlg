/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
public import QuantumAlg.Components.Oracle.ProjectedSignal
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Projected

/-!
# Complete projected QSVT construction facts

The same execution has the source polynomial block, exact occurrence budget,
and all original native coordinate bounds. These stronger construction facts
are separate from the public existential execution interface.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
noncomputable section

/-- Every permitted degree has an actual complete execution of the source polynomial block. -/
public lemma projected_complete_execution (N : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
        (UnitaryExecution.Owned.Binary.layout (1 + N)),
      Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word) (problem N source) ∧
      word.eventCost = (problem N source).resources.events ∧
      ∀ (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N),
        ∃ V : UnitaryOperator (Qubits (1 + N)),
          projectedPhasePlusBlock (projectedOutputProjector left right L) right V =
            singularValuePolynomial right L (realPolynomialToComplex P)
              (projectedUnitaryBlock left right U) ∧
          word.binaryMatrix (ProjectedSignal.interpretation U left right) = V := by
  obtain ⟨word, semantic, cost, depth⟩ :=
    Execution.Selected.exists_projected_target_execution N source
  refine ⟨word, word_solves N source word (fun U left right => (semantic U left right).1)
    cost depth, cost, ?_⟩
  intro U left right
  exact ⟨word.binaryMatrix (ProjectedSignal.interpretation U left right),
    (semantic U left right).2, rfl⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected

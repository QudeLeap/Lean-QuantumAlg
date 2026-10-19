/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.HadamardTest.Probability
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The exact Hadamard-test probability in the complete run

The actual finite result distribution and its relational success event retain
the registered real-overlap equality [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution

/-- The complete run's actual zero-result probability is exactly the source formula. -/
lemma outputDistribution_zero {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width)) {Reference : Register}
    (input : OracleInput .empty (pre width) Reference)
    (promised : inputPromise source input.caller.localState.quantumMarginal) :
    (run width).outputDistribution (environment unitary) input (.finite 0) =
      ENNReal.ofReal (probabilityZero unitary source) := by
  have actual := congrArg (fun distribution : PMF (CShape.Value (.finite 2)) =>
      distribution (.finite 0))
    (ExecutionState.toPMF_mapClassical ((run width).execute (environment unitary) Reference
      input.state)
      ((run width).execute_normalized (environment unitary) input) (run width).result)
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    (((code width).execute (environment unitary) Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
      |>.mapClassical (fun value => value.1.read (.storage (resultRef width).toCStorageRef))
      |>.block (.finite 0)).mass) = _
  apply congrArg ENNReal.ofReal
  apply code_zero_mass unitary source
  rw [ExecutionState.mapClassical_quantumMarginal,
    ← OracleInput.oracleInput_caller_quantumMarginal, ← Input.localState_quantumMarginal]
  exact promised

/-- The relational success event of the same run attains exactly its independent lower bound. -/
lemma actual_success {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width)) {Reference : Register}
    (input : OracleInput .empty (pre width) Reference)
    (promised : inputPromise source input.caller.localState.quantumMarginal) :
    ENNReal.ofReal (probabilityZero unitary source) =
      ((run width).relationalDistribution (environment unitary) input).toOuterMeasure
        {pair | pair.2 = .finite 0} := by
  have projection :
      ((run width).relationalDistribution (environment unitary) input).toOuterMeasure
        {pair | pair.2 = .finite 0} =
      ((run width).outputDistribution (environment unitary) input).toOuterMeasure
        {CShape.Value.finite (cardinality := 2) (0 : Fin 2)} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, PMF.toOuterMeasure_apply_singleton]
  exact (outputDistribution_zero unitary source input promised).symm

end

end QuantumAlg.HadamardTest

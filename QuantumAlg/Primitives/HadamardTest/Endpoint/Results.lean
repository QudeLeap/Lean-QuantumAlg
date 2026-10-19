/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Endpoint
import all QuantumAlg.Primitives.HadamardTest.Endpoint
import all QuantumAlg.Primitives.HadamardTest.Endpoint.Execution

public import QuantumAlg.Primitives.HadamardTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Primitives.HadamardTest.Specification
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.HadamardTest.Distribution
import all QuantumAlg.Primitives.HadamardTest.Restoration
import all QuantumAlg.Primitives.HadamardTest.Resources
import all QuantumAlg.Primitives.HadamardTest.Space
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete native Hadamard test with its exact scientific probability

The algorithm prepares one control, executes the actual controlled source
query, measures into a finite classical register, and reads that register.
Its same execution satisfies the independent event, space and depth limits,
complete borrowed-reference restoration, and the original exact probability
[AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

public lemma algorithm_output_listing (width : Nat) :
    (algorithm width).run.output.listing = (post width).keys := run_output_listing width

/-- Public input validity is exactly the original normalized source vector in its physical frame. -/
public lemma problem_valid_iff {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width))
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem width).valid (environment unitary) (unitary, source) state ↔
      ∀ row column, state.quantumMarginal.matrix row column =
        source.vec (inputBasisEquiv width row) * star (source.vec (inputBasisEquiv width column)) :=
  and_iff_right rfl

/-- Reading the actual result preserves the exact real-overlap formula [AJL06, qf2.tex:625-645]. -/
public lemma algorithm_probability_zero {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (source : NormalizedVector (Qubits width))
    {Reference : Register} (input : Execution.OracleInput .empty (pre width) Reference)
    (promised : (problem width).valid (environment unitary) (unitary, source)
      input.caller.localState) :
    (algorithm width).outputDistribution (environment unitary) input (.finite 0) =
      ENNReal.ofReal (probabilityZero unitary source) :=
  outputDistribution_zero unitary source input promised.2

end

end QuantumAlg.HadamardTest

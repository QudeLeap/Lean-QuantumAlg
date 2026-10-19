/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.SwapTest.Endpoint
import all QuantumAlg.Primitives.SwapTest.Endpoint
import all QuantumAlg.Primitives.SwapTest.Endpoint.Execution

public import QuantumAlg.Primitives.SwapTest.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.SwapTest.Specification
import all QuantumAlg.Primitives.SwapTest.Execution
import all QuantumAlg.Primitives.SwapTest.Probability
import all QuantumAlg.Primitives.SwapTest.Resources
import all QuantumAlg.Primitives.SwapTest.Restoration
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete elementary SWAP test with its exact scientific probability

The same complete measured execution supplies the source probability,
independent native resource limits and external reference restoration
[BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The entire live quantum and classical interface is retained by the actual output. -/
public lemma swapTestAlgorithm_output_listing (width : Nat) :
    (algorithm width).run.output.listing = (post width).keys := run_output_listing width

/-- The source product-state promise uses the actual physical input coordinates. -/
public lemma problem_valid_iff (actual : model.Environment) {width : Nat} (left right :
    NormalizedVector (Qubits width))
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem width).valid actual (left, right) state ↔
      ∀ row column, state.quantumMarginal.matrix row column =
        (left.tensor right).vec (inputBasisEquiv width row) *
          star ((left.tensor right).vec (inputBasisEquiv width column)) :=
  Iff.rfl

/-- The actual result has the original exact one-outcome probability. -/
public lemma algorithm_probability_one (actual : model.Environment) {width : Nat}
    (left right : NormalizedVector (Qubits width))
    {Reference : Register} (input : Execution.OracleInput .empty (pre width) Reference)
    (promised : (problem width).valid actual (left, right) input.caller.localState) :
    (algorithm width).outputDistribution actual input (.finite 1) =
      ENNReal.ofReal (probabilityOne left right) :=
  outputDistribution_one actual left right input promised

end

end QuantumAlg.SwapTest

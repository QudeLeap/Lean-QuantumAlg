/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

/-!
# Complete elementary SWAP test with its exact scientific probability

The same complete measured execution supplies the source probability,
independent native resource limits and external reference restoration
[BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.SwapTest

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The source product-state promise uses the actual physical input coordinates. -/
public theorem problem_valid_iff {width : Nat} (left right : NormalizedVector (Qubits width))
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem left right).valid state ↔
      ∀ row column, state.quantumMarginal.matrix row column =
        (left.tensor right).vec (inputBasisEquiv width row) *
          star ((left.tensor right).vec (inputBasisEquiv width column)) :=
  Iff.rfl

/-- The actual result has the original exact one-outcome probability. -/
public theorem algorithm_probability_one {width : Nat}
    (left right : NormalizedVector (Qubits width))
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (promised : (problem left right).valid input.localState) :
    (algorithm width).outputDistribution input (.finite 1) =
      ENNReal.ofReal (probabilityOne left right) :=
  outputDistribution_one left right input promised

private theorem algorithm_solves {width : Nat} (left right : NormalizedVector (Qubits width)) :
    Algorithm.Solves (algorithm width) (problem left right) := by
  constructor
  · intro Reference input promised
    exact le_of_eq (actual_success left right input promised)
  · intro _Reference _input _promised requirement present
    exact False.elim (List.not_mem_nil present)
  · intro _Reference input _promised
    exact code_borrowedRestored width (input.state.mapClassical (fun store => (store, store)))
  · intro _Reference _input _promised path _supported
    exact le_of_eq (code_events width path)
  · intro _Reference _input _promised path _supported
    exact code_residentSpace width path
  · intro _Reference _input _promised path _supported
    exact code_auxiliarySpace width path
  · intro _Reference _input _promised path _supported
    exact code_depth width path

/-- The same complete elementary measured circuit solves the independent problem and retains
exactly the original overlap formula for every admitted reference extension. -/
public theorem main {width : Nat} (left right : NormalizedVector (Qubits width)) :
    ∃ candidate : Algorithm .quantum (pre width) (post width) (.finite 2),
      Algorithm.Solves candidate (problem left right) ∧
        ∀ (Reference : Register) (input : Execution.Input (pre width) Reference),
          (problem left right).valid input.localState →
            candidate.outputDistribution input (.finite 1) =
              ENNReal.ofReal (probabilityOne left right) :=
  ⟨algorithm width, algorithm_solves left right,
    fun _Reference input promised => algorithm_probability_one left right input promised⟩

end

end QuantumAlg.SwapTest

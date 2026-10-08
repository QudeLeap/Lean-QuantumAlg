/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

/-- Public input validity is exactly the original normalized source vector in its physical frame. -/
public theorem problem_valid_iff {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width))
    (state : ExecutionState (Execution.Store (pre width)) (pre width).register) :
    (problem unitary source).valid state ↔
      ∀ row column, state.quantumMarginal.matrix row column =
        source.vec (inputBasisEquiv width row) * star (source.vec (inputBasisEquiv width column)) :=
  Iff.rfl

/-- Reading the actual result preserves the exact real-overlap formula [AJL06, qf2.tex:625-645]. -/
public theorem algorithm_probability_zero {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) (source : NormalizedVector (Qubits width))
    {Reference : Register} (input : Execution.OracleInput .empty (pre width) Reference)
    (promised : (problem unitary source).valid input.caller.localState) :
    (algorithm unitary).outputDistribution input (.finite 0) =
      ENNReal.ofReal (probabilityZero unitary source) :=
  outputDistribution_zero unitary source input promised

private theorem algorithm_solves {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width)) :
    Algorithm.Solves (algorithm unitary) (problem unitary source) := by
  constructor
  · intro Reference input promised _initialized
    exact le_of_eq (actual_success unitary source input promised)
  · intro _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro _Reference input _promised _initialized
    have restored := code_borrowedRestored unitary
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code unitary).BorrowedRestored _ input.state
      ((code unitary).execute _
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events unitary path)
  · intro _Reference _input _promised _initialized path _supported
    exact code_residentSpace unitary path
  · intro _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace unitary path
  · intro _Reference _input _promised _initialized path _supported
    exact code_depth unitary path

/-- The same complete native algorithm solves the independent problem and attains exactly
the original real-overlap probability on every reference extension [AJL06, qf2.tex:625-645]. -/
public theorem main {width : Nat} (unitary : UnitaryOperator (Qubits width))
    (source : NormalizedVector (Qubits width)) :
    ∃ candidate : Algorithm (model unitary) (pre width) (post width) (.finite 2),
      Algorithm.Solves candidate (problem unitary source) ∧
        ∀ (Reference : Register) (input : Execution.OracleInput .empty (pre width) Reference),
          (problem unitary source).valid input.caller.localState →
            candidate.outputDistribution input (.finite 0) =
              ENNReal.ofReal (probabilityZero unitary source) :=
  ⟨algorithm unitary, algorithm_solves unitary source,
    fun _Reference input promised => algorithm_probability_zero unitary source input promised⟩

end

end QuantumAlg.HadamardTest

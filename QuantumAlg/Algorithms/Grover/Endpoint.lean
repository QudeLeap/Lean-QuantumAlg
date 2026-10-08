/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Grover.Specification
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Algorithms.Grover.Context
import all QuantumAlg.Algorithms.Grover.Storage
import all QuantumAlg.Algorithms.Grover.Execution
import all QuantumAlg.Algorithms.Grover.Distribution
import all QuantumAlg.Algorithms.Grover.Restoration
import all QuantumAlg.Algorithms.Grover.Resources
import all QuantumAlg.Algorithms.Grover.Space
import all QuantumAlg.Algorithms.Grover.Specification
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Grover's complete native endpoint

The named algorithm contains the one actual prepare, Grover-unitary, Z-write
and packing execution. Its explicit complete output keeps every quantum
system and classical cell. The exact probability and native gate/query
counts are proved on this execution in addition to the independent Solves
contract [dW19, qcnotes.tex:2760-2852].
-/

namespace QuantumAlg.GroverSearch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public input contract preserves the original positive-width nonempty marked domain. -/
public theorem problem_valid_iff {n t : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem (t := t) marked k).valid state ↔
      0 < n ∧ markedCount marked = t ∧ 0 < t := Iff.rfl

/-- Acceptance checks the actual packed bits against the original marked predicate. -/
public theorem problem_accepts_bits_iff {n t : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem (t := t) marked k).accepts initial (.bits outcome) ↔
      marked (TerminalZMeasure.fullRegisterIndex outcome) = true := Iff.rfl

/-- The complete prepared search execution, with actual measured-result storage and full Output. -/
public def algorithm (n : Nat) (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    Algorithm (model marked) pre (post n k) (.bits n) where
  run := run marked k

/-- The named algorithm's actual output has exactly the source sin-squared marked probability. -/
public theorem algorithm_outputProbability_eq {n t k : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (counted : markedCount marked = t) (positive : 0 < t)
    {Reference : Register}
    (input : Execution.OracleInput (model marked).classicalOracles pre Reference) :
    ((algorithm n marked k).run.outputDistribution input).toOuterMeasure
      {result | match result with
        | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true} =
      ENNReal.ofReal
        (Real.sin (((2 : Real) * k + 1) *
          Real.arcsin (Real.sqrt ((t : Real) / ((2 ^ n : Nat) : Real)))) ^ 2) := by
  have projection :
      ((run marked k).relationalDistribution input).toOuterMeasure
        {pair | accepts marked pair.1 pair.2} =
      ((run marked k).outputDistribution input).toOuterMeasure
        {result | match result with
          | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.symm.trans (actual_success marked k counted positive input)

/-- All actual oracle calls are the k source phase queries. -/
public theorem algorithm_queryCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (algorithm n marked k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1
      | _ => 0) ((algorithm n marked k).run.code.resourcePool path) = k :=
  code_queryCount marked k path

/-- The same actual run contains the precisely counted elementary source-reflection gates. -/
public theorem algorithm_elementaryGateCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (algorithm n marked k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm n marked k).run.code.resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementaryGateCount n) :=
  code_elementaryGateCount marked k path

/-- The actual search run has this exact single-qubit gate multiplicity. -/
public theorem algorithm_singleQubitCount {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (algorithm n marked k).run.code.Path) :
    ResourcePool.count (model := model marked) (.gate .singleQubit)
      ((algorithm n marked k).run.code.resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementarySingleQubitCount n) :=
  code_singleQubitCount marked k path

/-- The actual search run uses CNOT only in its width-two reflections. -/
public theorem algorithm_cnotCount {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (algorithm n marked k).run.code.Path) :
    ResourcePool.count (model := model marked) (.gate .cnot)
      ((algorithm n marked k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryCNOTCount n :=
  code_cnotCount marked k path

/-- The actual search run uses the selected source reflection's exact Toffoli schedule. -/
public theorem algorithm_toffoliCount {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (path : (algorithm n marked k).run.code.Path) :
    ResourcePool.count (model := model marked) (.gate .toffoli)
      ((algorithm n marked k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryToffoliCount n :=
  code_toffoliCount marked k path

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public theorem algorithm_solves {n t k : Nat} (marked : Fin (2 ^ n) → Bool) :
    Algorithm.Solves (algorithm n marked k) (problem (t := t) marked k) := by
  constructor
  · intro Reference input promised _initialized
    exact le_of_eq (actual_success marked k promised.2.1 promised.2.2 input).symm
  · intro _Reference _input _promised _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _promised _initialized
    have restored := code_borrowedRestored marked k
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code marked k).BorrowedRestored _ input.state
      ((code marked k).execute _
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed _)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _promised _initialized path _supported
    exact le_of_eq (code_events marked k path)
  · intro _Reference _input _promised _initialized path _supported
    exact code_residentSpace marked k path
  · intro _Reference _input _promised _initialized path _supported
    exact code_auxiliarySpace marked k path
  · intro _Reference _input _promised _initialized path _supported
    exact code_depth marked k path


/-- The actual search execution solves the original positive-width problem with independent
complete event, space and depth bounds and mandatory joint borrowed restoration. -/
public theorem main {n t k : Nat} (marked : Fin (2 ^ n) → Bool) :
    ∃ candidate : Algorithm (model marked) pre (post n k) (.bits n),
      Algorithm.Solves candidate (problem (t := t) marked k) :=
  ⟨algorithm n marked k, algorithm_solves marked⟩

end

end QuantumAlg.GroverSearch

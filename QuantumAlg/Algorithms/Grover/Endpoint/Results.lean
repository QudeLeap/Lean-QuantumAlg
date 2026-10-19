/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Grover.Endpoint
import all QuantumAlg.Algorithms.Grover.Endpoint
import all QuantumAlg.Algorithms.Grover.Endpoint.Execution

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
public lemma problem_valid_iff {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n k).valid (environment marked) marked state ↔
      0 < n ∧ 0 < markedCount marked := by
  constructor
  · exact fun admitted => admitted.2
  · exact fun promised => ⟨rfl, promised⟩

/-- The original explicit marked-count promise is the same source instance. -/
public lemma problem_valid_counted_iff {n t : Nat} (marked : Fin (2 ^ n) → Bool)
    (k : Nat) (counted : markedCount marked = t)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n k).valid (environment marked) marked state ↔
      0 < n ∧ markedCount marked = t ∧ 0 < t := by
  rw [problem_valid_iff, counted]
  simp only [true_and]

/-- Acceptance checks the actual packed bits against the original marked predicate. -/
public lemma problem_accepts_bits_iff {n : Nat}
    (marked : Fin (2 ^ n) → Bool) (k : Nat)
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem n k).accepts (environment marked) marked initial (.bits outcome) ↔
      marked (TerminalZMeasure.fullRegisterIndex outcome) = true := Iff.rfl

/-- The quantum budget includes the one work wire precisely when a nonempty large-width
reflection schedule needs it. -/
public lemma groverProblem_quantumResident (n k : Nat) :
    (problem n k).resources.resident (.quantumSystems 2) =
      n + if k = 0 ∨ n ≤ 3 then 0 else 1 := by
  change (if (2 : ℕ+) = 2 then n + (if k = 0 ∨ n ≤ 3 then 0 else 1) else 0) = _
  exact if_pos rfl

/-- The named algorithm's actual output has exactly the source sin-squared marked probability. -/
public lemma algorithm_outputProbability_eq {n t k : Nat}
    (marked : Fin (2 ^ n) → Bool)
    (counted : markedCount marked = t) (positive : 0 < t)
    {Reference : Register}
    (input : Execution.OracleInput (model n).classicalOracles pre Reference) :
    ((algorithm n k).run.outputDistribution (environment marked) input).toOuterMeasure
      {result | match result with
        | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true} =
      ENNReal.ofReal
        (Real.sin (((2 : Real) * k + 1) *
          Real.arcsin (Real.sqrt ((t : Real) / ((2 ^ n : Nat) : Real)))) ^ 2) := by
  have projection :
      ((run n k).relationalDistribution (environment marked) input).toOuterMeasure
        {pair | accepts marked pair.1 pair.2} =
      ((run n k).outputDistribution (environment marked) input).toOuterMeasure
        {result | match result with
          | .bits outcome => marked (TerminalZMeasure.fullRegisterIndex outcome) = true} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  exact projection.symm.trans (actual_success marked k counted positive input)

/-- All actual oracle calls are the k source phase queries. -/
public lemma algorithm_queryCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1
      | _ => 0) ((algorithm n k).run.code.resourcePool path) = k :=
  code_queryCount n k path

/-- The same actual run contains the precisely counted elementary source-reflection gates. -/
public lemma algorithm_elementaryGateCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm n k).run.code.resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementaryGateCount n) :=
  code_elementaryGateCount n k path

/-- The actual search run has this exact single-qubit gate multiplicity. -/
public lemma algorithm_singleQubitCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .singleQubit)
      ((algorithm n k).run.code.resourcePool path) =
        n + k * (2 * n + ZeroReflection.elementarySingleQubitCount n) :=
  code_singleQubitCount n k path

/-- The actual search run uses CNOT only in its width-two reflections. -/
public lemma algorithm_cnotCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .cnot)
      ((algorithm n k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryCNOTCount n :=
  code_cnotCount n k path

/-- The actual search run uses the selected source reflection's exact Toffoli schedule. -/
public lemma algorithm_toffoliCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.count (model := model n) (.gate .toffoli)
      ((algorithm n k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryToffoliCount n :=
  code_toffoliCount n k path

/-- The named public execution satisfies its full independent input,
state and resource contract. -/
public lemma algorithm_solves (n k : Nat) :
    Algorithm.Solves (algorithm n k) (problem n k) :=
  complete_correct n k

end

end QuantumAlg.GroverSearch

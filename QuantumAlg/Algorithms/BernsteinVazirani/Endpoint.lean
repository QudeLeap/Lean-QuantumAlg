/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.BernsteinVazirani.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.BernsteinVazirani.Construction
import all QuantumAlg.Algorithms.BernsteinVazirani.Specification
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Readout.Execution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Distribution
import all QuantumAlg.Primitives.WalshHadamard.Readout.Restoration
import all QuantumAlg.Primitives.WalshHadamard.Readout.Resources
import all QuantumAlg.Primitives.WalshHadamard.Readout.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native Bernstein-Vazirani recovery

The hidden string supplies only the inner-product oracle. The common
Walsh-Hadamard execution prepares its own quantum input and computes the
answer from actual Z writes and finite-bit packing. Its complete Output
retains every live entry. The exact mathematical recovery theorem is
connected to the same execution's final block probabilities, and its paths
satisfy the independent native budgets for every width, including zero.
-/

namespace QuantumAlg.BernsteinVazirani

open WalshHadamard.Readout

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every local input state is admitted; normalization belongs to the execution Input. -/
public theorem problem_valid {n : Nat} (hidden : Fin (2 ^ n))
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem hidden).valid state := trivial

/-- The public output contract requires precisely the big-endian hidden-string encoding. -/
public theorem problem_returns_hidden_bits_iff {n : Nat} (hidden : Fin (2 ^ n))
    (initial : Execution.Store pre) (outcome : Fin n → Bool) :
    (problem hidden).accepts initial (.bits outcome) ↔
      outcome = (fun index => hidden.val.testBit (n - 1 - index.val)) := Iff.rfl

/-- The shared actual execution with the hidden-string oracle and complete live Output. -/
public def algorithm {n : Nat} (hidden : Fin (2 ^ n)) :
    Algorithm (model (oracle hidden)) pre (post n) (.bits n) where
  run := WalshHadamard.Readout.run (oracle hidden)

private theorem actual_success {n : Nat} (hidden : Fin (2 ^ n))
    {Reference : Register}
    (input : Execution.OracleInput ClassicalOracleModel.empty pre Reference) :
    ((WalshHadamard.Readout.run (oracle hidden)).relationalDistribution input).toOuterMeasure
      {pair | accepts hidden pair.1 pair.2} = 1 := by
  have projection :
      ((WalshHadamard.Readout.run (oracle hidden)).relationalDistribution input).toOuterMeasure
        {pair | accepts hidden pair.1 pair.2} =
      ((WalshHadamard.Readout.run (oracle hidden)).outputDistribution input).toOuterMeasure
        {result | match result with | .bits outcome => outcome = measurementOutcome n hidden} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, WalshHadamard.Readout.outputDistribution_eq,
    PMF.toOuterMeasure_map_apply]
  change ((measurement n).outcomePMF
    (WalshHadamard.Readout.evolvedState (oracle hidden))).toOuterMeasure
        {measurementOutcome n hidden} = 1
  have normalized :
      (WalshHadamard.Readout.evolvedState (oracle hidden)).normalized =
          (evolvedState hidden).normalized := rfl
  rw [TerminalZMeasure.outcomePMF_congr_normalized (measurement n) normalized,
    PMF.toOuterMeasure_apply_singleton]
  exact measurementOutcome_probability_one hidden

/-- The actual native execution recovers every hidden string with probability one,
preserving borrowed correlations and satisfying the independent complete resource bounds. -/
public theorem main {n : Nat} (hidden : Fin (2 ^ n)) :
    ∃ candidate : Algorithm (model (oracle hidden)) pre (post n) (.bits n),
      Algorithm.Solves candidate (problem hidden) := by
  refine ⟨algorithm hidden, ?_⟩
  constructor
  · intro Reference input _valid _initialized
    exact le_of_eq (actual_success hidden input).symm
  · intro _Reference _input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid _initialized
    have restored := code_borrowedRestored (oracle hidden)
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
    have history := Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
    change (code (oracle hidden)).BorrowedRestored Reference input.state
      ((code (oracle hidden)).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
    unfold Circuit.BorrowedRestored at restored ⊢
    rw [restored]
    refine Eq.trans ?_ history
    apply congrArg (Execution.observeBorrowed Reference)
    exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (code_events (oracle hidden) path)
  · intro _Reference _input _valid _initialized path _supported
    exact code_residentSpace (oracle hidden) path
  · intro _Reference _input _valid _initialized path _supported
    exact code_auxiliarySpace (oracle hidden) path
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (code_depth (oracle hidden) path)

end

end QuantumAlg.BernsteinVazirani

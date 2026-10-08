/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Protocol
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Basis.Seeded.ReadoutPromise

/-!
# Complete declared Shor round correctness on actual admitted executions

The original success floor, observed physical zero bank, full borrowed
restoration, native event ledger, both live-space peaks and actual dependency
depth all concern one sampling/recovery/feedback/reset execution. The local
domain retains every reference extension and every sound incoming latch.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) {N : Nat}
  (model : NumberTheory.Factoring.SemiprimeFactorModel N)
  (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
  (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
  (separated : NativeFactorScan.Separated cells result)

include separated in
/-- The actual joint initial/output distribution attains the original one-attempt threshold. -/
theorem relational_success {Reference : Register}
    (original : OracleInput
      (executionModel (Probability.Input.ofSemiprimeModel model)).classicalOracles ctx Reference)
    (admitted : inputDomain ctx model cells original.localState) :
    Probability.honestAttemptSuccessFloor N ≤
      ((algorithm ctx model sameWires cells result).relationalDistribution
        original).toOuterMeasure {pair | accepts model pair.2} := by
  let input := Probability.Input.ofSemiprimeModel model
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel entered :=
    BasisSeeded.mapStore ctx.quantumLayout.zeroLabel original.state
      (BasisSeeded.oracleInput_of_local_support (model := executionModel input)
        ctx.quantumLayout.zeroLabel original admitted.1) id (fun entry => (entry.2, entry.1))
  have enteredSound : ∀ record, 0 < (entered.block record).mass →
      SoundLatch model (NativeFactorScan.latchValue cells record.1) := by
    intro record positive
    obtain ⟨previous, same, present⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff original.state
        (fun entry => (entry.1, (entry.2, entry.1))) record).mp positive
    have localPositive : 0 < (original.localState.block previous).mass := by
      simpa only [OracleInput.oracleInput_localState_block, DensityOperator.marginalLeft_mass]
        using present
    have sameStore : previous.1 = record.1 := congrArg Prod.fst same
    simpa only [sameStore] using admitted.2 previous localPositive
  have lower := Completion.latch_success ctx model sameWires cells result separated entered seeded
    (original.state.mapClassical_normalized original.normalized
      (fun entry => (entry.1, (entry.2, entry.1)))) enteredSound
  rw [PMF.toOuterMeasure_map_apply] at lower
  change Probability.honestAttemptSuccessFloor N ≤
    (((algorithm ctx model sameWires cells result).run.executionDistribution original).map
      (fun record => (record.2.2.1,
        (algorithm ctx model sameWires cells result).run.result record))).toOuterMeasure
          {pair | accepts model pair.2}
  rw [PMF.toOuterMeasure_map_apply]
  exact lower

/-- Every real result fiber has the same zero bank, including zero-mass results. -/
theorem output_state {Reference : Register}
    (original : OracleInput
      (executionModel (Probability.Input.ofSemiprimeModel model)).classicalOracles ctx Reference) :
    (stateRequirement ctx N cells).Holds original.caller
      ((algorithm ctx model sameWires cells result).run.finalState Reference original.state) := by
  intro value
  apply AlgorithmRun.pure_fullSelection_of_executionReadout
    (algorithm ctx model sameWires cells result).run
    (Iteration.context ctx N).quantumLayout.zeroLabel _ original value
  intro reference history _ state selected
  exact BasisSeeded.readout_pure_fullSelection
    ((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result).execute reference state)
    (Iteration.context ctx N).quantumLayout.zeroLabel
    (Completion.code_seeded ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result state)
    (fun store => (algorithm ctx model sameWires cells result).run.output.eval store) selected

include separated in
/-- One actual complete round meets every obligation of the independent protocol. -/
theorem shorDeclared_round_solves (noBorrowedQuantum : ctx.borrowedQuantumWires = [])
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (algorithm ctx model sameWires cells result).Solves
      (problem ctx model cells duration unitQueries) := by
  constructor
  · intro Reference original _valid admitted
    exact relational_success ctx model sameWires cells result separated original admitted
  · intro Reference original _valid _admitted requirement present
    have same : requirement = stateRequirement ctx N cells := List.mem_singleton.mp present
    subst requirement
    exact output_state ctx model sameWires cells result original
  · intro Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result) noBorrowedQuantum reference state
  · intro _Reference _original _valid _admitted path _supported
    exact Completion.code_pool_le ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result path
  · intro _Reference _original _valid _admitted path _supported
    exact Completion.code_resident_le ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result path
  · intro _Reference _original _valid _admitted path _supported
    exact Completion.code_auxiliary_le ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result path
  · intro _Reference _original _valid _admitted path _supported
    exact Circuit.depth_le_weightedCount_of_pool_le
      (Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result)
      duration (completionEnvelope (Probability.Input.ofSemiprimeModel model)) path
      (Completion.code_pool_le ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result path)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

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
lemma relational_success {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles ctx Reference)
    (admitted : inputDomain ctx model cells original.localState) :
    Probability.honestAttemptSuccessFloor N ≤
      ((algorithm ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result).relationalDistribution
        (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure
          {pair | accepts model pair.2} := by
  let input := Probability.Input.ofSemiprimeModel model
  let entered := original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel entered :=
    BasisSeeded.mapStore ctx.quantumLayout.zeroLabel original.state
      (BasisSeeded.oracleInput_of_local_support (model := executionModel N)
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
    (((algorithm ctx N (Probability.Input.ofSemiprimeModel model)
      sameWires cells result).run.executionDistribution
        (environment input) original).map
      (fun record => (record.2.2.1,
        (algorithm ctx N (Probability.Input.ofSemiprimeModel model)
          sameWires cells result).run.result
          record))).toOuterMeasure
          {pair | accepts model pair.2}
  rw [PMF.toOuterMeasure_map_apply]
  exact lower

/-- Every real result fiber has the same zero bank in every oracle environment. -/
lemma output_state (input : Input N) (actual : (executionModel N).Environment)
    {Reference : Register}
    (original : OracleInput (executionModel N).classicalOracles ctx Reference) :
    (stateRequirement ctx N cells).Holds original.caller
      ((algorithm ctx N input sameWires cells result).run.finalState
        actual Reference original.state) := by
  intro value
  apply AlgorithmRun.pure_fullSelection_of_executionReadout
    (algorithm ctx N input sameWires cells result).run actual
    (Iteration.context ctx N).quantumLayout.zeroLabel _ original value
  intro reference history _ state selected
  exact BasisSeeded.readout_pure_fullSelection
    ((Completion.code ctx N input sameWires cells result).execute actual reference state)
    (Iteration.context ctx N).quantumLayout.zeroLabel
    (Completion.code_seeded (environment := actual) ctx N input sameWires cells result state)
    (fun store => (algorithm ctx N input sameWires cells result).run.output.eval store) selected

include separated in
/-- One fixed complete round meets all seven obligations for every legal unknown factorization. -/
lemma shorDeclared_round_solves (input : Input N)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) :
    (algorithm ctx N input sameWires cells result).Solves
      (problem ctx N input cells) := by
  constructor
  · intro actual witness Reference original valid admitted
    have same := environment_eq_of_quantum input actual valid
    subst actual
    exact relational_success ctx witness sameWires cells result separated original admitted
  · intro actual _witness Reference original _valid _admitted requirement present
    have same : requirement = stateRequirement ctx N cells := List.mem_singleton.mp present
    subst requirement
    exact output_state ctx sameWires cells result input actual original
  · intro actual _witness Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (Completion.code ctx N input sameWires cells result) actual
      noBorrowedQuantum reference state
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact Completion.code_pool_le ctx N input sameWires cells result path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact Completion.code_resident_le ctx N input sameWires cells result path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact Completion.code_auxiliary_le ctx N input sameWires cells result path
  · intro _actual _witness _Reference _original _valid _admitted path _supported
    exact Circuit.depth_le_weightedCount_of_pool_le
      (Completion.code ctx N input sameWires cells result)
      Resource.Event.quantumDuration (completionEnvelope N) path
      (Completion.code_pool_le ctx N input sameWires cells result path)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

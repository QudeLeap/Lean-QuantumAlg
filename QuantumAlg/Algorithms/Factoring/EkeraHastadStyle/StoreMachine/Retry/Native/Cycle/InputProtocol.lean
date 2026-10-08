/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Soundness

/-!
# Input-based native factoring batch protocol

The original source distribution, rather than a good-key lower bound, specifies
each independently completed batch. A populated value is accepted exactly when
it is a checked nontrivial factor. The actual first and reused batch programs
retain their complete bank/reference state, physical cleanup and independent
resource budgets for every source input. Good-key numerical floors can be
derived separately from this input-based contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.InputProtocol

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {N : Nat}

/-- The independent source failure mass of one fully recovered batch. -/
def sourceFailure (input : Input N) : ENNReal := sampledBatchOutputPMF input none

/-- The exact typed source distribution of one fully recovered batch. -/
def sourceLaw (input : Input N) : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue

/-- The same checked nontrivial-factor event for every original modulus. -/
def accepts (N : Nat) : Set (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  {output | ∃ word, output = .optionSome word ∧
    word.toNat ∣ N ∧ 1 < word.toNat ∧ word.toNat < N}

private theorem accepted_iff_populated (input : Input N)
    (output : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (supported : output ∈ (sourceLaw input).support) :
    output ∈ accepts N ↔ output ≠ CShape.Value.optionNone := by
  cases output with
  | optionNone => simp [accepts]
  | optionSome word =>
      have sound := NativeRetrySelection.batch_outputValue_some_sound input word supported
      constructor
      · intro _ impossible
        cases impossible
      · intro _
        exact ⟨word, rfl, sound.1, sound.2.1, sound.2.2⟩

/-- The source probability of a checked factor is exactly one minus its failure mass. -/
theorem sourceSuccess (input : Input N) :
    (sourceLaw input).toOuterMeasure (accepts N) = 1 - sourceFailure input := by
  calc
    (sourceLaw input).toOuterMeasure (accepts N) =
        (sourceLaw input).toOuterMeasure
          {output | output ≠ CShape.Value.optionNone} := by
      apply PMF.toOuterMeasure_apply_eq_of_inter_support_eq
      ext output
      simp only [Set.mem_inter_iff]
      apply and_congr_left
      intro supported
      exact accepted_iff_populated input output supported
    _ = 1 - sourceFailure input := by
      rw [PMF.eventProbability_eq_one_sub_complement]
      have complement : {output : (LatticeBatchRecoveryOutput.OutputShape N).Value |
          ¬ output ≠ CShape.Value.optionNone} = {CShape.Value.optionNone} := by
        ext output
        simp only [not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      rw [complement, PMF.toOuterMeasure_apply_singleton]
      exact congrArg (fun mass : ENNReal => 1 - mass)
        (NativeRetrySelection.batch_outputValue_none input)

private theorem batchSuccess {pre post : RuntimeCtx .quantum}
    (program : AlgorithmRun RuntimeRound.model pre post
      (LatticeBatchRecoveryOutput.OutputShape N))
    (input : Input N) {Reference : Register}
    (original : OracleInput RuntimeRound.model.classicalOracles pre Reference)
    (law : ReferenceLaw program original (sourceLaw input)) :
    1 - sourceFailure input ≤
      (program.relationalDistribution original).toOuterMeasure
        {pair | pair.2 ∈ accepts N} := by
  have projection :
      (program.relationalDistribution original).toOuterMeasure
          {pair | pair.2 ∈ accepts N} =
        (program.outputDistribution original).toOuterMeasure (accepts N) := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, outputDistribution_of_referenceLaw program original _ law,
    sourceSuccess input]

namespace FirstBatch

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- One actual first batch, with no good-key or caller-bank premise. -/
def problem (input : Input N) :
    Problem RuntimeRound.model base (NativeBatchRecovery.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ output => InputProtocol.accepts N output
  successLB := ⟨1 - sourceFailure input, tsub_le_self⟩
  states := [batchRequirement (model := RuntimeRound.model) (pre := base)
    (NativeCycles.FirstBatch.seed base noQuantum N)
    (NativeCycles.FirstBatch.read base noQuantum N)]
  resources :=
    { events := NativeBatchRecovery.eventEnvelope N
      resident := base.residentSpace + NativeBatchRecovery.additionalSpace N
      auxiliary := base.auxiliarySpace + NativeBatchRecovery.additionalSpace N }
  depth :=
    { duration := fun _ => 1
      limit := NativeBatchRecovery.depthBound N
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Actual first-batch output, joint state, cleanup and budgets meet the source-law contract. -/
theorem solves (input : Input N) :
    Algorithm.Solves (NativeCycles.FirstBatch.algorithm base noQuantum input)
      (problem base noQuantum input) := by
  constructor
  · intro Reference original _valid _initialized
    exact batchSuccess (NativeCycles.FirstBatch.algorithm base noQuantum input).run input
      original (NativeCycles.FirstBatch.referenceLaw base noQuantum input original)
  · intro Reference original _valid _initialized requirement present
    have same : requirement = batchRequirement (model := RuntimeRound.model) (pre := base)
        (NativeCycles.FirstBatch.seed base noQuantum N)
        (NativeCycles.FirstBatch.read base noQuantum N) := List.mem_singleton.mp present
    subst requirement
    exact batchRequirement_holds
      (NativeCycles.FirstBatch.algorithm base noQuantum input).run
      (NativeCycles.FirstBatch.seed base noQuantum N)
      (NativeCycles.FirstBatch.read base noQuantum N) rfl original _
      (NativeCycles.FirstBatch.referenceLaw base noQuantum input original)
      (NativeBatchRecovery.code_seedBlocks base noQuantum input
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))))
  · intro Reference original _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (firstBatch_restartCleanup base noQuantum input).restores reference state
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchRecovery.code_pool_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchRecovery.code_resident_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchRecovery.code_auxiliary_le base noQuantum input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchRecovery.code_depth_le base noQuantum input path

/-- The first actual sampled and recovered batch completes one caller request. -/
def complete (input : Input N) :
    Circuit.CompleteCycle (NativeBatchRecovery.code base noQuantum input)
      (problem base noQuantum input) where
  output := (NativeCycles.FirstBatch.algorithm base noQuantum input).run.output
  certified := solves base noQuantum input

end FirstBatch

namespace ReuseBatch

variable (base : RuntimeCtx .quantum)
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (cells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- A completed later batch on the locally established seed domain. -/
def problem (input : Input N) :
    Problem RuntimeRound.model base (NativeBatchReuseRecovery.context base N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := SeedDomain (NativeCycles.ReuseBatch.inputSeed base sameWires)
  initialization := fun _ => True
  accepts := fun _ output => InputProtocol.accepts N output
  successLB := ⟨1 - sourceFailure input, tsub_le_self⟩
  states := [batchRequirement (model := RuntimeRound.model) (pre := base)
    (NativeCycles.ReuseBatch.seed base sameWires)
    (NativeCycles.ReuseBatch.read base)]
  resources :=
    { events := NativeBatchReuseRecovery.eventEnvelope N
      resident := base.residentSpace + NativeBatchReuseRecovery.additionalSpace N
      auxiliary := base.auxiliarySpace + NativeBatchReuseRecovery.additionalSpace N }
  depth :=
    { duration := fun _ => 1
      limit := NativeBatchReuseRecovery.depthBound N
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

attribute [local irreducible] NativeBatchReuseRecovery.code

/-- The actual fresh-source reuse satisfies the same all-input batch contract. -/
theorem solves (input : Input N)
    (distinct : Function.Injective (fun index => (cells index).key))
    (noBorrowed : base.borrowedQuantumWires = []) :
    Algorithm.Solves (NativeCycles.ReuseBatch.algorithm base sameWires cells input)
      (problem base sameWires input) := by
  constructor
  · intro Reference original valid _initialized
    change SeedDomain (NativeCycles.ReuseBatch.inputSeed base sameWires)
      original.caller.localState at valid
    exact batchSuccess (NativeCycles.ReuseBatch.algorithm base sameWires cells input).run
      input original
      (NativeCycles.ReuseBatch.referenceLaw base sameWires cells input distinct original valid)
  · intro Reference original valid _initialized requirement present
    change SeedDomain (NativeCycles.ReuseBatch.inputSeed base sameWires)
      original.caller.localState at valid
    have same : requirement = batchRequirement (model := RuntimeRound.model) (pre := base)
        (NativeCycles.ReuseBatch.seed base sameWires)
        (NativeCycles.ReuseBatch.read base) := List.mem_singleton.mp present
    subst requirement
    have seeded : RuntimeRound.HasSeedBlocks
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) := by
      change BasisSeeded.Holds (NativeCycles.ReuseBatch.inputSeed base sameWires)
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
      convert seeded_mapRecord
        (NativeCycles.ReuseBatch.inputSeed base sameWires) original.state
        (seeded_input (NativeCycles.ReuseBatch.inputSeed base sameWires) original valid)
        (fun entry => (entry.2, entry.1)) using 1
      exact ExecutionState.executionState_mapClassical_congr original.state rfl
    exact batchRequirement_holds
      (NativeCycles.ReuseBatch.algorithm base sameWires cells input).run
      (NativeCycles.ReuseBatch.seed base sameWires)
      (NativeCycles.ReuseBatch.read base) rfl original _
      (NativeCycles.ReuseBatch.referenceLaw base sameWires cells input distinct original valid)
      (NativeBatchReuseRecovery.code_seedBlocks base sameWires cells input
        (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) seeded)
  · intro Reference original _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (model := RuntimeRound.model) (pre := base)
      (post := NativeBatchReuseRecovery.context base N)
      (NativeBatchReuseRecovery.code base sameWires cells input)
      noBorrowed reference (History := history) state
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_pool_le base sameWires cells input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_resident_le base sameWires cells input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_auxiliary_le base sameWires cells input path
  · intro _Reference _original _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_depth_le base sameWires cells input path

/-- One actual reused bank and its full recovery complete the next request. -/
def complete (input : Input N)
    (distinct : Function.Injective (fun index => (cells index).key))
    (noBorrowed : base.borrowedQuantumWires = []) :
    Circuit.CompleteCycle (NativeBatchReuseRecovery.code base sameWires cells input)
      (problem base sameWires input) where
  output := (NativeCycles.ReuseBatch.algorithm base sameWires cells input).run.output
  certified := solves base sameWires cells input distinct noBorrowed

end ReuseBatch

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles.InputProtocol

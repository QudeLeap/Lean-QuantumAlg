/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Boundary
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Sampled
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Independently completed native factoring batches

Each caller protocol requests one full sampled sixteen-outcome factoring trial,
including classical recovery. Acceptance requires a declared prime, with the
original sampler-adjusted success floor. The state requirement includes the
entire bank and reference, and the budgets are the independent batch formulas.

The first batch admits every caller input and prepares its bank internally.
Reuse admits the locally observable seed domain, allowing every corresponding
reference extension. Its actual predecessor establishes that domain. The seed
is never a new assumption on the outer factoring caller.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A completed batch returns the typed encoding of one of the independently declared primes. -/
def acceptedFactor {N : Nat} (model : GoodKeyModel N) :
    Set (LatticeBatchRecoveryOutput.OutputShape N).Value :=
  LatticeBatchRecoveryOutput.outputValue '' NativeBatchSuccess.accepts model

private theorem source_success {N : Nat} (model : GoodKeyModel N) :
    NativeBatchSuccess.successFloor model.bitWidth ≤
      ((sampledBatchOutputPMF model.input).map
        LatticeBatchRecoveryOutput.outputValue).toOuterMeasure
        (acceptedFactor model) := by
  rw [PMF.toOuterMeasure_map_apply]
  exact (NativeBatchSuccess.sampled_ge model).trans
    (PMF.toOuterMeasure_mono _ (fun value present => ⟨value, present.1, rfl⟩))

private theorem batch_success {pre post : RuntimeCtx .quantum} {N : Nat}
    (program : AlgorithmRun RuntimeRound.model pre post (LatticeBatchRecoveryOutput.OutputShape N))
    (model : GoodKeyModel N) {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles pre Reference)
    (law : ReferenceLaw program input
      ((sampledBatchOutputPMF model.input).map LatticeBatchRecoveryOutput.outputValue)) :
    NativeBatchSuccess.successFloor model.bitWidth ≤
      (program.relationalDistribution input).toOuterMeasure
        {pair | pair.2 ∈ acceptedFactor model} := by
  have projection :
      (program.relationalDistribution input).toOuterMeasure
          {pair | pair.2 ∈ acceptedFactor model} =
        (program.outputDistribution input).toOuterMeasure (acceptedFactor model) := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection, outputDistribution_of_referenceLaw program input _ law]
  exact source_success model

namespace FirstBatch

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The original identity seed on the actual final bank coordinates. -/
def seed (N : Nat) : (NativeBatchRecovery.context base noQuantum N).register.Index :=
  (RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchRecovery.seedWires base noQuantum N)).symm
    (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- The protocol observes the actual retained factor cell. -/
def read (N : Nat) : OutputRead (NativeBatchRecovery.context base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N) :=
  .read (.storage (NativeBatchRecovery.resultRef base noQuantum N).toCStorageRef)

/-- Independent first-trial specification with the original source success floor.

**Input.** Arbitrary normalized caller storage and reference, with no supplied quantum bank.
**Output.** One optional declared prime, plus the complete seed/reference state on every result.
**Resource budget.** Independent first-batch and recovery event, space and unit-depth formulas.
**Success.** The original sampler-adjusted sixteen-sample conditional batch floor.
**Source.** Factoring reduction [EH17, source.tex:878-966] and lattice recovery
[E23, arxiv-v5.tex:329-355], with the original fixed-width residue sampler.
-/
def problem (model : GoodKeyModel N) :
    Problem RuntimeRound.model base (NativeBatchRecovery.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ output => output ∈ acceptedFactor model
  successLB := ⟨NativeBatchSuccess.successFloor model.bitWidth,
    NativeBatchSuccess.successFloor_le_one model.bitWidth⟩
  states := [batchRequirement (model := RuntimeRound.model) (pre := base)
    (seed base noQuantum N) (read base noQuantum N)]
  resources :=
    { events := NativeBatchRecovery.eventEnvelope N
      resident := base.residentSpace + NativeBatchRecovery.additionalSpace N
      auxiliary := base.auxiliarySpace + NativeBatchRecovery.additionalSpace N }
  depth :=
    { duration := fun _ => 1
      limit := NativeBatchRecovery.depthBound N
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- The actual first sampled and recovered batch, with its complete output. -/
def algorithm (specification : Input N) :
    Algorithm RuntimeRound.model base (NativeBatchRecovery.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  ⟨NativeBatchRecovery.run base noQuantum specification⟩

/-- Its exact original factor law retains every incoming reference coordinate. -/
theorem referenceLaw (specification : Input N) {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    ReferenceLaw (algorithm base noQuantum specification).run input
      ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue) := by
  intro weight leftRef rightRef
  let entered := input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  exact (NativeRetryChain.first_weighted_reference base noQuantum specification entered
    weight leftRef rightRef).trans
      (ExecutionState.referenceFiberSum_mapClassical input.state
        (fun entry => (entry.1, (entry.2, entry.1))) (fun _ _ => _) leftRef rightRef)

/-- Success, complete state, borrowed restoration and budgets hold for every caller input. -/
theorem solves (model : GoodKeyModel N) :
    Algorithm.Solves (algorithm base noQuantum model.input) (problem base noQuantum model) := by
  constructor
  · intro Reference input _valid _initialized
    exact batch_success (algorithm base noQuantum model.input).run model input
      (referenceLaw base noQuantum model.input input)
  · intro Reference input _valid _initialized requirement present
    have same : requirement = batchRequirement (model := RuntimeRound.model) (pre := base)
        (seed base noQuantum N)
        (read base noQuantum N) := List.mem_singleton.mp present
    subst requirement
    exact batchRequirement_holds (algorithm base noQuantum model.input).run
      (seed base noQuantum N) (read base noQuantum N) rfl input _
      (referenceLaw base noQuantum model.input input)
      (NativeBatchRecovery.code_seedBlocks base noQuantum model.input
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))))
  · intro Reference input _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact (firstBatch_restartCleanup base noQuantum model.input).restores reference state
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchRecovery.code_pool_le base noQuantum model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchRecovery.code_resident_le base noQuantum model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchRecovery.code_auxiliary_le base noQuantum model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchRecovery.code_depth_le base noQuantum model.input path

/-- One actual first batch completes exactly the independently specified factoring trial. -/
def complete (model : GoodKeyModel N) :
    Circuit.CompleteCycle (NativeBatchRecovery.code base noQuantum model.input)
      (problem base noQuantum model) where
  output := (algorithm base noQuantum model.input).run.output
  certified := solves base noQuantum model

end FirstBatch

namespace ReuseBatch

variable (base : RuntimeCtx .quantum) {N : Nat}
  (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)

/-- The admitted local seed is independently fixed by the source parameters. -/
def inputSeed : base.register.Index :=
  (RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    sameWires).symm (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- The same fixed seed on the final retained context. -/
def seed : (NativeBatchReuseRecovery.context base N).register.Index :=
  (RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuseRecovery.seedWires base sameWires)).symm
    (reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- The independent observation is the new real retained factor cell. -/
def read : OutputRead (NativeBatchReuseRecovery.context base N)
    (LatticeBatchRecoveryOutput.OutputShape N) :=
  .read (.storage (NativeBatchReuseRecovery.resultRef base N).toCStorageRef)

/-- One complete later factoring trial on the locally admitted original bank.

**Input.** The local source seed, allowing every reference extension and classical correlation.
**Output.** One optional declared prime and the same complete seed/reference promise.
**Resource budget.** Independent reused-batch and recovery formulas; no new quantum preparation.
**Success.** The original sampler-adjusted sixteen-sample conditional batch floor.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:329-355]. Actual predecessor
execution proves this internal seed domain; the outer factoring caller has no seed premise.
-/
def problem (model : GoodKeyModel N) :
    Problem RuntimeRound.model base (NativeBatchReuseRecovery.context base N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := SeedDomain (inputSeed base sameWires)
  initialization := fun _ => True
  accepts := fun _ output => output ∈ acceptedFactor model
  successLB := ⟨NativeBatchSuccess.successFloor model.bitWidth,
    NativeBatchSuccess.successFloor_le_one model.bitWidth⟩
  states := [batchRequirement (model := RuntimeRound.model) (pre := base)
    (seed base sameWires) (read base)]
  resources :=
    { events := NativeBatchReuseRecovery.eventEnvelope N
      resident := base.residentSpace + NativeBatchReuseRecovery.additionalSpace N
      auxiliary := base.auxiliarySpace + NativeBatchReuseRecovery.additionalSpace N }
  depth :=
    { duration := fun _ => 1
      limit := NativeBatchReuseRecovery.depthBound N
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

variable (cells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- The actual fresh-source batch reuses the original physical bank and measurement cells. -/
def algorithm (specification : Input N) :
    Algorithm RuntimeRound.model base (NativeBatchReuseRecovery.context base N)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  ⟨NativeBatchReuseRecovery.run base sameWires cells specification⟩

private def emptyRead : CInputRef base (.fixedVector 0 .unit) :=
  .fixedVector fun index => Fin.elim0 index

/-- The seed-domain lift permits the original complete fresh-batch reference law. -/
theorem referenceLaw (specification : Input N)
    (distinct : Function.Injective (fun index => (cells index).key)) {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference)
    (admitted : SeedDomain (inputSeed base sameWires) input.caller.localState) :
    ReferenceLaw (algorithm base sameWires cells specification).run input
      ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue) := by
  intro weight leftRef rightRef
  let entered := input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have seeded : RuntimeRound.HasSeedBlocks
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N entered := by
    change BasisSeeded.Holds (inputSeed base sameWires) entered
    convert seeded_mapRecord (inputSeed base sameWires) input.state
      (seeded_input (inputSeed base sameWires) input admitted)
      (fun entry => (entry.2, entry.1)) using 1
    exact ExecutionState.executionState_mapClassical_congr input.state rfl
  have separate : ∀ index, (cells index).key ∉ (emptyRead base).storageKeys := by
    intro index
    simp only [emptyRead, CInputRef.storageKeys, List.ofFn_zero, List.flatten_nil,
      List.not_mem_nil]
    simp
  exact (NativeBatchReuseRecovery.nativeBatchReuseRecovery_output_weighted_reference
    base sameWires cells specification (emptyRead base) distinct separate entered seeded
    (fun _ value => weight value) leftRef rightRef).trans
      (ExecutionState.referenceFiberSum_mapClassical input.state
        (fun entry => (entry.1, (entry.2, entry.1))) (fun _ _ => _) leftRef rightRef)

attribute [local irreducible] NativeBatchReuseRecovery.code

/-- Actual reuse solves the same factoring protocol on every admitted reference extension. -/
theorem solves (model : GoodKeyModel N)
    (distinct : Function.Injective (fun index => (cells index).key))
    (noBorrowed : base.borrowedQuantumWires = []) :
    Algorithm.Solves (algorithm base sameWires cells model.input)
      (problem base sameWires model) := by
  constructor
  · intro Reference input valid _initialized
    change SeedDomain (inputSeed base sameWires) input.caller.localState at valid
    exact batch_success (algorithm base sameWires cells model.input).run model input
      (referenceLaw base sameWires cells model.input distinct input valid)
  · intro Reference input valid _initialized requirement present
    change SeedDomain (inputSeed base sameWires) input.caller.localState at valid
    have same : requirement = batchRequirement (model := RuntimeRound.model) (pre := base)
        (seed base sameWires)
        (read base) := List.mem_singleton.mp present
    subst requirement
    have seeded : RuntimeRound.HasSeedBlocks
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sameWires N
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) := by
      change BasisSeeded.Holds (inputSeed base sameWires)
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
      convert seeded_mapRecord (inputSeed base sameWires) input.state
        (seeded_input (inputSeed base sameWires) input valid)
        (fun entry => (entry.2, entry.1)) using 1
      exact ExecutionState.executionState_mapClassical_congr input.state rfl
    exact batchRequirement_holds (algorithm base sameWires cells model.input).run
      (seed base sameWires) (read base) rfl input _
      (referenceLaw base sameWires cells model.input distinct input valid)
      (NativeBatchReuseRecovery.code_seedBlocks base sameWires cells model.input
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))) seeded)
  · intro Reference input _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (model := RuntimeRound.model) (pre := base)
      (post := NativeBatchReuseRecovery.context base N)
      (NativeBatchReuseRecovery.code base sameWires cells model.input)
      noBorrowed reference (History := history) state
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_pool_le base sameWires cells model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_resident_le base sameWires cells model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_auxiliary_le base sameWires cells model.input path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeBatchReuseRecovery.code_depth_le base sameWires cells model.input path

/-- The later measured/recovered batch independently completes one actual factoring trial. -/
def complete (model : GoodKeyModel N)
    (distinct : Function.Injective (fun index => (cells index).key))
    (noBorrowed : base.borrowedQuantumWires = []) :
    Circuit.CompleteCycle (NativeBatchReuseRecovery.code base sameWires cells model.input)
      (problem base sameWires model) where
  output := (algorithm base sameWires cells model.input).run.output
  certified := solves base sameWires cells model distinct noBorrowed

end ReuseBatch

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Probability
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Actual retained recovery transports earlier reads and its factor jointly

The deterministic tail maps every complete store and mathematical history,
including the full quantum-reference blocks. Every earlier structural read
survives the real allocation and recovery. On the original source support,
the actual factor is the canonical pure recovery of that same complete source
output. The subsequent probability owner establishes this support internally.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] NativeBatchReuse.context NativeBatchReuse.code body tail step
  RuntimeResults.liftInput RuntimeResults.input

private theorem retained_reference {ctx : RuntimeCtx .quantum}
    {key : StorageKey} {shape : CShape} {fresh : key ∉ ctx.keys}
    (program : Circuit ctx (ctx.addRetained key shape fresh))
    (update : Store ctx → Store (ctx.addRetained key shape fresh) × program.Path)
    (record : Circuit.RetainedRecord program update)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store (ctx.addRetained key shape fresh) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum (program.execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (update entry.1).1) leftRef rightRef := by
  have actual := congrArg
    (fun result : State (ctx.addRetained key shape fresh) Reference (History × program.Path) =>
      ExecutionState.referenceFiberSum result (fun entry _ => weight entry.1) leftRef rightRef)
    (record Reference state)
  exact actual.trans (ExecutionState.referenceFiberSum_mapClassical state
    (fun entry => ((update entry.1).1, (entry.2, (update entry.1).2)))
    (fun entry _ => weight entry.1) leftRef rightRef)

variable (base : RuntimeCtx .quantum) {N : Nat}

/-- The actual tail retains any earlier operand jointly with its actual recovered factor. -/
theorem tail_weighted_reference (input : Input N) {previousShape : CShape}
    (previous : CInputRef (NativeBatchReuse.context base N) previousShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (NativeBatchReuse.context base N) Reference History)
    (weight : previousShape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((tail base input).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput base N previous))
          (entry.1.read (.storage (resultRef base N).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read previous)
          ((step base input entry.1).1.read (.storage (resultRef base N).toCStorageRef)))
        leftRef rightRef := by
  have transported := retained_reference (tail base input) (step base input)
    (tail_execute base input) state
    (fun store => weight (store.read (liftInput base N previous))
      (store.read (.storage (resultRef base N).toCStorageRef))) leftRef rightRef
  refine transported.trans ?_
  exact congrArg
    (fun observe : Store (NativeBatchReuse.context base N) → ℂ =>
      ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) leftRef rightRef)
    (funext fun store => congrArg
      (fun old => weight old
        ((step base input store).1.read (.storage (resultRef base N).toCStorageRef)))
      (tail_callerFrame base input store previous))

variable (sameWires : base.quantumWires =
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
  (originalCells : Fin (measurementBits N) → CWriteRef base (.finite 2))

/-- Pure recovery of the actual complete source Output uses exactly its sixteen stored terminals. -/
theorem packedValue_sourceOutput (before : Store (NativeBatchReuse.context base N)) :
    NativeBatchRecovery.packedValue
        ((NativeBatchReuse.run base N sameWires originalCells).output.eval before) =
      LatticeFixedBatchRecoveryMachine.batchValue
        (NativeBatchRecovery.decodeSource
          ((NativeBatchReuse.run base N sameWires originalCells).output.eval before))
        (sourceTerminals base N) before := by
  unfold NativeBatchRecovery.packedValue NativeBatchRecovery.recoverValue
    LatticeFixedBatchRecoveryMachine.batchValue
  apply congrArg (LatticeBatchRecoveryOutput.outputValue (N := N))
  apply congrArg (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N))
  apply List.Vector.ext
  intro index
  simp only [NativeBatchRecovery.decodeSamples, NativeBatchRecovery.decodeOutcomes,
    LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map, List.Vector.get_ofFn]
  congr 1

private theorem sourceOutput_parameter_read (before : Store (NativeBatchReuse.context base N)) :
    ((NativeBatchReuse.run base N sameWires originalCells).output.eval before).second.first =
      before.read (NativeBatchReuse.finalParameter base N) := by
  unfold NativeBatchReuse.run NativeBatch.resultShape
  rw [Output.all_eval, OutputRead.eval_read]
  exact NativeBatchRecovery.read_middle before (NativeBatchReuse.finalSample base N)
    (NativeBatchReuse.finalParameter base N) (NativeBatchReuse.finalResults base N)

private theorem output_on_source_support (input : Input N)
    (before : Store (NativeBatchReuse.context base N))
    (supported : (NativeBatchReuse.run base N sameWires originalCells).output.eval before ∈
      (NativeBatch.sourceDistribution input).support) :
    (step base input before).1.read (.storage (resultRef base N).toCStorageRef) =
      NativeBatchRecovery.packedValue
        ((NativeBatchReuse.run base N sameWires originalCells).output.eval before) := by
  have parameterStored :=
    (sourceOutput_parameter_read base sameWires originalCells before).symm.trans
      (NativeBatchRecovery.sourceDistribution_parameter input _ supported)
  exact (tail_output base input
    (NativeBatchRecovery.decodeSource
      ((NativeBatchReuse.run base N sameWires originalCells).output.eval before)) before
    parameterStored).trans (packedValue_sourceOutput base sameWires originalCells before).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuseRecovery

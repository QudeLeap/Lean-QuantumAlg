/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Tail
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Resources

/-!
# Packed fixed-batch recovery endpoint

This module composes the real seeded 120-pair recovery pass with the real
wide-to-public output packer.  Workspace allocation remains outside this
component; the relation is already the exact shaped endpoint value over the
sixteen retained terminal cells.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeBatchRecoveryEndpoint

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Observe the mathematical full-path record through the generic composition laws.
attribute [local irreducible] Circuit.sequenceStoreRecord

/-- Recovery tail, output packer, and their shared persistent selector. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the tail stage. -/
  tail : LatticeBatchRecoveryTail.Refs ctx N
  /-- Nested references for the output stage. -/
  output : LatticeBatchRecoveryOutput.Refs ctx N
  sharedSelection : output.selection = tail.fold.factorSelection

/-- Local separation certificates for the two sequential components. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  tail : LatticeBatchRecoveryTail.Separation refs.tail
  output : LatticeBatchRecoveryOutput.Separation refs.output

/-- Avoidance of every cell written by the recovery and output components. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  tail : LatticeBatchRecoveryTail.CallerFrameAvoids refs.tail other
  output : LatticeBatchRecoveryOutput.CallerFrameAvoids refs.output other

/-- Exact shaped pure value of the fixed sixteen-sample batch. -/
def batchOutputValue {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs ctx N) (before : Store ctx) :
    CShape.Value (LatticeBatchRecoveryOutput.OutputShape N) :=
  LatticeBatchRecoveryOutput.outputValue
    (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N)
      (LatticePairRecoveryBatch.preparedSamples
        (preparedResidue sample) refs.tail.terminals before))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Run the seeded pair fold and then materialize its optional result. -/
def into (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (LatticeBatchRecoveryTail.into input refs.tail)
    (LatticeBatchRecoveryOutput.into refs.output)

/-- The actual output packer consumes the complete recovery store. -/
noncomputable def step (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.sequenceStoreRecord (LatticeBatchRecoveryTail.into input refs.tail)
    (LatticeBatchRecoveryOutput.into refs.output)
    (LatticeBatchRecoveryTail.step input refs.tail)
    (LatticeBatchRecoveryOutput.step refs.output) store

/-- Recovery and packing are composed through their actual intermediate store. -/
theorem step_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (step input refs store).1 = (LatticeBatchRecoveryOutput.step refs.output
      (LatticeBatchRecoveryTail.step input refs.tail store).1).1 :=
  Circuit.sequenceStoreRecord_store _ _ _ _ store

/-- The complete shaped endpoint execution retains the actual path and every reference. -/
theorem into_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord _ _ _ _
    (LatticeBatchRecoveryTail.into_execute input refs.tail)
    (LatticeBatchRecoveryOutput.into_execute refs.output) Reference state

/-- Every caller read outside the complete endpoint footprint survives unconditionally. -/
theorem into_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (LatticeBatchRecoveryOutput.into_callerFrame refs.output _ other avoids.output).trans
    (LatticeBatchRecoveryTail.into_callerFrame input refs.tail store other avoids.tail)

/-- The exact public shaped batch value and the complete structural caller frame. -/
structure Relation (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  output : after.read (FirstAccepted.cellRead refs.output.result) =
    batchOutputValue sample refs before
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- The actual recovery-and-packing sequence emits the original shaped fixed-batch value. -/
theorem into_correct (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : LatticeBatchRecoveryTail.InitialConditions input sample store refs.tail) :
    Relation sample refs store (step input refs store).1 := by
  have recovered := LatticeBatchRecoveryTail.into_correct input sample refs.tail
    separation.tail store initial
  have packed := LatticeBatchRecoveryOutput.into_correct refs.output separation.output
    (LatticeBatchRecoveryTail.step input refs.tail store).1
  refine ⟨?_, into_callerFrame input refs store⟩
  rw [step_store, packed.output, refs.sharedSelection, recovered.selected]
  rfl

/-- Independent native allowance for full recovery and both output operations. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  LatticeBatchRecoveryTail.eventEnvelope N + LatticeBatchRecoveryOutput.eventEnvelope N

/-- Independent complete dependency depth includes both final packing operations. -/
def depthBound (N : Nat) : Nat := LatticeBatchRecoveryTail.depthBound N + 2

omit [BitWord.Selected model] in
private theorem sequence_pool_le (first second : Circuit model ctx ctx)
    (firstBound secondBound : ResourcePool model)
    (firstLe : ∀ path, first.resourcePool path ≤ firstBound)
    (secondLe : ∀ path, second.resourcePool path ≤ secondBound)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path ≤ firstBound + secondBound := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (firstLe path.1) (secondLe path.2)

/-- Every actual native coordinate meets the independent complete endpoint allowance. -/
theorem into_pool_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N := by
  unfold into at path ⊢
  unfold eventEnvelope
  with_reducible
    exact sequence_pool_le _ _ _ _
      (LatticeBatchRecoveryTail.into_pool_le input refs.tail)
      (LatticeBatchRecoveryOutput.into_pool_le refs.output) path

/-- The actual complete endpoint meets its independent sequential dependency-depth bound. -/
theorem into_depth_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add (LatticeBatchRecoveryTail.into_depth_le input refs.tail path.1)
    (LatticeBatchRecoveryOutput.into_depth_le refs.output path.2)

/-- The endpoint resident peak includes the same actual native-power scope as recovery. -/
theorem into_resident_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤
      ctx.residentSpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (LatticeBatchRecoveryTail.into input refs.tail)
    (LatticeBatchRecoveryOutput.into refs.output) path).le.trans ?_
  exact SpacePool.max_le (LatticeBatchRecoveryTail.into_resident_le input refs.tail path.1)
    ((LatticeBatchRecoveryOutput.into_resident_le refs.output path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- Auxiliary accounting includes the actual reusable recovery scope and existing context roles. -/
theorem into_auxiliary_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (LatticeBatchRecoveryTail.into input refs.tail)
    (LatticeBatchRecoveryOutput.into refs.output) path).le.trans ?_
  exact SpacePool.max_le (LatticeBatchRecoveryTail.into_auxiliary_le input refs.tail path.1)
    ((LatticeBatchRecoveryOutput.into_auxiliary_le refs.output path.2).trans
      (le_add_of_nonneg_right zero_le))

/-- Recovery and packing jointly restore borrowed systems with arbitrary external references. -/
theorem into_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeBatchRecoveryTail.into_borrowedRestored input refs.tail Reference state)
    (LatticeBatchRecoveryOutput.into_borrowedRestored refs.output Reference _)

end

end LatticeBatchRecoveryEndpoint
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Complete native event allowance of the actual single-bank RSA parent

The independent ledger counts one literal initial load, every real source and
complete recovery, sixteen measured members per batch, their paid packing and
complete reset plus reload, and the final actual optional selector. Every
new bank wire contributes its genuine preparation coordinate. Retained
classical frame and measurement-cell allocations emit no native events.


-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- Each actual bank wire contributes one dimension-tagged native preparation occurrence. -/
def preparationEventBudget (width : Nat) : ResourcePool Model :=
  (1 + 2 * width) • ResourcePool.singleton (model := Model) (.preparation (2 : ℕ+))

/-- The existing literal seed word contributes exactly its selected native X instructions. -/
def seedEventBudget (width N : Nat) : ResourcePool Model :=
  EncodedBit.Word.BasisLoad.xCount (ShortDLP.CompiledMAU.Recycling.seedLabel width N) •
    ResourcePool.singleton (model := Model) (.gate .singleQubit)

/-- Frequency packing remains one paid, width-indexed native classical operation. -/
def packingEventBudget (m ell : Nat) : ResourcePool Model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := Model)
    (.nominalEncoding (.packFiniteBits (ShortDLP.CompiledMAU.Recycling.resultBits m ell)))))

/-- One complete chronological round includes member, paid pack, every reset and literal reload. -/
def roundEventBudget (m ell width N : Nat) : ResourcePool Model :=
  ShortDLP.CompiledMAU.Recycling.Resources.memberBudget m ell width + packingEventBudget m ell +
    ShortDLP.CompiledMAU.Recycling.BankReset.eventBudget width + seedEventBudget width N

/-- The source allowance contains the actual random draw and complete parameter computation. -/
def sourceEventBudget (N : Nat) : ResourcePool Model :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N

/-- Recovery retains the existing complete native ledger for every fixed-batch pair. -/
def recoveryEventBudget (N : Nat) : ResourcePool Model :=
  LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N

/-- All sixteen complete rounds precede one full actual recovery on each batch. -/
def bodyEventBudget (N : Nat) : ResourcePool Model :=
  16 • roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N +
    recoveryEventBudget N

/-- A complete batch additionally draws and computes its own chronological source. -/
def batchEventBudget (N : Nat) : ResourcePool Model :=
  sourceEventBudget N + bodyEventBudget N

/-- The same optional selector reads every factor and performs its actual final pack. -/
def selectionEventBudget (N count : Nat) : ResourcePool Model :=
  FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) count

/-- Independent complete native allowance, with the literal event-free empty branch. -/
def eventBudget (N : Nat) : Nat → ResourcePool Model
  | 0 => 0
  | laterCount + 1 =>
      preparationEventBudget (arithmeticBits N) + seedEventBudget (arithmeticBits N) N +
        (laterCount + 1) • batchEventBudget N + selectionEventBudget N (laterCount + 1)

private lemma events_sequence_le {firstCtx middleCtx lastCtx : RuntimeCtx .quantum}
    (first : Circuit Model firstCtx middleCtx) (second : Circuit Model middleCtx lastCtx)
    (path : (first.seq second).Path) (left right : ResourcePool Model)
    (firstBound : first.resourcePool path.1 ≤ left)
    (secondBound : second.resourcePool path.2 ≤ right) :
    (first.seq second).resourcePool path ≤ left + right := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add firstBound secondBound

private lemma events_six_sequences_le {c0 c1 c2 c3 c4 c5 c6 : RuntimeCtx .quantum}
    (code0 : Circuit Model c0 c1) (code1 : Circuit Model c1 c2)
    (code2 : Circuit Model c2 c3) (code3 : Circuit Model c3 c4)
    (code4 : Circuit Model c4 c5) (code5 : Circuit Model c5 c6)
    (path : (code0.seq (code1.seq (code2.seq (code3.seq (code4.seq code5))))).Path)
    (budget0 budget1 budget2 budget3 budget4 budget5 : ResourcePool Model)
    (bound0 : code0.resourcePool path.1 ≤ budget0)
    (bound1 : code1.resourcePool path.2.1 ≤ budget1)
    (bound2 : code2.resourcePool path.2.2.1 ≤ budget2)
    (bound3 : code3.resourcePool path.2.2.2.1 ≤ budget3)
    (bound4 : code4.resourcePool path.2.2.2.2.1 ≤ budget4)
    (bound5 : code5.resourcePool path.2.2.2.2.2 ≤ budget5) :
    (code0.seq (code1.seq (code2.seq (code3.seq (code4.seq code5))))).resourcePool path ≤
      budget0 + (budget1 + (budget2 + (budget3 + (budget4 + budget5)))) :=
  events_sequence_le code0 (code1.seq (code2.seq (code3.seq (code4.seq code5)))) path
    budget0 _ bound0
    (events_sequence_le code1 (code2.seq (code3.seq (code4.seq code5))) path.2
      budget1 _ bound1
      (events_sequence_le code2 (code3.seq (code4.seq code5)) path.2.2
        budget2 _ bound2
        (events_sequence_le code3 (code4.seq code5) path.2.2.2
          budget3 _ bound3
          (events_sequence_le code4 code5 path.2.2.2.2 budget4 budget5 bound4 bound5))))

private lemma events_source_pool_le {ctx : RuntimeCtx .quantum} (N : Nat)
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N))
    (path : (source N sample parameter).Path) :
    (source N sample parameter).resourcePool path ≤ sourceEventBudget N :=
  events_sequence_le
    (ShorStyle.Canonical.Sampler.PackedSample.draw (model := Model) N sample)
    (ShorStyle.Canonical.Sampler.Program.circuit (model := Model)
      N (FirstAccepted.cellRead sample) parameter) path _ _
    (ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_pool
      (model := Model) N sample path.1).le
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_pool_le
      (model := Model) N (FirstAccepted.cellRead sample) parameter path.2)

private lemma events_round_pool_le (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width N : Nat) {shape : CShape}
    (parameter : CInputRef (ShortDLP.CompiledMAU.Recycling.context
      frame frameNoQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod N)ˣ)
    (result : CWriteRef (ShortDLP.CompiledMAU.Recycling.context
      frame frameNoQuantum m ell width) (.bits (ShortDLP.CompiledMAU.Recycling.resultBits m ell)))
    (path : (ShortDLP.CompiledMAU.Recycling.Round.code
      frame frameNoQuantum m ell width parameter N generator target result).Path) :
    (ShortDLP.CompiledMAU.Recycling.Round.code
      frame frameNoQuantum m ell width parameter N generator target result).resourcePool path ≤
        roundEventBudget m ell width N := by
  have memberBound := ShortDLP.CompiledMAU.Recycling.Resources.member_events
    frame frameNoQuantum m ell width N (generator path.1.1.1) (target path.1.1.1) path.1.1.2
  have packBound : (ShortDLP.CompiledMAU.Recycling.Packing.code
      frame frameNoQuantum m ell width result).resourcePool path.1.2 =
      packingEventBudget m ell := by
    rw [Circuit.resourcePool,
      ShortDLP.CompiledMAU.Recycling.Packing.recyclingPacking_eventTrace]
    simp only [packingEventBudget, ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  have resetBound := ShortDLP.CompiledMAU.Recycling.BankReset.recyclingBankReset_events
    frame frameNoQuantum m ell width path.2.1
  have loadBound := ShortDLP.CompiledMAU.Recycling.Reload.recyclingReload_events
    frame frameNoQuantum m ell width N path.2.2
  change ResourcePool.ofList
    (((ShortDLP.CompiledMAU.Recycling.Round.selected
        frame frameNoQuantum m ell width parameter N generator target).eventTrace path.1.1 ++
      (ShortDLP.CompiledMAU.Recycling.Packing.code
        frame frameNoQuantum m ell width result).eventTrace path.1.2) ++
      ((ShortDLP.CompiledMAU.Recycling.BankReset.code
          frame frameNoQuantum m ell width).eventTrace path.2.1 ++
        (ShortDLP.CompiledMAU.Recycling.Reload.code
          frame frameNoQuantum m ell width N).eventTrace path.2.2)) ≤ _
  simp only [ResourcePool.ofList_append]
  refine (add_le_add (add_le_add memberBound packBound.le)
    (add_le_add resetBound loadBound.le)).trans_eq ?_
  unfold roundEventBudget seedEventBudget
  ac_rfl

private lemma events_bankPreparation_pool (width : Nat) :
    ZeroPreparation.eventCost AlgorithmGate.model .empty
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum BitWord.model .empty =
      preparationEventBudget width := by
  simpa only [ShortDLP.CompiledMAU.Recycling.Arithmetic.width_eq, preparationEventBudget] using
    ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum 2
      (fun _ => rfl) BitWord.model .empty

private lemma events_prepare_pool (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width N : Nat)
    (path : (ShortDLP.CompiledMAU.Recycling.prepare frame frameNoQuantum m ell width N).Path) :
    (ShortDLP.CompiledMAU.Recycling.prepare frame frameNoQuantum m ell width N).resourcePool path =
      preparationEventBudget width + seedEventBudget width N := by
  change ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum BitWord.model .empty ++
    ((MeasurementCells.allocate (model := Model)
        (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width)
        2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell)).eventTrace path.2.1 ++
      (ShortDLP.CompiledMAU.Recycling.Reload.code
        frame frameNoQuantum m ell width N).eventTrace path.2.2)) = _
  have cellsEmpty := MeasurementCells.allocate_eventTrace (model := Model)
    (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width)
    2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell) path.2.1
  rw [cellsEmpty, List.nil_append, ResourcePool.ofList_append]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum BitWord.model .empty +
    (ShortDLP.CompiledMAU.Recycling.Reload.code
      frame frameNoQuantum m ell width N).resourcePool path.2.2 = _
  exact congrArg₂ (fun left right : ResourcePool Model => left + right)
    (events_bankPreparation_pool width)
    (ShortDLP.CompiledMAU.Recycling.Reload.recyclingReload_events
      frame frameNoQuantum m ell width N path.2.2)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma events_firstSource_pool_le (laterCount : Nat)
    (path : (firstSource base N laterCount).Path) :
    (firstSource base N laterCount).resourcePool path ≤ sourceEventBudget N :=
  events_source_pool_le N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (ClassicalFrame.parameterRef base N (laterCount + 1) 0) path

private lemma events_nextSource_pool_le (count : Nat) (batch : Fin count)
    (path : (nextSource base noQuantum N count batch).Path) :
    (nextSource base noQuantum N count batch).resourcePool path ≤ sourceEventBudget N :=
  events_source_pool_le N
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)) path

private lemma events_member_pool_le (count : Nat) (batch : Fin count) (index : Fin 16)
    (path : (member base noQuantum N count batch index).Path) :
    (member base noQuantum N count batch index).resourcePool path ≤
      roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N :=
  events_round_pool_le (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)))
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.packedRef base N count batch index)) path

private lemma events_members_pool_le (count : Nat) (batch : Fin count)
    (path : (members base noQuantum N count batch).Path) :
    (members base noQuantum N count batch).resourcePool path ≤
      16 • roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N :=
  Circuit.forRange_pool_le 16 (member base noQuantum N count batch)
    (roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    (fun index => events_member_pool_le base noQuantum N count batch index) path

private lemma events_recover_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (recover base noQuantum N input count batch).Path) :
    (recover base noQuantum N input count batch).resourcePool path ≤ recoveryEventBudget N :=
  LatticeFixedBatchRecoveryMachine.into_pool_le (model := Model) input
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.factorRef base N count batch)) path

private lemma events_batchBody_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (batchBody base noQuantum N input count batch).Path) :
    (batchBody base noQuantum N input count batch).resourcePool path ≤ bodyEventBudget N :=
  events_sequence_le (members base noQuantum N count batch)
    (recover base noQuantum N input count batch) path _ _
    (events_members_pool_le base noQuantum N count batch path.1)
    (events_recover_pool_le base noQuantum N input count batch path.2)

private lemma events_nextBatch_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (nextBatch base noQuantum N input count batch).Path) :
    (nextBatch base noQuantum N input count batch).resourcePool path ≤ batchEventBudget N :=
  events_sequence_le (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) path _ _
    (events_nextSource_pool_le base noQuantum N count batch path.1)
    (events_batchBody_pool_le base noQuantum N input count batch path.2)

private lemma events_select_pool_le (count : Nat)
    (path : (select base noQuantum N count).Path) :
    (select base noQuantum N count).resourcePool path ≤ selectionEventBudget N count :=
  FirstAccepted.Direct.Optional.Allocation.into_pool_le (model := Model)
    (fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count batch)))
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.selectedRef base N count)) path

/-- The complete positive parent charges every actual native event against its parameter budget. -/
lemma rsaRecyclingParent_positiveCode_pool_le (input : Input N) (laterCount : Nat)
    (path : (positiveCode base noQuantum N input laterCount).Path) :
    (positiveCode base noQuantum N input laterCount).resourcePool path ≤
      eventBudget N (laterCount + 1) := by
  have allocationZero : (ClassicalFrame.allocate base N (laterCount + 1)).resourcePool path.1 =
      0 := by
    rw [Circuit.resourcePool, ClassicalFrame.rsaRecyclingFrame_allocate_trace,
      ResourcePool.ofList_nil]
  have first := events_firstSource_pool_le base N laterCount path.2.1
  have initial := events_prepare_pool (ClassicalFrame.context base N (laterCount + 1))
    (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N path.2.2.1
  have firstBatch := events_batchBody_pool_le base noQuantum N input (laterCount + 1) 0
    path.2.2.2.1
  have tail := Circuit.forRange_pool_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    (batchEventBudget N)
    (fun index => events_nextBatch_pool_le base noQuantum N input (laterCount + 1) index.succ)
    path.2.2.2.2.1
  have last := events_select_pool_le base noQuantum N (laterCount + 1) path.2.2.2.2.2
  refine (events_six_sequences_le
    (ClassicalFrame.allocate base N (laterCount + 1)) (firstSource base N laterCount)
    (ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    (batchBody base noQuantum N input (laterCount + 1) 0)
    (Circuit.forRange laterCount
      (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ))
    (select base noQuantum N (laterCount + 1)) path
    0 (sourceEventBudget N)
    (preparationEventBudget (arithmeticBits N) + seedEventBudget (arithmeticBits N) N)
    (bodyEventBudget N) (laterCount • batchEventBudget N)
    (selectionEventBudget N (laterCount + 1))
    allocationZero.le first initial.le firstBatch tail last).trans_eq ?_
  simp only [zero_add, eventBudget, succ_nsmul, batchEventBudget]
  ac_rfl

/-- Every count bounds the ledger of that same actual run, including the original empty branch. -/
lemma rsaRecyclingParent_run_pool_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.resourcePool path ≤ eventBudget N count := by
  cases count with
  | zero =>
      have empty : (run base noQuantum N input 0).code.resourcePool path = 0 :=
        (congrArg (fun events : List (Resource.Event Model) => ResourcePool.ofList events)
          (NativeRetryEmpty.code_eventTrace base N path)).trans
            (ResourcePool.ofList_nil (model := Model))
      exact empty.le
  | succ laterCount =>
      exact rsaRecyclingParent_positiveCode_pool_le base noQuantum N input laterCount path

end

end QuantumAlg.Factoring.RSA.Recycling.Program

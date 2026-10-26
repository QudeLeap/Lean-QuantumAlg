/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Resources

/-!
# Complete native event allowance of the actual measured constant-workspace RSA parent

The independent ledger counts one literal initial load, every real source and
complete recovery, configured measured members per batch, their paid packing and
complete reset plus reload, and the final actual optional selector. Every
new bank wire contributes its genuine preparation coordinate. Retained
classical frame and measurement-cell allocations emit no native events.


-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := MeasuredRSAModel

/-- Each actual bank wire contributes one dimension-tagged native preparation occurrence. -/
def preparationEventBudget (width : Nat) : ResourcePool Model :=
  (2 * width + 4) • ResourcePool.singleton (model := Model) (.preparation (2 : ℕ+))

/-- The existing literal seed word contributes exactly its selected native X instructions. -/
def seedEventBudget (width N : Nat) : ResourcePool Model :=
  EncodedBit.Word.BasisLoad.xCount (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel width N) •
    ResourcePool.singleton (model := Model) (.gate .singleQubit)

/-- Frequency packing remains one paid, width-indexed native classical operation. -/
def packingEventBudget (m ell : Nat) : ResourcePool Model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := Model)
    (.nominalEncoding (.packFiniteBits (ShortDLP.CompiledMAU.Recycling.resultBits m ell)))))

/-- One complete chronological round includes member, paid pack, every reset and literal reload. -/
def roundEventBudget (m ell width N : Nat) : ResourcePool Model :=
  ShortDLP.CompiledMAU.Recycling.Measured.Round.eventBudget m ell width N

/-- The source allowance contains the actual random draw and complete parameter computation. -/
def sourceEventBudget (N : Nat) : ResourcePool Model :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N

/-- Recovery retains the existing complete native ledger for every fixed-batch pair. -/
def recoveryEventBudget (N : Nat) : ResourcePool Model :=
  LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N
    configuration.additionalMembers

/-- All configured complete rounds precede one full actual recovery on each batch. -/
def bodyEventBudget (N : Nat) : ResourcePool Model :=
  membersPerBatch • roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N +
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

omit configuration in
private lemma events_sequence_le {firstCtx middleCtx lastCtx : RuntimeCtx .quantum}
    (first : Circuit Model firstCtx middleCtx) (second : Circuit Model middleCtx lastCtx)
    (path : (first.seq second).Path) (left right : ResourcePool Model)
    (firstBound : first.resourcePool path.1 ≤ left)
    (secondBound : second.resourcePool path.2 ≤ right) :
    (first.seq second).resourcePool path ≤ left + right := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add firstBound secondBound

omit configuration in
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

omit configuration in
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

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma events_firstSource_pool_le (laterCount : Nat)
    (path : (firstSource base N laterCount).Path) :
    (firstSource base N laterCount).resourcePool path ≤ sourceEventBudget N :=
  events_source_pool_le N (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0) path

private lemma events_nextSource_pool_le (count : Nat) (batch : Fin count)
    (path : (nextSource base noQuantum N count batch).Path) :
    (nextSource base noQuantum N count batch).resourcePool path ≤ sourceEventBudget N :=
  events_source_pool_le N
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.sampleRef base N count batch))
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)) path

private lemma events_member_pool_le (input : Input N) (large : 5 ≤ arithmeticBits N)
    (odd : Odd N) (count : Nat) (batch : Fin count) (index : Fin membersPerBatch)
    (path : (member base noQuantum N input count batch index).Path) :
    (member base noQuantum N input count batch index).resourcePool path ≤
      roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N := by
  have bounded := ShortDLP.CompiledMAU.Recycling.Measured.Round.measuredRound_events
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (measuredRSA_arithmeticBits_atLeastTwo input) large (modulusWord N)
    (by rw [measuredRSA_modulusWord_toNat]; have nontrivial := input.modulus_gt_one; omega)
    (measuredRSA_modulusWord_lowBit odd) (parameterGenerator N) (parameterTargetWord N)
    (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.packedRef base N count batch index)) path
  exact bounded.trans_eq (congrArg
    (ShortDLP.CompiledMAU.Recycling.Measured.Round.eventBudget
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (measuredRSA_modulusWord_toNat N))

private lemma events_members_pool_le (input : Input N) (large : 5 ≤ arithmeticBits N)
    (odd : Odd N) (count : Nat) (batch : Fin count)
    (path : (members base noQuantum N input count batch).Path) :
    (members base noQuantum N input count batch).resourcePool path ≤
      membersPerBatch • roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N :=
  Circuit.forRange_pool_le membersPerBatch (member base noQuantum N input count batch)
    (roundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    (fun index => events_member_pool_le base noQuantum N input large odd count batch index) path

private lemma events_recover_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (recover base noQuantum N input count batch).Path) :
    (recover base noQuantum N input count batch).resourcePool path ≤ recoveryEventBudget N :=
  LatticeFixedBatchRecoveryMachine.into_pool_le (model := Model) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.factorRef base N count batch)) path

private lemma events_batchBody_pool_le (input : Input N)
    (large : 5 ≤ arithmeticBits N) (odd : Odd N) (count : Nat) (batch : Fin count)
    (path : (batchBody base noQuantum N input count batch).Path) :
    (batchBody base noQuantum N input count batch).resourcePool path ≤ bodyEventBudget N :=
  events_sequence_le (members base noQuantum N input count batch)
    (recover base noQuantum N input count batch) path _ _
    (events_members_pool_le base noQuantum N input large odd count batch path.1)
    (events_recover_pool_le base noQuantum N input count batch path.2)

private lemma events_nextBatch_pool_le (input : Input N)
    (large : 5 ≤ arithmeticBits N) (odd : Odd N) (count : Nat) (batch : Fin count)
    (path : (nextBatch base noQuantum N input count batch).Path) :
    (nextBatch base noQuantum N input count batch).resourcePool path ≤ batchEventBudget N :=
  events_sequence_le (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) path _ _
    (events_nextSource_pool_le base noQuantum N count batch path.1)
    (events_batchBody_pool_le base noQuantum N input large odd count batch path.2)

private lemma events_select_pool_le (count : Nat)
    (path : (select base noQuantum N count).Path) :
    (select base noQuantum N count).resourcePool path ≤ selectionEventBudget N count :=
  FirstAccepted.Direct.Optional.Allocation.into_pool_le (model := Model)
    (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)) path

/-- The complete positive parent charges every actual native event against its parameter budget. -/
lemma rsaMeasuredParent_positiveCode_pool_le (input : Input N)
    (large : 5 ≤ arithmeticBits N) (odd : Odd N) (laterCount : Nat)
    (path : (positiveCode base noQuantum N input laterCount).Path) :
    (positiveCode base noQuantum N input laterCount).resourcePool path ≤
      eventBudget N (laterCount + 1) := by
  have allocationZero :
      (Recycling.ClassicalFrame.allocate base N (laterCount + 1)).resourcePool path.1 =
      0 := by
    rw [Circuit.resourcePool, Recycling.ClassicalFrame.rsaRecyclingFrame_allocate_trace,
      ResourcePool.ofList_nil]
  have first := events_firstSource_pool_le base N laterCount path.2.1
  have initial :=
    ShortDLP.CompiledMAU.Recycling.Measured.measuredPreparation_events
      (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat path.2.2.1
  have initialPool :
      (ShortDLP.CompiledMAU.Recycling.Measured.prepare
        (Recycling.ClassicalFrame.context base N (laterCount + 1))
        (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat).resourcePool
          path.2.2.1 =
        preparationEventBudget (arithmeticBits N) + seedEventBudget (arithmeticBits N) N := by
    refine initial.trans ?_
    unfold ShortDLP.CompiledMAU.Recycling.Measured.measuredPreparationBudget
    rw [measuredRSA_modulusWord_toNat]
    rfl
  have firstBatch := events_batchBody_pool_le base noQuantum N input large odd (laterCount + 1) 0
    path.2.2.2.1
  have tail := Circuit.forRange_pool_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    (batchEventBudget N)
    (fun index => events_nextBatch_pool_le
      base noQuantum N input large odd (laterCount + 1) index.succ)
    path.2.2.2.2.1
  have last := events_select_pool_le base noQuantum N (laterCount + 1) path.2.2.2.2.2
  refine (events_six_sequences_le
    (Recycling.ClassicalFrame.allocate base N (laterCount + 1)) (firstSource base N laterCount)
    (ShortDLP.CompiledMAU.Recycling.Measured.prepare
      (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat)
    (batchBody base noQuantum N input (laterCount + 1) 0)
    (Circuit.forRange laterCount
      (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ))
    (select base noQuantum N (laterCount + 1)) path
    0 (sourceEventBudget N)
    (preparationEventBudget (arithmeticBits N) + seedEventBudget (arithmeticBits N) N)
    (bodyEventBudget N) (laterCount • batchEventBudget N)
    (selectionEventBudget N (laterCount + 1))
    allocationZero.le first initialPool.le firstBatch tail last).trans_eq ?_
  simp only [zero_add, eventBudget, succ_nsmul, batchEventBudget]
  ac_rfl

/-- Every count bounds the ledger of that same actual run, including the original empty branch. -/
lemma rsaMeasuredParent_run_pool_le (input : Input N)
    (large : 5 ≤ arithmeticBits N) (odd : Odd N) (count : Nat)
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
      exact rsaMeasuredParent_positiveCode_pool_le base noQuantum N input large odd laterCount path

end

end QuantumAlg.Factoring.RSA.Measured.Program

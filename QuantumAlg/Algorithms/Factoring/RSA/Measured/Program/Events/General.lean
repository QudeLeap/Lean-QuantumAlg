/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Resources.General
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Actual measured RSA native envelope on every original modulus input

The same chronological syntax retains every source draw, measured member,
full physical reset/reload, complete pair recovery and final selection.
The independent general arithmetic cap includes even moduli and widths two,
three and four. No key witness narrows this resource domain
[G25, main.tex:199-295,354-360; EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical

private abbrev Model := MeasuredRSAModel

/-- The complete actual round uses the parity-independent arithmetic ledger. -/
def generalRoundEventBudget (m ell width N : Nat) : ResourcePool Model :=
  ShortDLP.CompiledMAU.Recycling.Measured.Resources.General.roundBudget m ell width N

/-- Every configured original member precedes the same complete native pair recovery. -/
def generalBodyEventBudget (N : Nat) : ResourcePool Model :=
  membersPerBatch • generalRoundEventBudget
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N + recoveryEventBudget N

/-- Each actual batch retains its own fresh native draw and parameter computation. -/
def generalBatchEventBudget (N : Nat) : ResourcePool Model :=
  sourceEventBudget N + generalBodyEventBudget N

/-- Independent full-domain event formula; the original empty run remains event-free. -/
def generalEventBudget (N : Nat) : Nat → ResourcePool Model
  | 0 => 0
  | laterCount + 1 =>
      preparationEventBudget (arithmeticBits N) + seedEventBudget (arithmeticBits N) N +
        (laterCount + 1) • generalBatchEventBudget N + selectionEventBudget N (laterCount + 1)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma generalEvents_member_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (index : Fin membersPerBatch)
    (path : (member base noQuantum N input count batch index).Path) :
    (member base noQuantum N input count batch index).resourcePool path ≤
      generalRoundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N := by
  have bounded :=
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.General.measuredGeneralRound_events
      (Recycling.ClassicalFrame.context base N count)
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (FirstAccepted.cellRead (bankWrite base noQuantum N count
        (Recycling.ClassicalFrame.parameterRef base N count batch)))
      (measuredRSA_arithmeticBits_atLeastTwo input) (modulusWord N)
      (parameterGenerator N) (parameterTargetWord N)
      (bankWrite base noQuantum N count
        (Recycling.ClassicalFrame.packedRef base N count batch index)) path
  exact bounded.trans_eq (congrArg
    (ShortDLP.CompiledMAU.Recycling.Measured.Resources.General.roundBudget
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (measuredRSA_modulusWord_toNat N))

private lemma generalEvents_members_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (members base noQuantum N input count batch).Path) :
    (members base noQuantum N input count batch).resourcePool path ≤
      membersPerBatch • generalRoundEventBudget
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N :=
  Circuit.forRange_pool_le membersPerBatch (member base noQuantum N input count batch)
    (generalRoundEventBudget (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    (fun index => generalEvents_member_pool_le base noQuantum N input count batch index) path

private lemma generalEvents_recover_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (recover base noQuantum N input count batch).Path) :
    (recover base noQuantum N input count batch).resourcePool path ≤ recoveryEventBudget N :=
  LatticeFixedBatchRecoveryMachine.into_pool_le (model := Model) input
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (terminals base noQuantum N count batch)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.factorRef base N count batch)) path

private lemma generalEvents_batchBody_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (batchBody base noQuantum N input count batch).Path) :
    (batchBody base noQuantum N input count batch).resourcePool path ≤ generalBodyEventBudget N :=
  events_sequence_le (members base noQuantum N input count batch)
    (recover base noQuantum N input count batch) path _ _
    (generalEvents_members_pool_le base noQuantum N input count batch path.1)
    (generalEvents_recover_pool_le base noQuantum N input count batch path.2)

private lemma generalEvents_nextBatch_pool_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (nextBatch base noQuantum N input count batch).Path) :
    (nextBatch base noQuantum N input count batch).resourcePool path ≤ generalBatchEventBudget N :=
  events_sequence_le (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) path _ _
    (events_nextSource_pool_le base noQuantum N count batch path.1)
    (generalEvents_batchBody_pool_le base noQuantum N input count batch path.2)

private lemma generalEvents_select_pool_le (count : Nat)
    (path : (select base noQuantum N count).Path) :
    (select base noQuantum N count).resourcePool path ≤ selectionEventBudget N count :=
  FirstAccepted.Direct.Optional.Allocation.into_pool_le (model := Model)
    (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch)))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)) path

/-- The complete positive parent charges every actual native event against its parameter budget. -/
lemma rsaMeasuredGeneral_positiveCode_pool_le (input : Input N) (laterCount : Nat)
    (path : (positiveCode base noQuantum N input laterCount).Path) :
    (positiveCode base noQuantum N input laterCount).resourcePool path ≤
      generalEventBudget N (laterCount + 1) := by
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
  have firstBatch := generalEvents_batchBody_pool_le base noQuantum N input (laterCount + 1) 0
    path.2.2.2.1
  have tail := Circuit.forRange_pool_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    (generalBatchEventBudget N)
    (fun index => generalEvents_nextBatch_pool_le
      base noQuantum N input (laterCount + 1) index.succ)
    path.2.2.2.2.1
  have last := generalEvents_select_pool_le base noQuantum N (laterCount + 1) path.2.2.2.2.2
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
    (generalBodyEventBudget N) (laterCount • generalBatchEventBudget N)
    (selectionEventBudget N (laterCount + 1))
    allocationZero.le first initialPool.le firstBatch tail last).trans_eq ?_
  simp only [zero_add, generalEventBudget, succ_nsmul, generalBatchEventBudget]
  ac_rfl

/-- Every count bounds the ledger of that same actual run, including the original empty branch. -/
lemma rsaMeasuredGeneral_run_pool_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.resourcePool path ≤ generalEventBudget N count := by
  cases count with
  | zero =>
      have empty : (run base noQuantum N input 0).code.resourcePool path = 0 :=
        (congrArg (fun events : List (Resource.Event Model) => ResourcePool.ofList events)
          (NativeRetryEmpty.code_eventTrace base N path)).trans
            (ResourcePool.ofList_nil (model := Model))
      exact empty.le
  | succ laterCount =>
      exact rsaMeasuredGeneral_positiveCode_pool_le base noQuantum N input laterCount path


/-- Independent general native work bounds the actual full-domain quantum schedule. -/
def generalQuantumTimeLimit (N count : Nat) : Nat :=
  ResourcePool.weightedCount Resource.Event.quantumDuration (generalEventBudget N count)

/-- Every native gate coordinate has its own independent full-domain scalar allowance. -/
def generalGateCountLimit (N count : Nat) (coordinate : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count (model := Model) (.gate coordinate) (generalEventBudget N count)

/-- The classical native coordinate is kept separate from all quantum gate coordinates. -/
def generalClassicalOperationLimit (N count : Nat) : Nat :=
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight (generalEventBudget N count)

/-- Every original modulus input satisfies each actual native gate bound at every finite count. -/
lemma rsaMeasuredGeneral_run_gateCount_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate coordinate)
      ((run base noQuantum N input count).code.resourcePool path) ≤
        generalGateCountLimit N count coordinate :=
  ResourcePool.le_iff_count.mp
    (rsaMeasuredGeneral_run_pool_le base noQuantum N input count path) (.gate coordinate)

/-- All classical operations of the same actual full-domain path retain their separate bound. -/
lemma rsaMeasuredGeneral_run_classicalOperation_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum N input count).code.resourcePool path) ≤
        generalClassicalOperationLimit N count :=
  ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (rsaMeasuredGeneral_run_pool_le base noQuantum N input count path)

/-- The same actual path satisfies the full-domain quantum-time bound. -/
lemma rsaMeasuredGeneral_run_quantumTime_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.quantumTime path ≤ generalQuantumTimeLimit N count :=
  Circuit.depth_le_weightedCount_of_pool_le (run base noQuantum N input count).code
    Resource.Event.quantumDuration (generalEventBudget N count) path
    (rsaMeasuredGeneral_run_pool_le base noQuantum N input count path)

end

end QuantumAlg.Factoring.RSA.Measured.Program

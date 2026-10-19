/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.ClassicalCoordinates
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Execution.Time

/-!
# Independent quantum time of the actual single-bank RSA parent

The same actual parent prepares its bank once, runs sixteen complete measured
members per batch, and resets plus reloads after every member, including the
last. Purely classical sampling, parameter computation, recovery and final
selection retain their native ledger entries and have zero quantum duration.

-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- The original literal seed loader contributes its actual native X count. -/
def seedLoadQuantumTime (N : Nat) : Nat :=
  EncodedBit.Word.BasisLoad.xCount
    (ShortDLP.CompiledMAU.Recycling.seedLabel (arithmeticBits N) N)

/-- One actual complete member includes the terminal parallel reset and seed reload. -/
def memberQuantumTimeLimit (N : Nat) : Nat :=
  ShortDLP.CompiledMAU.Recycling.Resources.memberTime
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) + 1 + seedLoadQuantumTime N

/-- Independent whole-run time includes one initial load and all sixteen members per batch. -/
def quantumTimeLimit (N : Nat) : Nat → Nat
  | 0 => 0
  | laterCount + 1 =>
      seedLoadQuantumTime N + 16 * (laterCount + 1) * memberQuantumTimeLimit N

private lemma quantum_sequence_le {firstCtx middleCtx lastCtx : RuntimeCtx .quantum}
    (first : Circuit Model firstCtx middleCtx) (second : Circuit Model middleCtx lastCtx)
    (path : (first.seq second).Path) (left right : Nat)
    (firstBound : first.quantumTime path.1 ≤ left)
    (secondBound : second.quantumTime path.2 ≤ right) :
    (first.seq second).quantumTime path ≤ left + right :=
  (Circuit.quantumTime_seq first second path.1 path.2).trans_le
    (Nat.add_le_add firstBound secondBound)

private lemma quantum_six_sequences_le {c0 c1 c2 c3 c4 c5 c6 : RuntimeCtx .quantum}
    (code0 : Circuit Model c0 c1) (code1 : Circuit Model c1 c2)
    (code2 : Circuit Model c2 c3) (code3 : Circuit Model c3 c4)
    (code4 : Circuit Model c4 c5) (code5 : Circuit Model c5 c6)
    (path : (code0.seq (code1.seq (code2.seq (code3.seq (code4.seq code5))))).Path)
    (budget0 budget1 budget2 budget3 budget4 budget5 : Nat)
    (bound0 : code0.quantumTime path.1 ≤ budget0)
    (bound1 : code1.quantumTime path.2.1 ≤ budget1)
    (bound2 : code2.quantumTime path.2.2.1 ≤ budget2)
    (bound3 : code3.quantumTime path.2.2.2.1 ≤ budget3)
    (bound4 : code4.quantumTime path.2.2.2.2.1 ≤ budget4)
    (bound5 : code5.quantumTime path.2.2.2.2.2 ≤ budget5) :
    (code0.seq (code1.seq (code2.seq (code3.seq (code4.seq code5))))).quantumTime path ≤
      budget0 + (budget1 + (budget2 + (budget3 + (budget4 + budget5)))) :=
  quantum_sequence_le code0 (code1.seq (code2.seq (code3.seq (code4.seq code5)))) path
    budget0 _ bound0
    (quantum_sequence_le code1 (code2.seq (code3.seq (code4.seq code5))) path.2
      budget1 _ bound1
      (quantum_sequence_le code2 (code3.seq (code4.seq code5)) path.2.2
        budget2 _ bound2
        (quantum_sequence_le code3 (code4.seq code5) path.2.2.2
          budget3 _ bound3
          (quantum_sequence_le code4 code5 path.2.2.2.2 budget4 budget5 bound4 bound5))))

private lemma quantum_range_le {ctx : RuntimeCtx .quantum} (count : Nat)
    (body : Fin count → Circuit Model ctx ctx) (budget : Nat)
    (bound : ∀ index path, (body index).quantumTime path ≤ budget)
    (path : (Circuit.forRange count body).Path) :
    (Circuit.forRange count body).quantumTime path ≤ count * budget :=
  (Circuit.forRange_depth_le_sum count body Resource.Event.quantumDuration
    (fun _ => budget) bound path).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id])

private lemma classicalQuantumWeight_zero {execution : ExecutionModel}
    (pool : ResourcePool execution)
    (absent : ∀ event : Resource.Event execution,
      (∀ label, event ≠ .classicalOperation label) → ResourcePool.count event pool = 0) :
    ResourcePool.weightedCount Resource.Event.quantumDuration pool = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event emitted
  cases event with
  | classicalOperation _ => rfl
  | classicalQuery _ => rfl
  | preparation _ => rfl
  | measurement _ => rfl
  | gate coordinate =>
      have zero := absent (.gate coordinate) (fun _ => by simp)
      have positive := Multiset.count_pos.mpr emitted
      exact False.elim ((Nat.ne_of_gt positive) zero)
  | oracle coordinate =>
      have zero := absent (.oracle coordinate) (fun _ => by simp)
      have positive := Multiset.count_pos.mpr emitted
      exact False.elim ((Nat.ne_of_gt positive) zero)

private lemma source_pool_le {ctx : RuntimeCtx .quantum} (N : Nat)
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N))
    (path : (source N sample parameter).Path) :
    (source N sample parameter).resourcePool path ≤
      ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N := by
  change ResourcePool.ofList
    ((ShorStyle.Canonical.Sampler.PackedSample.draw (model := Model) N sample).eventTrace path.1 ++
      (ShorStyle.Canonical.Sampler.Program.circuit (model := Model)
        N (FirstAccepted.cellRead sample) parameter).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_pool
      (model := Model) N sample path.1).le
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_pool_le
      (model := Model) N (FirstAccepted.cellRead sample) parameter path.2)

private lemma sourceQuantumWeight_zero (N : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) = 0 :=
  classicalQuantumWeight_zero _ (fun event outside =>
    OracleModel.Native.Declared.declared_source_count_eq_zero
      (model := Model) event outside N)

private lemma source_quantumTime_zero {ctx : RuntimeCtx .quantum} (N : Nat)
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N))
    (path : (source N sample parameter).Path) :
    (source N sample parameter).quantumTime path = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Circuit.depth_le_weightedCount_of_pool_le (source N sample parameter)
    Resource.Event.quantumDuration
    (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) path
    (source_pool_le N sample parameter path)).trans_eq (sourceQuantumWeight_zero N)

private lemma recoveryQuantumWeight_zero (N : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N) = 0 :=
  classicalQuantumWeight_zero _ (fun event outside =>
    OracleModel.Native.Declared.declared_recovery_count_eq_zero
      (model := Model) event outside N)

private lemma selectionQuantumWeight_zero (N count : Nat) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) count) =
      0 := by
  simp [FirstAccepted.Direct.Optional.Allocation.eventEnvelope, ResourcePool.scale,
    FirstAccepted.Direct.Optional.eventEnvelope, FirstAccepted.Direct.copyTrace,
    Resource.Event.quantumDuration]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma firstSource_quantumTime_zero (laterCount : Nat)
    (path : (firstSource base N laterCount).Path) :
    (firstSource base N laterCount).quantumTime path = 0 :=
  source_quantumTime_zero N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (ClassicalFrame.parameterRef base N (laterCount + 1) 0) path

private lemma nextSource_quantumTime_zero (count : Nat) (batch : Fin count)
    (path : (nextSource base noQuantum N count batch).Path) :
    (nextSource base noQuantum N count batch).quantumTime path = 0 :=
  source_quantumTime_zero N
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)) path

private lemma member_quantumTime_le (count : Nat) (batch : Fin count) (index : Fin 16)
    (path : (member base noQuantum N count batch index).Path) :
    (member base noQuantum N count batch index).quantumTime path ≤ memberQuantumTimeLimit N := by
  have bound := ShortDLP.CompiledMAU.Recycling.Round.code_quantumTime
    (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch))) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.packedRef base N count batch index)) path
  refine bound.trans_eq ?_
  simp only [memberQuantumTimeLimit, seedLoadQuantumTime,
    ShortDLP.CompiledMAU.Recycling.Round.quantumTimeLimit, Nat.add_assoc]

private lemma members_quantumTime_le (count : Nat) (batch : Fin count)
    (path : (members base noQuantum N count batch).Path) :
    (members base noQuantum N count batch).quantumTime path ≤
      16 * memberQuantumTimeLimit N :=
  quantum_range_le 16 (member base noQuantum N count batch) (memberQuantumTimeLimit N)
    (fun index => member_quantumTime_le base noQuantum N count batch index) path

private lemma recover_quantumTime_zero (input : Input N) (count : Nat) (batch : Fin count)
    (path : (recover base noQuantum N input count batch).Path) :
    (recover base noQuantum N input count batch).quantumTime path = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Circuit.depth_le_weightedCount_of_pool_le
    (recover base noQuantum N input count batch) Resource.Event.quantumDuration
    (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N) path
    (LatticeFixedBatchRecoveryMachine.into_pool_le (model := Model) input
      (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.parameterRef base N count batch)))
      (terminals base noQuantum N count batch)
      (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.factorRef base N count batch))
      path)).trans_eq
      (recoveryQuantumWeight_zero N)

private lemma batchBody_quantumTime_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (batchBody base noQuantum N input count batch).Path) :
    (batchBody base noQuantum N input count batch).quantumTime path ≤
      16 * memberQuantumTimeLimit N :=
  (quantum_sequence_le (members base noQuantum N count batch)
    (recover base noQuantum N input count batch) path _ 0
    (members_quantumTime_le base noQuantum N count batch path.1)
    (recover_quantumTime_zero base noQuantum N input count batch path.2).le).trans_eq
      (Nat.add_zero _)

private lemma nextBatch_quantumTime_le (input : Input N) (count : Nat) (batch : Fin count)
    (path : (nextBatch base noQuantum N input count batch).Path) :
    (nextBatch base noQuantum N input count batch).quantumTime path ≤
      16 * memberQuantumTimeLimit N :=
  (quantum_sequence_le (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) path 0 _
    (nextSource_quantumTime_zero base noQuantum N count batch path.1).le
    (batchBody_quantumTime_le base noQuantum N input count batch path.2)).trans_eq
      (Nat.zero_add _)

private lemma select_quantumTime_zero (count : Nat)
    (path : (select base noQuantum N count).Path) :
    (select base noQuantum N count).quantumTime path = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Circuit.depth_le_weightedCount_of_pool_le (select base noQuantum N count)
    Resource.Event.quantumDuration
    (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) count) path
    (FirstAccepted.Direct.Optional.Allocation.into_pool_le
      (model := Model)
      (fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.factorRef base N count batch)))
      (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.selectedRef base N count))
      path)).trans_eq (selectionQuantumWeight_zero N count)

private lemma prepare_quantumTime_le (frame : RuntimeCtx .quantum)
    (frameNoQuantum : frame.quantumWires = []) (m ell width N : Nat)
    (path : (ShortDLP.CompiledMAU.Recycling.prepare frame frameNoQuantum m ell width N).Path) :
    (ShortDLP.CompiledMAU.Recycling.prepare frame frameNoQuantum m ell width N).quantumTime path ≤
      EncodedBit.Word.BasisLoad.xCount (ShortDLP.CompiledMAU.Recycling.seedLabel width N) := by
  let allocated : Circuit Model frame
      (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width) :=
    Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
      frame frame.canonicalFreshKey
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum
      frame.runtimeCtx_canonicalFreshKey_fresh
      (ShortDLP.CompiledMAU.Recycling.allocationDisjoint frame frameNoQuantum width)
  let retained : Circuit Model
      (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width)
      (ShortDLP.CompiledMAU.Recycling.context frame frameNoQuantum m ell width) :=
    MeasurementCells.allocate (model := Model)
      (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width)
      2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell)
  let loaded : Circuit Model
      (ShortDLP.CompiledMAU.Recycling.context frame frameNoQuantum m ell width)
      (ShortDLP.CompiledMAU.Recycling.context frame frameNoQuantum m ell width) :=
    ShortDLP.CompiledMAU.Recycling.Reload.code frame frameNoQuantum m ell width N
  have allocatedTime : allocated.quantumTime path.1 = 0 :=
    Circuit.quantumTime_prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
      frame frame.canonicalFreshKey
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.layout width).toQuantum
      frame.runtimeCtx_canonicalFreshKey_fresh
      (ShortDLP.CompiledMAU.Recycling.allocationDisjoint frame frameNoQuantum width) path.1
  have retainedTime : retained.quantumTime path.2.1 = 0 :=
    MeasurementCells.allocate_depth (model := Model)
      (ShortDLP.CompiledMAU.Recycling.bankContext frame frameNoQuantum width)
      2 (ShortDLP.CompiledMAU.Recycling.resultBits m ell) Resource.Event.quantumDuration path.2.1
  have loadedTime := ShortDLP.CompiledMAU.Recycling.Reload.recyclingReload_quantumTime
    frame frameNoQuantum m ell width N path.2.2
  exact (quantum_sequence_le allocated (retained.seq loaded) path 0 _ allocatedTime.le
    (quantum_sequence_le retained loaded path.2 0 _ retainedTime.le loadedTime)).trans_eq
      (by simp only [Nat.zero_add])

/-- The same actual positive parent pays one initial load and each complete chronological round. -/
lemma rsaRecyclingParent_positiveCode_quantumTime_le (input : Input N) (laterCount : Nat)
    (path : (positiveCode base noQuantum N input laterCount).Path) :
    (positiveCode base noQuantum N input laterCount).quantumTime path ≤
      quantumTimeLimit N (laterCount + 1) := by
  have allocationZero := ClassicalFrame.rsaRecyclingFrame_allocate_depth
    base N (laterCount + 1) Resource.Event.quantumDuration path.1
  have firstZero := firstSource_quantumTime_zero base N laterCount path.2.1
  have initial := prepare_quantumTime_le (ClassicalFrame.context base N (laterCount + 1))
    (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N path.2.2.1
  have first := batchBody_quantumTime_le base noQuantum N input (laterCount + 1) 0
    path.2.2.2.1
  have tail := quantum_range_le laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    (16 * memberQuantumTimeLimit N)
    (fun index => nextBatch_quantumTime_le base noQuantum N input (laterCount + 1) index.succ)
    path.2.2.2.2.1
  have lastZero := select_quantumTime_zero base noQuantum N (laterCount + 1) path.2.2.2.2.2
  refine (quantum_six_sequences_le
    (ClassicalFrame.allocate base N (laterCount + 1)) (firstSource base N laterCount)
    (ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    (batchBody base noQuantum N input (laterCount + 1) 0)
    (Circuit.forRange laterCount
      (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ))
    (select base noQuantum N (laterCount + 1)) path
    0 0 (seedLoadQuantumTime N) (16 * memberQuantumTimeLimit N)
    (laterCount * (16 * memberQuantumTimeLimit N)) 0
    allocationZero.le firstZero.le initial first tail lastZero.le).trans_eq ?_
  simp only [quantumTimeLimit, Nat.zero_add, Nat.add_zero]
  ring

/-- Every natural count bounds the quantum time of that same run, with the literal empty case. -/
lemma rsaRecyclingParent_run_quantumTime_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.quantumTime path ≤ quantumTimeLimit N count := by
  cases count with
  | zero =>
      change (NativeRetryEmpty.code base N).depth Resource.Event.quantumDuration path ≤ 0
      exact (NativeRetryEmpty.code_depth base N Resource.Event.quantumDuration path).le
  | succ laterCount =>
      exact rsaRecyclingParent_positiveCode_quantumTime_le base noQuantum N input laterCount path

end

end QuantumAlg.Factoring.RSA.Recycling.Program

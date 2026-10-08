/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Probability
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Complete chronological factor weights along the actual same-bank suffix

Each induction step observes the protected earlier operand together with
the next real retained factor. The actual next batch's full joint reference
law then supplies the same factor kernel before continuing the real suffix.
Fresh result keys and preserved original measurement identities discharge
the additional structural separation introduced by this induction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] RuntimeResults.context RuntimeResults.liftInput
  RuntimeResults.liftWrite RuntimeResults.input

private theorem reuseInput_storage (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) :
    NativeBatchReuseRecovery.callerInput start N (.storage ref.toCStorageRef) =
      .storage (reuseWrite N ref).toCStorageRef := by
  unfold NativeBatchReuseRecovery.callerInput NativeBatchReuseRecovery.liftInput
    NativeBatchReuse.callerInput NativeBatchReuse.finalInput reuseWrite
  exact congrArg
    (fun input : CInputRef (NativeBatchReuse.context start N) shape =>
      input.underRetained (NativeBatchReuseRecovery.resultKey start N)
        (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatchReuse.context start N).canonicalFreshKey_fresh)
    (RuntimeResults.shortDLP_runtimeResults_lift_storage
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (NativeBatchReuse.sampledWrite start N ref) 16)

private theorem reuseInput_product (N : Nat) {start : RuntimeCtx .quantum}
    {left right : CShape} (first : CInputRef start left) (second : CInputRef start right) :
    NativeBatchReuseRecovery.callerInput start N (.product first second) =
      .product (NativeBatchReuseRecovery.callerInput start N first)
        (NativeBatchReuseRecovery.callerInput start N second) := by
  unfold NativeBatchReuseRecovery.callerInput NativeBatchReuseRecovery.liftInput
    NativeBatchReuse.callerInput NativeBatchReuse.finalInput
  exact congrArg
    (fun input : CInputRef (NativeBatchReuse.context start N) (.product left right) =>
      input.underRetained (NativeBatchReuseRecovery.resultKey start N)
        (LatticeBatchRecoveryOutput.OutputShape N)
        (NativeBatchReuse.context start N).canonicalFreshKey_fresh)
    (RuntimeRepetition.liftInput_product
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) first)
      (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) second) 16)

private theorem reuseInput_keys (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef start shape) :
    (NativeBatchReuseRecovery.callerInput start N input).storageKeys = input.storageKeys := by
  let sampled := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) input
  have sampleKeys : sampled.storageKeys = input.storageKeys := by
    unfold sampled ShorStyle.Canonical.Sampler.Retained.liftInput
    exact (CInputRef.storageKeys_underRetained _ _ _ _).trans
      (CInputRef.storageKeys_underRetained _ _ _ _)
  have roundKeys := RuntimeResults.shortDLP_runtimeResults_liftInput_keys
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) sampled 16
  unfold NativeBatchReuseRecovery.callerInput NativeBatchReuseRecovery.liftInput
  exact (CInputRef.storageKeys_underRetained _ _ _ _).trans (roundKeys.trans sampleKeys)

private theorem suffixInput_storage (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) (count : Nat) :
    suffixInput N (.storage ref.toCStorageRef) count =
      .storage (suffixWrite N ref count).toCStorageRef := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction =>
      exact (congrArg (fun input => suffixInput N input count)
        (reuseInput_storage N ref)).trans (induction (reuseWrite N ref))

private theorem suffixInput_product (N : Nat) {start : RuntimeCtx .quantum}
    {left right : CShape} (first : CInputRef start left) (second : CInputRef start right)
    (count : Nat) :
    suffixInput N (.product first second) count =
      .product (suffixInput N first count) (suffixInput N second count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count induction =>
      exact (congrArg (fun input => suffixInput N input count)
        (reuseInput_product N first second)).trans
        (induction (NativeBatchReuseRecovery.callerInput start N first)
          (NativeBatchReuseRecovery.callerInput start N second))

private theorem reuseWrite_result_ne (N : Nat) {start : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef start shape) :
    (reuseWrite N ref).key ≠ (NativeBatchReuseRecovery.resultRef start N).key := by
  let before := RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (NativeBatchReuse.sampledWrite start N ref) 16
  intro same
  apply (NativeBatchReuse.context start N).canonicalFreshKey_fresh
  have live : before.key ∈ (NativeBatchReuse.context start N).keys :=
    List.mem_map_of_mem before.toCStorageRef.present
  have keyEq : before.key = (NativeBatchReuse.context start N).canonicalFreshKey := same
  exact keyEq ▸ live

/-- The chronological suffix observation reads only its actual individual retained factor cells. -/
def suffixValues (N : Nat) (start : RuntimeCtx .quantum) (count : Nat)
    (store : Store (suffixContext N start count)) :
    List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count :=
  List.Vector.ofFn (fun index => store.read
    (.storage (suffixResults N start count index).toCStorageRef))

private theorem suffixValues_cons (N : Nat) (start : RuntimeCtx .quantum) (count : Nat)
    (store : Store (suffixContext N start (count + 1))) :
    suffixValues N start (count + 1) store =
      List.Vector.cons
        (store.read (.storage
          (suffixWrite N (NativeBatchReuseRecovery.resultRef start N) count).toCStorageRef))
        (suffixValues N (NativeBatchReuseRecovery.context start N) count store) := by
  apply List.Vector.ext
  intro index
  refine Fin.cases ?_ (fun index => ?_) index
  · simp only [suffixValues, List.Vector.get_ofFn, suffixResults, List.Vector.get_cons_zero]
    rfl
  · simp only [suffixValues, List.Vector.get_ofFn, suffixResults, List.Vector.get_cons_succ]
    rfl

attribute [local irreducible] NativeBatchReuseRecovery.code NativeBatchReuseRecovery.callerInput
  NativeBatchReuseRecovery.context NativeBatchReuse.code reuseWrite
  ExecutionState.referenceFiberSum

private theorem reuse_joint_separate (N : Nat) {start : RuntimeCtx .quantum}
    {shape : CShape} (previous : CInputRef start shape)
    (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
    (separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
    (index : Fin (measurementBits N)) :
    (reuseWrite N (originalCells index)).key ∉
      (CInputRef.product (NativeBatchReuseRecovery.callerInput start N previous)
        (.storage (NativeBatchReuseRecovery.resultRef start N).toCStorageRef)).storageKeys := by
  intro present
  rcases List.mem_append.mp present with oldKey | headKey
  · have oldMember : (originalCells index).key ∈ previous.storageKeys := by
      have transported := (reuseInput_keys N previous) ▸ oldKey
      exact (reuseWrite_key N (originalCells index)) ▸ transported
    exact separate index oldMember
  · exact reuseWrite_result_ne N (originalCells index) (List.mem_singleton.mp headKey)

/-- The real suffix's complete joint weights follow the original independent factor-vector PMF. -/
theorem suffix_weighted_reference {N : Nat} (input : Input N) :
    ∀ (count : Nat) {previousShape : CShape} (start : RuntimeCtx .quantum)
      (wires : start.quantumWires =
        (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires)
      (previous : CInputRef start previousShape)
      (originalCells : Fin (measurementBits N) → CWriteRef start (.finite 2))
      (_distinct : Function.Injective (fun index => (originalCells index).key))
      (_separate : ∀ index, (originalCells index).key ∉ previous.storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State start Reference (RuntimeRound.model.HiddenState × History)),
      RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
        wires N state →
      ∀ (weight : previousShape.Value →
          List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count → ℂ)
        (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum
          ((suffixCode input start wires originalCells count).execute Reference state)
          (fun entry _ => weight (entry.1.read (suffixInput N previous count))
            (suffixValues N start count entry.1)) leftRef rightRef =
        ExecutionState.referenceFiberSum state
          (fun entry _ => ∑ values :
              List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count,
            ((PMF.independentReplicateVector
              ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
              count values).toReal : ℂ) * weight (entry.1.read previous) values)
          leftRef rightRef := by
  intro count
  induction count with
  | zero =>
      intro previousShape start wires previous originalCells _distinct _separate
        Reference History _ state _seeded weight leftRef rightRef
      let observe := fun store : Store start => weight (store.read previous) List.Vector.nil
      have executed := congrArg
        (fun final : State start Reference (RuntimeRound.model.HiddenState × (History × Unit)) =>
          ExecutionState.referenceFiberSum final (fun entry _ => observe entry.1)
            leftRef rightRef)
        (Circuit.execute_id_mapClassical (model := RuntimeRound.model) Reference state)
      have transported := executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => observe entry.1) leftRef rightRef)
      have empty (store : Store start) : suffixValues N start 0 store = List.Vector.nil :=
        Subsingleton.elim _ _
      have aligned := congrArg
        (fun read : Store start → ℂ => ExecutionState.referenceFiberSum
          ((Circuit.id (model := RuntimeRound.model) start).execute Reference state)
          (fun entry _ => read entry.1)
            leftRef rightRef)
        (funext fun store => congrArg (weight (store.read previous)) (empty store))
      exact aligned.trans (transported.trans (congrArg
        (fun read : Store start → ℂ => ExecutionState.referenceFiberSum state
          (fun entry _ => read entry.1) leftRef rightRef)
        (funext fun store => (RuntimeRepetition.weighted_empty
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          (weight (store.read previous))).symm)))
  | succ count induction =>
      intro previousShape start wires previous originalCells distinct separate
        Reference History _ state seeded weight leftRef rightRef
      let next := NativeBatchReuseRecovery.context start N
      let nextWires := (NativeBatchReuseRecovery.context_base_wires start N).trans wires
      let nextCells := fun index => reuseWrite N (originalCells index)
      let nextPrevious := NativeBatchReuseRecovery.callerInput start N previous
      let head := NativeBatchReuseRecovery.resultRef start N
      let joint := CInputRef.product nextPrevious (.storage head.toCStorageRef)
      let first := NativeBatchReuseRecovery.code start wires originalCells input
      let rest := suffixCode input next nextWires nextCells count
      let advanced : State next Reference
          (RuntimeRound.model.HiddenState × (History × first.Path)) := first.execute Reference state
      let finalWeight := fun store : Store (suffixContext N start (count + 1)) =>
        weight (store.read (suffixInput N previous (count + 1)))
          (suffixValues N start (count + 1) store)
      let restWeight := fun old : (CShape.product previousShape
          (LatticeBatchRecoveryOutput.OutputShape N)).Value =>
        fun values : List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count =>
          weight old.first (List.Vector.cons old.second values)
      have nextDistinct : Function.Injective (fun index => (nextCells index).key) := by
        intro left right same
        exact distinct ((reuseWrite_key N (originalCells left)).symm.trans
          (same.trans (reuseWrite_key N (originalCells right))))
      have nextSeparate := reuse_joint_separate N previous originalCells separate
      have nextSeed := NativeBatchReuseRecovery.code_seedBlocks start wires originalCells
        input state seeded
      have restLaw := induction next nextWires joint nextCells nextDistinct nextSeparate
        advanced nextSeed restWeight leftRef rightRef
      have finalRead (store : Store (suffixContext N start (count + 1))) :
          finalWeight store = restWeight (store.read (suffixInput N joint count))
            (suffixValues N next count store) := by
        have headRead := congrArg
          (fun ref : CInputRef (suffixContext N next count)
              (LatticeBatchRecoveryOutput.OutputShape N) => store.read ref)
          (suffixInput_storage N head count)
        have jointRead := congrArg
          (fun ref : CInputRef (suffixContext N next count)
              (.product previousShape (LatticeBatchRecoveryOutput.OutputShape N)) =>
            store.read ref)
          (suffixInput_product N nextPrevious (.storage head.toCStorageRef) count)
        have jointValue := jointRead.trans (congrArg
          (fun factor => CShape.Value.product (store.read (suffixInput N nextPrevious count))
            factor) headRead)
        have expanded := congrArg
          (weight (store.read (suffixInput N previous (count + 1))))
          (suffixValues_cons N start count store)
        exact expanded.trans (congrArg
          (fun old => restWeight old (suffixValues N next count store)) jointValue.symm)
      have aligned := congrArg
        (fun read : Store (suffixContext N next count) → ℂ =>
          ExecutionState.referenceFiberSum (rest.execute Reference advanced)
            (fun entry _ => read entry.1) leftRef rightRef) (funext finalRead)
      let firstWeight := fun old : previousShape.Value =>
        fun factor : (LatticeBatchRecoveryOutput.OutputShape N).Value =>
          ∑ values : List.Vector (LatticeBatchRecoveryOutput.OutputShape N).Value count,
            ((PMF.independentReplicateVector
              ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
              count values).toReal : ℂ) * weight old (List.Vector.cons factor values)
      have firstLaw := NativeBatchReuseRecovery.nativeBatchReuseRecovery_output_weighted_reference
        start wires originalCells input previous distinct separate state seeded firstWeight
        leftRef rightRef
      have summed := congrArg
        (fun read : Store start → ℂ => ExecutionState.referenceFiberSum state
          (fun entry _ => read entry.1) leftRef rightRef)
        (funext fun store => (PMF.independentReplicateVector_weighted_cons
          ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          count (weight (store.read previous))).symm)
      exact (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef).trans (aligned.trans (restLaw.trans (firstLaw.trans summed)))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

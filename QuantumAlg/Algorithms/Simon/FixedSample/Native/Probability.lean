/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Observation
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.VectorMass

/-!
# The joint law of the actual fixed Simon samples

The original first sample uses the actual preparation; the following samples
use the paid reset of the same bank. The complete reference observation is
derived by composing their conditional Born laws on the actual intermediate
states. The resulting finite vector law is the original independent product
distribution, without an independent-outcomes assumption.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Different fixed sample indices designate different actually retained cells. -/
theorem nativeSimon_slot_keys (base : RuntimeCtx .quantum) (n count : Nat) :
    Function.Injective (fun index => (slotRef base n count index).key) := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          change (slots base n count).canonicalFreshKey = (slotRef base n count right).key at same
          have present := MeasurementCells.reference_key_mem
            (slotRef base n count right).toCStorageRef
          exact False.elim ((slots base n count).canonicalFreshKey_fresh (same.symm ▸ present))
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          change (slotRef base n count left).key = (slots base n count).canonicalFreshKey at same
          have present := MeasurementCells.reference_key_mem
            (slotRef base n count left).toCStorageRef
          exact False.elim ((slots base n count).canonicalFreshKey_fresh (same ▸ present))
        · intro same
          exact congrArg Fin.succ (ih same)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n total : Nat)

/-- The quantum preparation changes no retained sample identity. -/
theorem nativeSimon_bankSlot_keys :
    Function.Injective (fun index => (bankSlot base noQuantum n total index).key) :=
  nativeSimon_slot_keys base n total

/-- The result-cell allocation also keeps those same distinct sample identities. -/
theorem nativeSimon_sampleRef_keys :
    Function.Injective (fun index => (sampleRef base noQuantum n total index).key) := by
  intro left right same
  have keys := (MeasurementCells.liftWrite_key 2
    (bankSlot base noQuantum n total left) n).symm.trans
      (same.trans (MeasurementCells.liftWrite_key 2
        (bankSlot base noQuantum n total right) n))
  exact nativeSimon_bankSlot_keys base noQuantum n total keys

/-- A joint sample event observes the actual stored slots in the supplied chronological order. -/
def sampleIndicator (count : Nat) (indices : Fin count → Fin total)
    (outcomes : Fin count → Outcome n) (store : Store (context base noQuantum n total)) : ℂ :=
  ∏ index : Fin count,
    if store.read (.storage (sampleRef base noQuantum n total (indices index)).toCStorageRef) =
      CShape.Value.bits (outcomes index) then 1 else 0

private theorem reference_congr {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n total) Reference History)
    (first second : Store (context base noQuantum n total) → ℂ)
    (equal : ∀ store, first store = second store) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => first entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => second entry.1) leftRef rightRef :=
  congrArg (fun observe : Store (context base noQuantum n total) → ℂ =>
    ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) leftRef rightRef)
      (funext equal)

/-- The actual reset-sample loop has its product law jointly with old structural inputs and Ref. -/
theorem nativeSimon_range_reference (sampling : SamplingCircuit n) :
    ∀ (count : Nat) (indices : Fin count → Fin total) (_distinct : Function.Injective indices)
      {shape : CShape} (other : CInputRef (bankContext base noQuantum n total) shape)
      (_separate : ∀ index, (bankSlot base noQuantum n total (indices index)).key ∉
        other.storageKeys)
      {Reference : Register} {History : Type} [Fintype History]
      (state : State (context base noQuantum n total) Reference History)
      (weight : shape.Value → ℂ) (outcomes : Fin count → Outcome n)
      (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum
        ((Circuit.forRange count (fun index =>
          reusedSample base noQuantum n total sampling (indices index))).execute Reference state)
        (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)) *
          sampleIndicator base noQuantum n total count indices outcomes entry.1) leftRef rightRef =
      (∏ index : Fin count, ((sampling.outcomePMF (outcomes index)).toReal : ℂ)) *
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)))
          leftRef rightRef := by
  intro count
  induction count with
  | zero =>
      intro indices _distinct shape other _separate Reference History _
        state weight outcomes leftRef rightRef
      have executed := congrArg
        (fun output : State (context base noQuantum n total) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)))
            leftRef rightRef) (Circuit.execute_id_mapClassical Reference state)
      have mapped := ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry _ => weight (entry.1.read (MeasurementCells.liftInput 2 other n)))
        leftRef rightRef
      simp only [Circuit.forRange, sampleIndicator, Fin.prod_univ_zero, mul_one, one_mul]
      convert executed.trans mapped using 1
      congr 1
  | succ count ih =>
      intro indices distinct shape other separate Reference History _
        state weight outcomes leftRef rightRef
      let head := bankSlot base noQuantum n total (indices 0)
      let joint : CInputRef (bankContext base noQuantum n total) (.product shape (.bits n)) :=
        .product other (.storage head.toCStorageRef)
      let first := reusedSample base noQuantum n total sampling (indices 0)
      let rest := Circuit.forRange count fun index =>
        reusedSample base noQuantum n total sampling (indices index.succ)
      let advanced := first.execute Reference state
      let headIndicator := fun value : (CShape.bits n).Value =>
        if value = CShape.Value.bits (outcomes 0) then (1 : ℂ) else 0
      let tailWeight := fun value : (CShape.product shape (.bits n)).Value =>
        weight value.first * headIndicator value.second
      have tailDistinct : Function.Injective (fun index : Fin count => indices index.succ) :=
        fun _ _ same => Fin.succ_injective _ (distinct same)
      have tailSeparate : ∀ index : Fin count,
          (bankSlot base noQuantum n total (indices index.succ)).key ∉ joint.storageKeys := by
        intro index present
        rcases List.mem_append.mp present with old | atHead
        · exact separate index.succ old
        · have same := nativeSimon_bankSlot_keys base noQuantum n total
            (List.mem_singleton.mp atHead)
          have impossible := congrArg Fin.val (distinct same)
          simp only [Fin.val_succ, Fin.val_zero] at impossible
          omega
      have tailLaw := ih (fun index => indices index.succ) tailDistinct joint tailSeparate
        advanced tailWeight (fun index => outcomes index.succ) leftRef rightRef
      let finalWeight := fun store : Store (context base noQuantum n total) =>
        weight (store.read (MeasurementCells.liftInput 2 other n)) *
          sampleIndicator base noQuantum n total (count + 1) indices outcomes store
      have aligned := reference_congr base noQuantum n total (rest.execute Reference advanced)
        finalWeight (fun store => tailWeight (store.read (MeasurementCells.liftInput 2 joint n)) *
          sampleIndicator base noQuantum n total count (fun index => indices index.succ)
            (fun index => outcomes index.succ) store) (fun store => by
          dsimp only [finalWeight, tailWeight, joint, headIndicator, head]
          rw [MeasurementCells.liftInput_product, MeasurementCells.liftInput_storage]
          dsimp only [Store.read, CShape.Value.first, CShape.Value.second, sampleIndicator]
          rw [Fin.prod_univ_succ]
          change weight (store.read (MeasurementCells.liftInput 2 other n)) *
            ((if store.read (.storage (sampleRef base noQuantum n total (indices 0)).toCStorageRef)
              = CShape.Value.bits (outcomes 0) then 1 else 0) * _) =
            (weight (store.read (MeasurementCells.liftInput 2 other n)) *
              (if store.read (.storage
                (sampleRef base noQuantum n total (indices 0)).toCStorageRef) =
                  CShape.Value.bits (outcomes 0) then 1 else 0)) * _
          ring) leftRef rightRef
      have headAligned := reference_congr base noQuantum n total advanced
        (fun store => tailWeight (store.read (MeasurementCells.liftInput 2 joint n)))
        (fun store => weight (store.read (MeasurementCells.liftInput 2 other n)) *
          if store.read (.storage (sampleRef base noQuantum n total (indices 0)).toCStorageRef) =
            CShape.Value.bits (outcomes 0) then 1 else 0) (fun store => by
          dsimp only [tailWeight, joint, headIndicator, head]
          rw [MeasurementCells.liftInput_product, MeasurementCells.liftInput_storage]
          rfl) leftRef rightRef
      have headLaw := nativeSimon_reusedSample_outcome_reference base noQuantum n total sampling
        (indices 0) other (separate 0) state weight (outcomes 0) leftRef rightRef
      have composed := (Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef).trans (aligned.trans (tailLaw.trans
          (congrArg (fun coefficient : ℂ =>
            (∏ index : Fin count, ((sampling.outcomePMF (outcomes index.succ)).toReal : ℂ)) *
              coefficient) (headAligned.trans headLaw))))
      refine composed.trans ?_
      rw [Fin.prod_univ_succ]
      ring

private def emptyRead (ctx : RuntimeCtx .quantum) : CInputRef ctx (.fixedVector 0 .unit) :=
  .fixedVector fun index => Fin.elim0 index

private theorem emptyRead_keys (ctx : RuntimeCtx .quantum) : (emptyRead ctx).storageKeys = [] := by
  simp only [emptyRead, CInputRef.storageKeys, List.ofFn_zero, List.flatten_nil]

/-- The real first sample and all paid successors have the original joint Born law. -/
theorem nativeSimon_sampleBatch_reference (sampling : SamplingCircuit n)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n total) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum n total).quantumLayout.zeroLabel state)
    (outcomes : Fin total → Outcome n) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((sampleBatch base noQuantum n sampling total).execute Reference state)
      (fun entry _ => sampleIndicator base noQuantum n total total id outcomes entry.1)
        leftRef rightRef =
      (∏ index : Fin total, ((sampling.outcomePMF (outcomes index)).toReal : ℂ)) *
        ExecutionState.referenceFiberSum state (fun _ _ => 1) leftRef rightRef := by
  cases total with
  | zero =>
      have executed := congrArg
        (fun output : State (context base noQuantum n 0) Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output (fun _ _ => 1) leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      have mapped := ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ()))) (fun _ _ => 1) leftRef rightRef
      simp only [sampleBatch, sampleIndicator, Fin.prod_univ_zero, one_mul]
      convert executed.trans mapped using 1
      congr 1
  | succ count =>
      let head := bankSlot base noQuantum n (count + 1) 0
      let first := sample base noQuantum n (count + 1) sampling 0
      let rest := Circuit.forRange count fun index =>
        reusedSample base noQuantum n (count + 1) sampling index.succ
      let advanced := first.execute Reference state
      let headIndicator := fun value : (CShape.bits n).Value =>
        if value = CShape.Value.bits (outcomes 0) then (1 : ℂ) else 0
      have separate : ∀ index : Fin count,
          (bankSlot base noQuantum n (count + 1) index.succ).key ∉
            (CInputRef.storage head.toCStorageRef).storageKeys := by
        intro index present
        have same := nativeSimon_bankSlot_keys base noQuantum n (count + 1)
          (List.mem_singleton.mp present)
        exact Fin.succ_ne_zero index same
      have tailLaw := nativeSimon_range_reference base noQuantum n (count + 1) sampling count
        Fin.succ (Fin.succ_injective _) (.storage head.toCStorageRef) separate advanced
        headIndicator (fun index => outcomes index.succ) leftRef rightRef
      have aligned := reference_congr base noQuantum n (count + 1)
        (rest.execute Reference advanced)
        (sampleIndicator base noQuantum n (count + 1) (count + 1) id outcomes)
        (fun store => headIndicator (store.read
          (MeasurementCells.liftInput 2 (.storage head.toCStorageRef) n)) *
          sampleIndicator base noQuantum n (count + 1) count Fin.succ
            (fun index => outcomes index.succ) store) (fun store => by
          rw [MeasurementCells.liftInput_storage]
          dsimp only [sampleIndicator, headIndicator, head]
          rw [Fin.prod_univ_succ]
          rfl) leftRef rightRef
      have emptySeparate : (bankSlot base noQuantum n (count + 1) 0).key ∉
          (emptyRead (bankContext base noQuantum n (count + 1))).storageKeys := by
        rw [emptyRead_keys]
        exact List.not_mem_nil
      have firstLaw := nativeSimon_sample_outcome_reference base noQuantum n (count + 1)
        sampling 0 (emptyRead (bankContext base noQuantum n (count + 1))) emptySeparate
        state seeded (fun _ => 1) (outcomes 0) leftRef rightRef
      have headLaw : ExecutionState.referenceFiberSum advanced
          (fun entry _ => headIndicator (entry.1.read
            (MeasurementCells.liftInput 2 (.storage head.toCStorageRef) n)))
            leftRef rightRef =
          ((sampling.outcomePMF (outcomes 0)).toReal : ℂ) *
            ExecutionState.referenceFiberSum state (fun _ _ => 1) leftRef rightRef := by
        simp only [MeasurementCells.liftInput_storage]
        dsimp only [advanced, first, headIndicator, head]
        simp only [one_mul] at firstLaw
        convert firstLaw using 1
        congr 1
      have combined := (Circuit.referenceFiberSum_execute_seq first rest state
        (sampleIndicator base noQuantum n (count + 1) (count + 1) id outcomes)
        leftRef rightRef).trans (aligned.trans (tailLaw.trans
          (congrArg (fun coefficient : ℂ =>
            (∏ index : Fin count, ((sampling.outcomePMF (outcomes index.succ)).toReal : ℂ)) *
              coefficient) headLaw)))
      refine combined.trans ?_
      rw [Fin.prod_univ_succ]
      ring

/-- The actual allocator and loop establish the joint law from every original complete state. -/
theorem nativeSimon_code_reference (sampling : SamplingCircuit n)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (outcomes : Fin total → Outcome n)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum n total sampling).execute Reference state)
      (fun entry _ => sampleIndicator base noQuantum n total total id outcomes entry.1)
        leftRef rightRef =
      (∏ index : Fin total, ((sampling.outcomePMF (outcomes index)).toReal : ℂ)) *
        ExecutionState.referenceFiberSum state (fun _ _ => 1) leftRef rightRef := by
  have first := Circuit.referenceFiberSum_execute_seq (allocate base noQuantum n total)
    (sampleBatch base noQuantum n sampling total) state
    (sampleIndicator base noQuantum n total total id outcomes) leftRef rightRef
  have sampled := nativeSimon_sampleBatch_reference base noQuantum n total sampling
    ((allocate base noQuantum n total).execute Reference state)
    (nativeSimon_allocate_seeded base noQuantum n total state) outcomes leftRef rightRef
  have allocated := nativeSimon_allocate_reference base noQuantum n total (emptyRead base)
    state (fun _ => 1) leftRef rightRef
  exact first.trans (sampled.trans (congrArg
    (fun coefficient : ℂ =>
      (∏ index : Fin total, ((sampling.outcomePMF (outcomes index)).toReal : ℂ)) * coefficient)
    allocated))

/-- Read the same stored bit vectors as a mathematical vector of original measurement outcomes. -/
def sampleOutcomes (value : (CShape.fixedVector total (.bits n)).Value) :
    List.Vector (Outcome n) total :=
  List.Vector.ofFn fun index position => ((value.get index).bitGet position).toBool

private theorem sampleOutcomes_eq_iff (value : (CShape.fixedVector total (.bits n)).Value)
    (outcomes : List.Vector (Outcome n) total) :
    sampleOutcomes n total value = outcomes ↔
      ∀ index, value.get index = CShape.Value.bits (outcomes.get index) := by
  constructor
  · intro same index
    have atIndex := congrArg (fun samples : List.Vector (Outcome n) total => samples.get index) same
    simp only [sampleOutcomes, List.Vector.get_ofFn] at atIndex
    cases actual : value.get index with
    | bits bits =>
        rw [actual] at atIndex
        change bits = outcomes.get index at atIndex
        exact congrArg CShape.Value.bits atIndex
  · intro same
    apply List.Vector.ext
    intro index
    simp only [sampleOutcomes, List.Vector.get_ofFn]
    rw [same index]
    rfl

private theorem sampleIndicator_observed (store : Store (context base noQuantum n total))
    (outcomes : List.Vector (Outcome n) total) :
    sampleIndicator base noQuantum n total total id outcomes.get store =
      if sampleOutcomes n total (store.read (samplesInput base noQuantum n total)) = outcomes
      then (1 : ℂ) else 0 := by
  rw [sampleIndicator, Fintype.prod_boole]
  have same := sampleOutcomes_eq_iff n total
    (store.read (samplesInput base noQuantum n total)) outcomes
  split <;> split
  · rfl
  · rename_i observed missing
    exact (missing (same.mpr observed)).elim
  · rename_i missing observed
    exact (missing (same.mp observed)).elim
  · rfl

/-- The decoded actual output PMF is the original finite independent vector law. -/
theorem nativeSimon_run_outputDistribution (sampling : SamplingCircuit n)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum n total sampling).outputDistribution input).map (sampleOutcomes n total) =
      PMF.independentReplicateVector sampling.outcomePMF total := by
  let actual := run base noQuantum n total sampling
  let distribution := PMF.independentReplicateVector sampling.outcomePMF total
  change (((actual.execute Reference input.state).toPMF (actual.execute_normalized input)).map
    actual.result).map (sampleOutcomes n total) = distribution
  rw [PMF.map_comp]
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum input.state
    (actual.execute Reference input.state) input.normalized (actual.execute_normalized input)
  intro outcomes leftRef rightRef
  let initial := input.state.mapClassical (fun store => (store, store))
  have read := reference_congr base noQuantum n total (actual.execute Reference input.state)
    (fun store => if sampleOutcomes n total (store.read (samplesInput base noQuantum n total)) =
      outcomes then (1 : ℂ) else 0)
    (sampleIndicator base noQuantum n total total id outcomes.get)
    (fun store => (sampleIndicator_observed base noQuantum n total store outcomes).symm)
    leftRef rightRef
  have joint := nativeSimon_code_reference base noQuantum n total sampling initial outcomes.get
    leftRef rightRef
  have old := ExecutionState.referenceFiberSum_mapClassical input.state
    (fun store => (store, store)) (fun _ _ => (1 : ℂ)) leftRef rightRef
  refine read.trans (joint.trans ?_)
  rw [old]
  have probability :
      (∏ index : Fin total, ((sampling.outcomePMF (outcomes.get index)).toReal : ℂ)) =
      ((distribution outcomes).toReal : ℂ) := by
    rw [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]
  rw [probability]
  simp only [ExecutionState.referenceFiberSum, Finset.mul_sum, one_mul]

end

end QuantumAlg.SimonsProblem.FixedSample.Native

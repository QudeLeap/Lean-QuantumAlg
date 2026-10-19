/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Setup.Probability
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Next.Probability
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Next.Caller
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.FiniteWeights
import all QuantumAlg.Util.PMF.VectorMass
import Mathlib.Data.ENNReal.Inv
import Mathlib.Probability.Distributions.Uniform

/-!
# Joint physical source read for the declared EH batches

The structural read observes the original source, complete parameter and
sixteen chronological sample cells. Finite reindexing of their actual joint
Born indicator law yields the canonical source distribution, preserving both
coordinates of every external reference block.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] context nextBatch

/-- The source, complete parameter and sixteen chronological sample values. -/
def resultShape (N : Nat) : CShape :=
  .product (.bits (residueSamplingBits N))
    (.product (ParameterShape N) (.fixedVector 16 (.bits (measurementBits N))))

/-- One exact source value and its conditional sample vector. -/
def sourceValue {N : Nat} (input : Input N)
    (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) :
    (resultShape N).Value :=
  .product (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source))
    (.product (parameterValue input source)
      (.fixedVector (fun index => .bits (samples.get index))))

/-- Pure same-source distribution, independent of the physical batch module. -/
def sourceDistribution {N : Nat} (input : Input N) : PMF (resultShape N).Value :=
  (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind fun source =>
    (PMF.independentReplicateVector (selectedOutcomePMF (parameterValue input source)) 16).map
      (sourceValue input source)

private lemma reference_sum {C Index : Type} [Fintype C] [Fintype Index]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (weight : Index → C → R.Index → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun value basis => ∑ index, weight index value basis)
        left right =
      ∑ index, ExecutionState.referenceFiberSum state (weight index) left right := by
  simp only [ExecutionState.referenceFiberSum, Finset.sum_mul]
  calc
    _ = ∑ basis : R.Index, ∑ index : Index, ∑ value : C,
        weight index value basis * (state.block value).matrix (basis, left) (basis, right) := by
      apply Finset.sum_congr rfl
      intro basis _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma vector_weight (count width : Nat)
    (values : Fin count → (CShape.bits width).Value)
    (weight : (CShape.fixedVector count (.bits width)).Value → ℂ) :
    weight (.fixedVector values) =
      ∑ samples : List.Vector (Fin width → Bool) count,
        weight (.fixedVector fun index => .bits (samples.get index)) *
          ∏ index, if values index = .bits (samples.get index) then (1 : ℂ) else 0 := by
  let actual : List.Vector (Fin width → Bool) count :=
    List.Vector.ofFn fun index bit => ((values index).bitGet bit).toBool
  have represented : ∀ index, values index = .bits (actual.get index) := by
    intro index
    simp only [actual, List.Vector.get_ofFn]
    cases values index
    rfl
  have indicator (samples : List.Vector (Fin width → Bool) count) :
      (∏ index, if values index = .bits (samples.get index) then (1 : ℂ) else 0) =
        if samples = actual then 1 else 0 := by
    by_cases same : samples = actual
    · subst samples
      simp only [represented, if_true, Finset.prod_const_one]
    · rw [if_neg same]
      have different : ∃ index, values index ≠ .bits (samples.get index) := by
        by_contra none
        push Not at none
        apply same
        apply List.Vector.ext
        intro index
        exact CShape.Value.bits.inj ((none index).symm.trans (represented index))
      obtain ⟨index, different⟩ := different
      exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg different)
  simp_rw [indicator]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg weight (congrArg CShape.Value.fixedVector (funext represented))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Joint structural read of the actual source, parameter and sixteen slots. -/
def sourceRead : CInputRef (context base noQuantum N) (resultShape N) :=
  .product (.storage (sourceRef base noQuantum N).toCStorageRef)
    (.product (.storage (parameterRef base noQuantum N).toCStorageRef)
      (.fixedVector fun index => .storage (terminalRef base noQuantum N index).toCStorageRef))

private lemma source_read_weight (store : Store (context base noQuantum N))
    (weight : (resultShape N).Value → ℂ) :
    weight (store.read (sourceRead base noQuantum N)) =
      ∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
        weight (.product (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
          (.product (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
            (.fixedVector fun index => .bits (samples.get index)))) *
          terminalIndicator base noQuantum N 16 id samples.get store :=
  vector_weight 16 (measurementBits N)
    (fun index => store.read (.storage (terminalRef base noQuantum N index).toCStorageRef))
    (fun outcomes => weight
      (.product (store.read (.storage (sourceRef base noQuantum N).toCStorageRef))
        (.product (store.read (.storage (parameterRef base noQuantum N).toCStorageRef)) outcomes)))

private lemma sourceDistribution_weighted (input : Input N)
    (weight : (resultShape N).Value → ℂ) :
    (∑ output : (resultShape N).Value,
      ((sourceDistribution input output).toReal : ℂ) * weight output) =
      ∑ source : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          ∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
            ((PMF.independentReplicateVector
              (selectedOutcomePMF (parameterValue input source)) 16 samples).toReal : ℂ) *
              weight (sourceValue input source samples) := by
  unfold sourceDistribution
  rw [PMF.sum_bind_toReal_mul]
  apply Finset.sum_congr rfl
  intro source _
  rw [PMF.sum_map_toReal_mul, PMF.uniformOfFintype_apply, Fintype.card_fin,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv]

private lemma source_moment (input : Input N)
    (weight : (resultShape N).Value → ℂ) :
    (∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
      ∑ source : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          (weight (sourceValue input source samples) *
            ∏ index : Fin 16,
              ((selectedOutcomePMF (parameterValue input source)
                (samples.get index)).toReal : ℂ))) =
      ∑ output : (resultShape N).Value,
        ((sourceDistribution input output).toReal : ℂ) * weight output := by
  rw [Finset.sum_comm, sourceDistribution_weighted N input weight]
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.mul_sum]
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  apply Finset.sum_congr rfl
  intro samples _
  rw [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]
  exact mul_comm _ _

private lemma weighted_from_samples {origin : RuntimeCtx .quantum}
    {Reference : Register} {History FinalHistory : Type}
    [Fintype History] [Fintype FinalHistory]
    (initial : State origin Reference History)
    (final : State (context base noQuantum N) Reference FinalHistory)
    (weight : (resultShape N).Value → ℂ)
    (left right : Reference.Index)
    (sampled : ∀ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
      ExecutionState.referenceFiberSum final
        (fun entry _ => weight
          (.product (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef))
            (.product (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
              (.fixedVector fun index => .bits (samples.get index)))) *
            terminalIndicator base noQuantum N 16 id samples.get entry.1) left right =
        ExecutionState.referenceFiberSum initial
          (fun _ _ => ∑ source : Fin (2 ^ residueSamplingBits N),
            (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
              (weight (sourceValue input source samples) *
                ∏ index : Fin 16,
                  ((selectedOutcomePMF (parameterValue input source)
                    (samples.get index)).toReal : ℂ))) left right) :
    ExecutionState.referenceFiberSum final
        (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum initial
        (fun _ _ => ∑ output : (resultShape N).Value,
          ((sourceDistribution input output).toReal : ℂ) * weight output)
        left right := by
  have expanded := congrArg
    (fun observe : (Store (context base noQuantum N) × FinalHistory) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum final observe left right)
    (funext fun entry => funext fun _ => source_read_weight base noQuantum N entry.1 weight)
  refine expanded.trans ((reference_sum final _ left right).trans ?_)
  refine (Finset.sum_congr rfl (fun samples _ => sampled samples)).trans ?_
  refine (reference_sum initial _ left right).symm.trans ?_
  exact congrArg (fun scalar : ℂ =>
    ExecutionState.referenceFiberSum initial (fun _ _ => scalar) left right)
      (source_moment N input weight)

/-- The actual first declared batch has the complete canonical joint source
distribution, with arbitrary input-store and external-reference weights. -/
lemma source_weighted_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (weight : (resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute (sourceEnvironment input)
      Reference state)
      (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ output : (resultShape N).Value,
        ((sourceDistribution input output).toReal : ℂ) * weight output)
      left right := by
  apply weighted_from_samples base noQuantum N input state _
    weight left right
  intro samples
  have actual := code_joint_reference base noQuantum N input state
    (fun parameter source => weight
      (.product source (.product parameter
        (.fixedVector fun index => .bits (samples.get index)))))
    samples.get left right
  simpa only [Declared.sourceWeight_eq_selected, sourceValue] using actual

attribute [local irreducible] callerInput

/-- The first physical batch retains an original caller value jointly with
its source, parameter and sixteen outcomes in every reference matrix entry. -/
lemma source_caller_weighted_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (weight : shape.Value → (resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N).execute (sourceEnvironment input)
      Reference state)
      (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (resultShape N).Value,
          ((sourceDistribution input output).toReal : ℂ) *
            weight (entry.1.read observed) output) left right := by
  let final := (code base noQuantum N).execute (sourceEnvironment input) Reference state
  let oldRead := callerInput base noQuantum N observed
  let sourceRefRead : CInputRef (context base noQuantum N)
      (.bits (residueSamplingBits N)) :=
    .storage (sourceRef base noQuantum N).toCStorageRef
  let jointOld : CInputRef (context base noQuantum N)
      (.product shape (.bits (residueSamplingBits N))) :=
    .product oldRead sourceRefRead
  have measuredFree : ∀ position,
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        jointOld.storageKeys := by
    intro position member
    exact (List.mem_append.mp member).elim
      (caller_measured_separated base noQuantum N observed position)
      (source_measured_separate base noQuantum N position)
  have workingFree :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        jointOld.storageKeys := by
    intro member
    exact (List.mem_append.mp member).elim
      (caller_working_separated base noQuantum N observed)
      (source_working_separate base noQuantum N)
  have slotFree : ∀ index,
      (terminalRef base noQuantum N index).key ∉ jointOld.storageKeys := by
    intro index member
    exact (List.mem_append.mp member).elim
      (caller_slot_separated base noQuantum N observed index)
      (fun present => terminal_source_ne base noQuantum N index
        (List.mem_singleton.mp present))
  have expanded := congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model N).HiddenState × (History × (code base noQuantum N).Path))) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum final observe left right)
    (funext fun entry => funext fun _ =>
      source_read_weight base noQuantum N entry.1
        (weight (entry.1.read oldRead)))
  refine expanded.trans ((reference_sum final _ left right).trans ?_)
  have sampleLaws := Finset.sum_congr rfl
    (fun (samples : List.Vector (Fin (measurementBits N) → Bool) 16)
      (_ : samples ∈ Finset.univ) => by
      let sampleWeight := fun parameter : (ParameterShape N).Value =>
        fun old : (CShape.product shape (.bits (residueSamplingBits N))).Value =>
          weight old.first (.product old.second
            (.product parameter (.fixedVector fun index => .bits (samples.get index))))
      let setupWeight := fun old parameter source =>
        weight old (.product source
          (.product parameter (.fixedVector fun index => .bits (samples.get index)))) *
          ∏ index : Fin 16,
            Declared.sourceWeight N input parameter (samples.get index)
      have conditional := firstTerminals_frame_reference base noQuantum N input
        jointOld measuredFree workingFree slotFree
        ((setup base noQuantum N).execute (sourceEnvironment input) Reference state)
        (setup_seeded base noQuantum N input state)
        sampleWeight samples.get left right
      have drawn := setup_input_reference base noQuantum N input observed state
        setupWeight left right
      exact (Circuit.referenceFiberSum_execute_seq (environment := sourceEnvironment input)
        (setup base noQuantum N) (firstBatch base noQuantum N)
        state (fun store => sampleWeight
          (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
          (store.read jointOld) *
            terminalIndicator base noQuantum N 16 id samples.get store)
        left right).trans (conditional.trans drawn))
  refine sampleLaws.trans ((reference_sum state _ left right).symm.trans ?_)
  apply congrArg
    (fun observe : (Store base × ((model N).HiddenState × History)) →
        base.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  simpa only [Declared.sourceWeight_eq_selected, sourceValue] using
    (source_moment N input (weight (entry.1.read observed)))

/-- Every later redraw and sixteen paid resets restore that same complete
source distribution on an arbitrary live bank and reference state. -/
lemma next_source_weighted_reference
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : (resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ∑ output : (resultShape N).Value,
        ((sourceDistribution input output).toReal : ℂ) * weight output)
      left right := by
  apply weighted_from_samples base noQuantum N input state _
    weight left right
  intro samples
  have actual := nextBatch_joint_reference base noQuantum N input state
    (fun parameter source => weight
      (.product source (.product parameter
        (.fixedVector fun index => .bits (samples.get index)))))
    samples.get left right
  simpa only [Declared.sourceWeight_eq_selected, sourceValue] using actual

/-- Every later paid batch redraws one new source and all sixteen samples,
while retaining an original caller value in every reference matrix entry. -/
lemma next_source_caller_weighted_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : shape.Value → (resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (resultShape N).Value,
          ((sourceDistribution input output).toReal : ℂ) *
            weight (entry.1.read (callerInput base noQuantum N observed)) output)
        left right := by
  let final := (nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state
  let oldRead := callerInput base noQuantum N observed
  have expanded := congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model N).HiddenState × (History × (nextBatch base noQuantum N).Path))) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum final observe left right)
    (funext fun entry => funext fun _ =>
      source_read_weight base noQuantum N entry.1
        (weight (entry.1.read oldRead)))
  refine expanded.trans ((reference_sum final _ left right).trans ?_)
  have sampleLaws := Finset.sum_congr rfl
    (fun (samples : List.Vector (Fin (measurementBits N) → Bool) 16)
      (_ : samples ∈ Finset.univ) => by
      have actual := nextBatch_caller_joint_reference base noQuantum N input
        observed state
        (fun old parameter source => weight old
          (.product source (.product parameter
            (.fixedVector fun index => .bits (samples.get index)))))
        samples.get left right
      simpa only [Declared.sourceWeight_eq_selected, sourceValue] using actual)
  refine sampleLaws.trans ((reference_sum state _ left right).symm.trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) ×
        ((model N).HiddenState × History)) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact source_moment N input (weight (entry.1.read oldRead))

/-- The first declared batch's real structural read has the exact canonical
joint distribution of source, parameter and sixteen samples. -/
lemma source_toPMF
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model N).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((((code base noQuantum N).execute (sourceEnvironment input) Reference state).toPMF
      (((code base noQuantum N).execute_mass (sourceEnvironment input) Reference state).trans
        normalized)).map
        (fun record => record.1.read (sourceRead base noQuantum N))) =
      sourceDistribution input := by
  refine ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((code base noQuantum N).execute (sourceEnvironment input) Reference state) normalized
    (((code base noQuantum N).execute_mass (sourceEnvironment input) Reference state).trans
      normalized)
    (fun record => record.1.read (sourceRead base noQuantum N))
    (sourceDistribution input) ?_
  intro selected left right
  exact (source_weighted_reference base noQuantum N input state
    (fun output => if output = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator (sourceDistribution input) selected))

/-- A later declared batch has the same complete source distribution after
its actual redraw, reset, observation and paid sample-copy sequence. -/
lemma next_source_toPMF
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((((nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state).toPMF
      (((nextBatch base noQuantum N).execute_mass (sourceEnvironment input) Reference
        state).trans normalized)).map
        (fun record => record.1.read (sourceRead base noQuantum N))) =
      sourceDistribution input := by
  refine ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state) normalized
    (((nextBatch base noQuantum N).execute_mass (sourceEnvironment input) Reference
      state).trans normalized)
    (fun record => record.1.read (sourceRead base noQuantum N))
    (sourceDistribution input) ?_
  intro selected left right
  exact (next_source_weighted_reference base noQuantum N input state
    (fun output => if output = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator (sourceDistribution input) selected))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

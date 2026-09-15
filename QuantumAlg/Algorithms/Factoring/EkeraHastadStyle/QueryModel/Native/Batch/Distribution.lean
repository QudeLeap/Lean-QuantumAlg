/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Distribution.Weights
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# The original source law in the actual fixed-bank storage

The structural read observes the existing source, complete parameter and
sixteen chronological sample cells. It allocates no result and executes no
additional instruction. Summing the proved actual sample indicators gives
every finite weight of this joint read, with both reference coordinates
preserved. The original source distribution follows by tracing those same
matrix entries, for both the first batch and subsequent paid bank reuse.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] context code nextBatch

private theorem reference_sum {C Index : Type} [Fintype C] [Fintype Index]
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

private theorem vector_weight (count width : Nat)
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

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- A joint structural read of the existing source, parameter and chronological sample slots. -/
def sourceRead : CInputRef (context base noQuantum N) (NativeBatch.resultShape N) :=
  .product (.storage (sourceRef base noQuantum N).toCStorageRef)
    (.product (.storage (parameterRef base noQuantum N).toCStorageRef)
      (.fixedVector fun index => .storage (terminalRef base noQuantum N index).toCStorageRef))

private theorem source_read_weight (store : Store (context base noQuantum N))
    (weight : (NativeBatch.resultShape N).Value → ℂ) :
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

private theorem source_moment (input : Input N)
    (weight : (NativeBatch.resultShape N).Value → ℂ) :
    (∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
      ∑ source : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          (weight (NativeBatch.sourceValue input source samples) *
            ∏ index : Fin 16,
              ((selectedOutcomePMF (parameterValue input source)
                (samples.get index)).toReal : ℂ))) =
      ∑ output : (NativeBatch.resultShape N).Value,
        ((NativeBatch.sourceDistribution input output).toReal : ℂ) * weight output := by
  rw [Finset.sum_comm, NativeBatch.nativeBatch_sourceDistribution_weighted]
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.mul_sum]
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  unfold NativeBatch.conditionalMoment
  apply Finset.sum_congr rfl
  intro samples _
  rw [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]
  exact mul_comm _ _

private theorem weighted_from_samples {origin : RuntimeCtx .quantum}
    {Reference : Register} {History FinalHistory : Type}
    [Fintype History] [Fintype FinalHistory]
    (initial : State origin Reference History)
    (final : State (context base noQuantum N) Reference FinalHistory)
    (input : Input N) (weight : (NativeBatch.resultShape N).Value → ℂ)
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
              (weight (NativeBatch.sourceValue input source samples) *
                ∏ index : Fin 16,
                  ((selectedOutcomePMF (parameterValue input source)
                    (samples.get index)).toReal : ℂ))) left right) :
    ExecutionState.referenceFiberSum final
        (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum initial
        (fun _ _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) * weight output)
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

/-- Every weight of the first batch's actual joint read has the original complete source law. -/
theorem nativeOracle_batch_source_weighted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : (NativeBatch.resultShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((code base noQuantum N input).execute Reference state)
        (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) * weight output)
        left right := by
  apply weighted_from_samples base noQuantum N state _ input weight left right
  intro samples
  exact nativeOracle_batch_code_reference base noQuantum N input state
    (fun parameter source => weight
      (.product source (.product parameter (.fixedVector fun index => .bits (samples.get index)))))
    samples.get left right

/-- Redraw and paid reuse have the same complete source law on arbitrary existing storage. -/
theorem nativeOracle_batch_next_source_weighted_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (NativeBatch.resultShape N).Value → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((nextBatch base noQuantum N input).execute Reference state)
        (fun entry _ => weight (entry.1.read (sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ output : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input output).toReal : ℂ) * weight output)
        left right := by
  apply weighted_from_samples base noQuantum N state _ input weight left right
  intro samples
  exact nativeOracle_batch_next_reference base noQuantum N input state
    (fun parameter source => weight
      (.product source (.product parameter (.fixedVector fun index => .bits (samples.get index)))))
    samples.get left right

/-- The actual first batch's structural read has the original complete source distribution. -/
theorem nativeOracle_batch_source_toPMF (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (normalized : state.IsNormalized) :
    ((((code base noQuantum N input).execute Reference state).toPMF
      (((code base noQuantum N input).execute_mass Reference state).trans normalized)).map
        (fun record => record.1.read (sourceRead base noQuantum N))) =
      NativeBatch.sourceDistribution input := by
  refine ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((code base noQuantum N input).execute Reference state) normalized
    (((code base noQuantum N input).execute_mass Reference state).trans normalized)
    (fun record => record.1.read (sourceRead base noQuantum N))
    (NativeBatch.sourceDistribution input) ?_
  intro selected left right
  exact (nativeOracle_batch_source_weighted_reference base noQuantum N input state
    (fun output => if output = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator (NativeBatch.sourceDistribution input) selected))

/-- A later actual batch has the same joint distribution without assumptions on old cells. -/
theorem nativeOracle_batch_next_source_toPMF (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (normalized : state.IsNormalized) :
    ((((nextBatch base noQuantum N input).execute Reference state).toPMF
      (((nextBatch base noQuantum N input).execute_mass Reference state).trans normalized)).map
        (fun record => record.1.read (sourceRead base noQuantum N))) =
      NativeBatch.sourceDistribution input := by
  refine ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((nextBatch base noQuantum N input).execute Reference state) normalized
    (((nextBatch base noQuantum N input).execute_mass Reference state).trans normalized)
    (fun record => record.1.read (sourceRead base noQuantum N))
    (NativeBatch.sourceDistribution input) ?_
  intro selected left right
  exact (nativeOracle_batch_next_source_weighted_reference base noQuantum N input state
    (fun output => if output = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum state (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator (NativeBatch.sourceDistribution input) selected))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

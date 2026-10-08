/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Joint.Input
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Reuse
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Completion

/-!
# Actual declared source tuples carry their complete original parameter

The actual joint Born law identifies the entire stored sample, full parameter
and measured phase with the original source encoding. Supported execution
records therefore supply their own recovery-input consistency; callers do not
provide a separate source distribution or agreement certificate.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

local instance {N : Nat} : Fintype (SourceOutcome N) :=
  Fintype.ofEquiv (Fin (2 ^ residueSamplingBits N) × TerminalZMeasure.Outcome (phaseBits N))
    (SourceWeights.outcomeEquiv N)

/-- The source tuple's transparent closed shape is independent of the candidate code. -/
abbrev sourceTupleShape (N : Nat) : CShape :=
  .product (.bits (residueSamplingBits N))
    (.product (ParameterShape (modulusBits N)) (.bits (phaseBits N)))

/-- The complete result uses the same original sampled bits, parameter and phase. -/
def sourceValue {N : Nat} (input : Input N) (outcome : SourceOutcome N) :
    (sourceTupleShape N).Value :=
  .product (.bits (Sampler.PackedSample.storedBits outcome.sample))
    (.product (parameterValue input outcome.sample) (.bits outcome.measurement))

/-- Read precisely the three actual retained operands passed to native recovery. -/
def tupleInput (ctx : RuntimeCtx .quantum) (N : Nat) :
    CInputRef (Iteration.context ctx N) (sourceTupleShape N) :=
  .product (Iteration.sampleInput ctx N)
    (.product (Iteration.parameterInput ctx N) (Iteration.phaseInput ctx N))

private theorem sourceValue_phase_weight {N : Nat} (input : Input N)
    (bits : Fin (residueSamplingBits N) → Bool)
    (parameter : (ParameterShape (modulusBits N)).Value) (phase : Fin (phaseBits N) → Bool) :
    (∑ sample : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        ((if (.product (.bits (Sampler.PackedSample.storedBits sample))
          (.product (parameterValue input sample) (.bits phase)) :
            (sourceTupleShape N).Value) = .product (.bits bits) (.product parameter (.bits
              phase))
            then 1 else 0) * ((sourceSampleOutcomePMF input sample phase).toReal : ℂ))) =
      (((sourceOutcomePMF input).map (sourceValue input)
        (.product (.bits bits) (.product parameter (.bits phase)))).toReal : ℂ) := by
  classical
  have original := (SourceWeights.one_eq input
    (fun outcome => if sourceValue input outcome =
      .product (.bits bits) (.product parameter (.bits phase)) then 1 else 0)).trans
        (PMF.sum_toReal_map_indicator (sourceOutcomePMF input) (sourceValue input)
          (.product (.bits bits) (.product parameter (.bits phase))))
  refine Eq.trans ?_ original
  unfold SourceWeights.one sourceValue
  apply Finset.sum_congr rfl
  intro sample _
  apply congrArg (fun value : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * value)
  by_cases matching : Sampler.PackedSample.storedBits sample = bits ∧
      parameterValue input sample = parameter
  · simp only [CShape.Value.product.injEq, CShape.Value.bits.injEq, matching.1, matching.2,
      true_and, if_true, one_mul, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [CShape.Value.product.injEq, CShape.Value.bits.injEq, ← and_assoc,
      matching, false_and, if_false, zero_mul, Finset.sum_const_zero]

/-- The full actual tuple has the original encoded point weight, with every reference entry. -/
theorem iteration_tuple_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    {shape : CShape} (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (value : (sourceTupleShape N).Value) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code ctx N input sameWires).execute Reference state)
      (fun entry _ => if entry.1.read (tupleInput ctx N) = value then 1 else 0)
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => (((sourceOutcomePMF input).map (sourceValue input) value).toReal : ℂ))
        leftRef rightRef := by
  cases value with
  | product sampled rest =>
    cases sampled with
    | bits bits =>
      cases rest with
      | product parameter measured =>
        cases measured with
        | bits phase =>
          let weight := fun value : (CShape.product shape
              (.product (ParameterShape (modulusBits N)) (.bits (residueSamplingBits N)))).Value =>
            if (.product value.second.second (.product value.second.first (.bits phase)) :
                (sourceTupleShape N).Value) = .product (.bits bits) (.product parameter (.bits
                  phase))
              then (1 : ℂ) else 0
          have actual := iteration_outcome_reference_input ctx N input sameWires observed
            state seeded weight phase leftRef rightRef
          have coefficient := sourceValue_phase_weight input bits parameter phase
          have sampled :
              ExecutionState.referenceFiberSum state
                (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
                  (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
                    (weight (.product (entry.1.read observed) (.product (parameterValue input
                      sample)
                      (.bits (Sampler.PackedSample.storedBits sample)))) *
                        ((sourceSampleOutcomePMF input sample phase).toReal : ℂ)))
                leftRef rightRef =
              ExecutionState.referenceFiberSum state
                (fun _ _ => (((sourceOutcomePMF input).map (sourceValue input)
                  (.product (.bits bits) (.product parameter (.bits phase)))).toReal : ℂ))
                leftRef rightRef := by
            apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe leftRef
              rightRef)
            funext entry basis
            exact coefficient
          refine Eq.trans ?_ (actual.trans sampled)
          apply congrArg (fun observe => ExecutionState.referenceFiberSum
            ((Iteration.code ctx N input sameWires).execute Reference state) observe leftRef
              rightRef)
          funext entry basis
          change
            (if (.product (entry.1.read (Iteration.sampleInput ctx N))
              (.product (entry.1.read (Iteration.parameterInput ctx N))
                (entry.1.read (Iteration.phaseInput ctx N))) : (sourceTupleShape N).Value) =
                  .product (.bits bits) (.product parameter (.bits phase)) then (1 : ℂ) else 0) =
              (if (.product (entry.1.read (Iteration.sampleInput ctx N))
                (.product (entry.1.read (Iteration.parameterInput ctx N)) (.bits phase)) :
                  (sourceTupleShape N).Value) =
                    .product (.bits bits) (.product parameter (.bits phase)) then 1 else 0) *
              (if entry.1.read (Iteration.phaseInput ctx N) = .bits phase then 1 else 0)
          cases measuredRead : entry.1.read (Iteration.phaseInput ctx N) with
          | bits chosen =>
            by_cases selectedPhase : chosen = phase
            · subst chosen
              simp only [if_true, mul_one]
            · simp only [CShape.Value.product.injEq, CShape.Value.bits.injEq, selectedPhase,
                and_false, if_false, mul_zero]

/-- The PMF is extracted from the same actual trace and full stored tuple. -/
theorem iteration_tuple_toPMF (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    {shape : CShape} (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized) :
    (((Iteration.code ctx N input sameWires).execute Reference state).toPMF
      (((Iteration.code ctx N input sameWires).execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read (tupleInput ctx N)) =
          (sourceOutcomePMF input).map (sourceValue input) := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((Iteration.code ctx N input sameWires).execute Reference state) normalized
    (((Iteration.code ctx N input sameWires).execute_mass Reference state).trans normalized)
  intro value leftRef rightRef
  exact iteration_tuple_reference ctx N input sameWires observed state seeded value leftRef rightRef

/-- Every supported actual record internally supplies one complete original source tuple. -/
theorem iteration_supported_source (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    {shape : CShape} (observed : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (record : Store (Iteration.context ctx N) ×
      ((executionModel input).HiddenState × (History × (Iteration.code ctx N input
        sameWires).Path)))
    (supported : record ∈
      (((Iteration.code ctx N input sameWires).execute Reference state).toPMF
        (((Iteration.code ctx N input sameWires).execute_mass Reference state).trans
          normalized)).support) :
    ∃ outcome : SourceOutcome N, record.1.read (tupleInput ctx N) = sourceValue input outcome := by
  have actual : record.1.read (tupleInput ctx N) ∈
      ((((Iteration.code ctx N input sameWires).execute Reference state).toPMF
        (((Iteration.code ctx N input sameWires).execute_mass Reference state).trans
          normalized)).map
          (fun entry => entry.1.read (tupleInput ctx N))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨record, supported, rfl⟩
  rw [iteration_tuple_toPMF ctx N input sameWires observed state seeded normalized] at actual
  obtain ⟨outcome, _positive, encoded⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
  exact ⟨outcome, encoded.symm⟩

/-- Supported actual sampling supplies the original recovery inputs without a caller certificate. -/
theorem iteration_supported_feedback (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (original : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated (Completion.cells ctx N original)
      (Completion.liftWrite ctx N result))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (record : Store (Iteration.context ctx N) ×
      ((executionModel input).HiddenState × (History × (Iteration.code ctx N input
        sameWires).Path)))
    (supported : record ∈
      (((Iteration.code ctx N input sameWires).execute Reference state).toPMF
        (((Iteration.code ctx N input sameWires).execute_mass Reference state).trans
          normalized)).support) :
    ∃ outcome : SourceOutcome N,
      record.1.read (tupleInput ctx N) = sourceValue input outcome ∧
      NativeFactorScan.latchValue (Completion.cells ctx N original)
        (Completion.feedbackStep ctx N input original result record.1).1 =
          NativeFactorScan.firstPresent
            (NativeFactorScan.latchValue (Completion.cells ctx N original) record.1)
            (NativeFactorScan.sourceResult input outcome) := by
  obtain ⟨outcome, encoded⟩ := iteration_supported_source ctx N input sameWires
    (.storage original.accepted.toCStorageRef) state seeded normalized record supported
  have parameterRead := congrArg (fun value => value.second.first) encoded
  have phaseRead := congrArg (fun value => value.second.second) encoded
  change record.1.read (Iteration.parameterInput ctx N) = parameterValue input outcome.sample
    at parameterRead
  change record.1.read (Iteration.phaseInput ctx N) = .bits outcome.measurement at phaseRead
  exact ⟨outcome, encoded, Completion.feedback_latches ctx N input original result
    separated record.1 outcome parameterRead phaseRead⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

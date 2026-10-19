/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Completion

/-!
# The original joint source law at the real next-round input

The complete preceding sampling, native recovery, first-success feedback and
physical reset supply the fixed zero bank. Its entire live store, hidden
state, path and arbitrary reference enter the next actual iteration. No new
input state or service initialization is supplied at this boundary.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

local instance {N : Nat} : Fintype (SourceOutcome N) :=
  Fintype.ofEquiv (Fin (2 ^ residueSamplingBits N) × TerminalZMeasure.Outcome (phaseBits N))
    (SourceWeights.outcomeEquiv N)

/-- The complete actual program has the original joint point weights. -/
lemma iteration_source_reference (ctx : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : ctx.quantumWires = (layout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (outcome : SourceOutcome N) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code ctx N sameWires).execute (environment input) Reference state)
      (fun entry _ => if sourceRead ctx N entry.1 = outcome
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ((sourceOutcomePMF input outcome).toReal : ℂ)) leftRef rightRef := by
  cases outcome with
  | mk sample phase =>
    have actual := iteration_outcome_reference ctx N input sameWires state seeded
      (fun value => if sampleRead value = sample then 1 else 0) phase leftRef rightRef
    have coefficient :
        (∑ chosen : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            ((if sampleRead (.bits (Sampler.PackedSample.storedBits chosen)) = sample
              then 1 else 0) * ((sourceSampleOutcomePMF input chosen phase).toReal : ℂ))) =
          ((sourceOutcomePMF input ⟨sample, phase⟩).toReal : ℂ) := by
      simp only [sampleRead_stored]
      exact original_pair_weight input sample phase
    rw [coefficient] at actual
    refine Eq.trans ?_ actual
    apply congrArg (fun observe => ExecutionState.referenceFiberSum
      ((Iteration.code ctx N sameWires).execute (environment input) Reference state)
      observe leftRef rightRef)
    funext entry basis
    exact sourceRead_indicator ctx N entry.1 sample phase

/-- The actual trace-derived source output PMF equals the original joint distribution. -/
lemma iteration_source_toPMF (ctx : RuntimeCtx .quantum)
    (N : Nat) (input : Input N) (sameWires : ctx.quantumWires = (layout N).wires)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized) :
    (((Iteration.code ctx N sameWires).execute (environment input) Reference state).toPMF
      (((Iteration.code ctx N sameWires).execute_mass
        (environment input) Reference state).trans normalized)).map
        (fun entry => sourceRead ctx N entry.1) =
          sourceOutcomePMF input := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((Iteration.code ctx N sameWires).execute (environment input) Reference state) normalized
    (((Iteration.code ctx N sameWires).execute_mass
      (environment input) Reference state).trans normalized)
  intro outcome leftRef rightRef
  exact iteration_source_reference ctx N input sameWires state seeded outcome leftRef rightRef


/-- The real first completed round supplies the entire state used by the next source sample. -/
lemma completion_next_source_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (outcome : SourceOutcome N) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code (Iteration.context ctx N) N
        ((Iteration.quantumWires ctx N).trans sameWires)).execute (environment input) Reference
          ((Completion.code ctx N input sameWires cells result).execute
            (environment input) Reference state))
      (fun entry _ => if sourceRead (Iteration.context ctx N) N entry.1 = outcome then 1 else 0)
      leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((Completion.code ctx N input sameWires cells result).execute
          (environment input) Reference state)
        (fun _ _ => ((sourceOutcomePMF input outcome).toReal : ℂ)) leftRef rightRef :=
  iteration_source_reference (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans sameWires)
    ((Completion.code ctx N input sameWires cells result).execute
      (environment input) Reference state)
    (Completion.code_seeded
      (environment := environment input) ctx N input sameWires cells result state)
    outcome leftRef rightRef

/-- Two actual complete rounds retain one unchanged physical bank and finish in fixed zero. -/
lemma completion_two_rounds_seeded (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History)) :
    BasisSeeded.Holds (Iteration.context (Iteration.context ctx N) N).quantumLayout.zeroLabel
      (((Completion.code ctx N input sameWires cells result).seq
        (Completion.code (Iteration.context ctx N) N input
          ((Iteration.quantumWires ctx N).trans sameWires)
          (Completion.cells ctx N cells) (Completion.liftWrite ctx N result))).execute
            (environment input) Reference state) :=
  BasisSeeded.seq
    (environment := environment input) (Completion.code ctx N input sameWires cells result)
    (Completion.code (Iteration.context ctx N) N input
      ((Iteration.quantumWires ctx N).trans sameWires)
      (Completion.cells ctx N cells) (Completion.liftWrite ctx N result)) _ state
    (Completion.code_seeded (environment := environment input) (Iteration.context ctx N) N input
      ((Iteration.quantumWires ctx N).trans sameWires)
      (Completion.cells ctx N cells) (Completion.liftWrite ctx N result)
      ((Completion.code ctx N input sameWires cells result).execute
        (environment input) Reference state))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

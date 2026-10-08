/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Reset
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Complete actual Shor sampling, recovery, first-success feedback and reset

The stored original parameter and measured phase feed the existing native
factor-recovery visit. Its actual selector preserves an earlier success.
Only after this feedback does the same physical bank reset to zero. The
complete round reads its real accepted bit and selected word; the optional
output is materialized by the final paid pack of the whole finite run.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Completion

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- Preserve an actual writable cell beneath precisely this iteration's allocations. -/
def liftWrite {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (Iteration.context ctx N) shape :=
  let sampled := output.underRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh
  let parameter := sampled.underRetained (Sampler.Retained.sampleContext ctx N).canonicalFreshKey
    (ParameterShape (modulusBits N)) (Sampler.Retained.sampleContext ctx N).canonicalFreshKey_fresh
  MeasurementCells.liftWrite 2
    (parameter.underRetained (Iteration.sampledContext ctx N).canonicalFreshKey
      (.bits (phaseBits N)) (Iteration.sampledContext ctx N).canonicalFreshKey_fresh) (phaseBits N)

/-- The lifted original writable cell keeps its actual storage identity. -/
theorem liftWrite_key {shape : CShape} (output : CWriteRef ctx shape) :
    (liftWrite ctx N output).key = output.key := by
  unfold liftWrite
  rw [MeasurementCells.liftWrite_key]
  rfl

/-- The real persistent selector cells survive all new source-result allocations. -/
def cells (original : NativeFactorScan.Cells ctx N) :
    NativeFactorScan.Cells (Iteration.context ctx N) N where
  candidate := liftWrite ctx N original.candidate
  accepted := liftWrite ctx N original.accepted
  selected := liftWrite ctx N original.selected
  scratch := liftWrite ctx N original.scratch

/-- Recovery consumes precisely the complete parameter and phase written by this iteration. -/
def inputs : NativeFactorScan.Inputs (Iteration.context ctx N) N where
  parameter := Iteration.parameterInput ctx N
  phase := Iteration.phaseInput ctx N

variable (input : Input N) (sameWires : ctx.quantumWires = (layout N).wires)
  (original : NativeFactorScan.Cells ctx N)
  (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))

/-- The original native recovery and selector execute on those same actual operands. -/
def feedback : Circuit (executionModel input) (Iteration.context ctx N) (Iteration.context ctx N) :=
  NativeFactorScan.visit (model := executionModel input) input (inputs ctx N)
    (cells ctx N original) (liftWrite ctx N result)

/-- The complete chronological body includes its paid recovery, feedback and final reset. -/
def code : Circuit (executionModel input) ctx (Iteration.context ctx N) :=
  (Iteration.code ctx N input sameWires).seq
    ((feedback ctx N input original result).seq
      (reset (Iteration.context ctx N) N input ((Iteration.quantumWires ctx N).trans sameWires)))

/-- Observe the true persistent latches while retaining every live caller and source result. -/
def run : AlgorithmRun (executionModel input) ctx (Iteration.context ctx N)
    (.product .bit (.unsignedWord (modulusBits N))) where
  code := code ctx N input sameWires original result
  output := Output.all (Iteration.context ctx N)
    (.read (.product (.storage (cells ctx N original).accepted.toCStorageRef)
      (.storage (cells ctx N original).selected.toCStorageRef)))

/-- The completed round exposes the entire actual final manifest. -/
theorem output_listing :
    (run ctx N input sameWires original result).output.listing =
      (Iteration.context ctx N).keys := rfl

/-- Real recovery and feedback retain their complete store, hidden state, history and path. -/
def feedbackStep (store : Store (Iteration.context ctx N)) :
    Store (Iteration.context ctx N) × (feedback ctx N input original result).Path :=
  NativeFactorScan.visitStep (model := executionModel input) input
    (inputs ctx N) (cells ctx N original) (liftWrite ctx N result) store

/-- The actual feedback retains its own typed path without expanding the internal recovery path. -/
theorem feedback_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (Iteration.context ctx N) Reference
      ((executionModel input).HiddenState × History)) :
    (feedback ctx N input original result).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := feedbackStep ctx N input original result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  NativeFactorScan.visit_execute (model := executionModel input) (ctx := Iteration.context ctx N)
    input (inputs ctx N) (cells ctx N original)
    (liftWrite ctx N result) Reference state

private theorem record_reference {model : ExecutionModel} {base : RuntimeCtx model.kind}
    (actualCode : Circuit model base base) (step : Store base → Store base × actualCode.Path)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (record : actualCode.execute Reference state = state.mapClassical (fun entry =>
      let chosen := step entry.1
      (chosen.1, (entry.2.1, (entry.2.2, chosen.2)))))
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum (actualCode.execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (step entry.1).1) leftRef rightRef := by
  rw [record]
  exact ExecutionState.referenceFiberSum_mapClassical (decision := inferInstance) state
    (fun entry => let chosen := step entry.1
      (chosen.1, (entry.2.1, (entry.2.2, chosen.2))))
    (fun entry _ => weight entry.1) leftRef rightRef

/-- The same actual recovery visit keeps an earlier success and tests this round's source result. -/
theorem feedback_latches
    (separated : NativeFactorScan.Separated (cells ctx N original) (liftWrite ctx N result))
    (store : Store (Iteration.context ctx N)) (outcome : SourceOutcome N)
    (parameterRead : store.read (Iteration.parameterInput ctx N) =
      parameterValue input outcome.sample)
    (phaseValue : store.read (Iteration.phaseInput ctx N) = .bits outcome.measurement) :
    NativeFactorScan.latchValue (cells ctx N original)
      (NativeFactorScan.visitStep (model := executionModel input) input
        (inputs ctx N) (cells ctx N original) (liftWrite ctx N result) store).1 =
      NativeFactorScan.firstPresent (NativeFactorScan.latchValue (cells ctx N original) store)
        (NativeFactorScan.sourceResult input outcome) :=
  NativeFactorScan.visit_latchValue (model := executionModel input) (ctx := Iteration.context ctx N)
    input (inputs ctx N) (cells ctx N original)
    (liftWrite ctx N result) separated store outcome parameterRead phaseValue

/-- The complete actual sampling/recovery/feedback round supplies its terminal physical zero. -/
theorem code_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History)) :
    BasisSeeded.Holds (Iteration.context ctx N).quantumLayout.zeroLabel
      ((code ctx N input sameWires original result).execute Reference state) := by
  let sample := Iteration.code ctx N input sameWires
  let recovered := feedback ctx N input original result
  let cleaned := reset (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans sameWires)
  exact BasisSeeded.seq sample (recovered.seq cleaned) _ state
    (BasisSeeded.seq recovered cleaned _ (sample.execute Reference state)
      (reset_seeded (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)
        (recovered.execute Reference (sample.execute Reference state))))

/-- Paid terminal reset preserves the entire reference-weighted actual feedback observation. -/
theorem code_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (weight : Store (Iteration.context ctx N) → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code ctx N input sameWires original result).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((Iteration.code ctx N input sameWires).execute Reference state)
        (fun entry _ => weight (feedbackStep ctx N input original result entry.1).1)
        leftRef rightRef := by
  let sample := Iteration.code ctx N input sameWires
  let recovered := feedback ctx N input original result
  let cleaned := reset (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans sameWires)
  let measured := sample.execute Reference state
  have sequence := Circuit.referenceFiberSum_execute_seq sample (recovered.seq cleaned)
    state weight leftRef rightRef
  have suffix := Circuit.referenceFiberSum_execute_seq recovered cleaned measured
    weight leftRef rightRef
  have retained := reset_reference (Iteration.context ctx N) N input
    ((Iteration.quantumWires ctx N).trans sameWires)
    (recovered.execute Reference measured) weight leftRef rightRef
  refine sequence.trans (suffix.trans (retained.trans ?_))
  exact record_reference recovered (feedbackStep ctx N input original result) measured
    (feedback_execute ctx N input original result measured) weight leftRef rightRef

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Completion

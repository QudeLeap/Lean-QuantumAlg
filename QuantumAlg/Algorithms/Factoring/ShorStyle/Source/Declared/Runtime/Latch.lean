/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Joint.Weight
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Supported
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Geometry

/-!
# Complete reference law of the real first-success feedback round

The actual supported sampling records carry their own original source inputs.
Zero-mass records contribute zero complete density blocks. Native recovery and
feedback therefore have the original first-present transition jointly with
the incoming latch and every reference coordinate; physical reset is included.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Read the actual two persistent latch cells as one closed structural input. -/
def latchInput (ctx : RuntimeCtx .quantum) (N : Nat) (cells : NativeFactorScan.Cells ctx N) :
    CInputRef ctx (.product .bit (.unsignedWord (modulusBits N))) :=
  .product (.storage cells.accepted.toCStorageRef) (.storage cells.selected.toCStorageRef)

private def sourceDecode (N : Nat) (value : (sourceTupleShape N).Value) : SourceOutcome N :=
  ⟨sampleRead value.first, phaseRead value.second.second⟩

private lemma sourceDecode_sourceValue {N : Nat} (input : Input N) (outcome : SourceOutcome N) :
    sourceDecode N (sourceValue input outcome) = outcome := by
  cases outcome with
  | mk sample phase =>
      simp only [sourceDecode, sourceValue, CShape.Value.first, CShape.Value.second,
        sampleRead_stored, phaseRead]

/-- An original actual cell read lifts to precisely the completion's genuine destination. -/
lemma completion_liftWrite_input {shape : CShape} (ctx : RuntimeCtx .quantum) (N : Nat)
    (cell : CWriteRef ctx shape) :
    iterationInput ctx N (.storage cell.toCStorageRef) =
      .storage (Completion.liftWrite ctx N cell).toCStorageRef := by
  let sampled := cell.underRetained ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh
  let parameter := sampled.underRetained (Sampler.Retained.sampleContext ctx N).canonicalFreshKey
    (ParameterShape (modulusBits N)) (Sampler.Retained.sampleContext ctx N).canonicalFreshKey_fresh
  let packed := parameter.underRetained (Iteration.sampledContext ctx N).canonicalFreshKey
    (.bits (phaseBits N)) (Iteration.sampledContext ctx N).canonicalFreshKey_fresh
  change MeasurementCells.liftInput 2 (.storage packed.toCStorageRef) (phaseBits N) =
    .storage (MeasurementCells.liftWrite 2 packed (phaseBits N)).toCStorageRef
  exact MeasurementCells.liftInput_storage 2 packed (phaseBits N)

private lemma iterationInput_product {first second : CShape} (ctx : RuntimeCtx .quantum)
    (N : Nat) (left : CInputRef ctx first) (right : CInputRef ctx second) :
    iterationInput ctx N (.product left right) =
      .product (iterationInput ctx N left) (iterationInput ctx N right) := by
  unfold iterationInput
  rw [show Sampler.Retained.liftInput (N := N) (.product left right) =
    .product (Sampler.Retained.liftInput (N := N) left)
      (Sampler.Retained.liftInput (N := N) right) from rfl,
    observation_liftInput_product]

private lemma lifted_latch (ctx : RuntimeCtx .quantum) (N : Nat)
    (cells : NativeFactorScan.Cells ctx N) (store : Store (Iteration.context ctx N)) :
    CShape.packOption (store.read (iterationInput ctx N (latchInput ctx N cells))) =
      NativeFactorScan.latchValue (Completion.cells ctx N cells) store := by
  unfold latchInput
  rw [iterationInput_product, completion_liftWrite_input, completion_liftWrite_input]
  rfl

/-- Full actual complete-round weights follow the original source and first-present feedback. -/
lemma completion_latch_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Completion.code ctx N input sameWires cells result).execute
        (environment input) Reference state)
      (fun entry _ => weight (NativeFactorScan.latchValue (Completion.cells ctx N cells) entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => SourceWeights.one input (fun outcome => weight
        (NativeFactorScan.firstPresent (NativeFactorScan.latchValue cells entry.1)
          (NativeFactorScan.sourceResult input outcome)))) left right := by
  let sampled := (Iteration.code ctx N sameWires).execute (environment input) Reference state
  have actual := Completion.code_reference
    (environment := environment input) ctx N input sameWires cells result state
    (fun store => weight (NativeFactorScan.latchValue (Completion.cells ctx N cells) store))
      left right
  have consistent :
      ExecutionState.referenceFiberSum sampled
        (fun entry _ => weight (NativeFactorScan.latchValue (Completion.cells ctx N cells)
          (Completion.feedbackStep ctx N input cells result entry.1).1)) left right =
        ExecutionState.referenceFiberSum sampled
          (fun entry _ => weight (NativeFactorScan.firstPresent
            (CShape.packOption (entry.1.read (iterationInput ctx N (latchInput ctx N cells))))
              (NativeFactorScan.sourceResult input (sourceRead ctx N entry.1)))) left right := by
    apply ExecutionState.referenceFiberSum_congr_on_positive sampled
    intro record positive basis
    have supported := (ExecutionState.mem_support_toPMF_iff sampled
      (((Iteration.code ctx N sameWires).execute_mass
        (environment input) Reference state).trans normalized)
        record).mpr positive
    obtain ⟨outcome, encoded, feedback⟩ := iteration_supported_feedback ctx N input sameWires
      cells result (Completion.separated ctx N cells result separated) state seeded normalized
        record supported
    have decoded : sourceRead ctx N record.1 = outcome :=
      (congrArg (sourceDecode N) encoded).trans (sourceDecode_sourceValue input outcome)
    rw [feedback, lifted_latch, decoded]
  have source := iteration_input_source_reference ctx N input sameWires (latchInput ctx N cells)
    state seeded (fun value outcome => weight
      (NativeFactorScan.firstPresent (CShape.packOption value)
        (NativeFactorScan.sourceResult input outcome))) left right
  exact actual.trans (consistent.trans source)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scope.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scan.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scan.Preservation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Source
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Projection

/-!
# Complete source readout of the actual scoped residue preparation
The real allocations, literal modulus load, ordered proposal fold, expanded
GCD decision and final product write produce the unchanged RSA parameter.
All scratch initialization and separation obligations are discharged by the
actual layout and scan. The only local sample premise describes the value
already written by the caller's real random-bit instruction.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private lemma cellRead_underWorkspace {shape : CShape} (output : CWriteRef ctx shape)
    (key : StorageKey) (cellShape : CShape) (fresh : key ∉ ctx.keys) :
    (FirstAccepted.cellRead output).underWorkspace key cellShape fresh =
      FirstAccepted.cellRead (output.underWorkspace key cellShape fresh) := rfl

private lemma underRead_cellRead {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) :
    Layout.underRead (FirstAccepted.cellRead output) width =
      FirstAccepted.cellRead (Layout.underWrite output width) := by
  let output1 : CWriteRef (Layout.modulusCtx ctx width) shape :=
    output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let read1 : CInputRef (Layout.modulusCtx ctx width) shape :=
    (FirstAccepted.cellRead output).underWorkspace ctx.canonicalFreshKey
        (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  have agreed1 : read1 = FirstAccepted.cellRead output1 :=
    cellRead_underWorkspace output ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let output2 : CWriteRef (Layout.gcdCtx ctx width) shape :=
    output1.underWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
      (Layout.modulusCtx ctx width).canonicalFreshKey_fresh
  let read2 : CInputRef (Layout.gcdCtx ctx width) shape :=
    (read1).underWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
      (Layout.modulusCtx ctx width).canonicalFreshKey_fresh
  have agreed2 : read2 = FirstAccepted.cellRead output2 :=
    (congrArg (fun reference : CInputRef (Layout.modulusCtx ctx width) shape =>
      reference.underWorkspace (Layout.modulusCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
        (Layout.modulusCtx ctx width).canonicalFreshKey_fresh) agreed1).trans
      (cellRead_underWorkspace output1 (Layout.modulusCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
        (Layout.modulusCtx ctx width).canonicalFreshKey_fresh)
  let output3 : CWriteRef (Layout.candidateCtx ctx width) shape :=
    output2.underWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.gcdCtx ctx width).canonicalFreshKey_fresh
  let read3 : CInputRef (Layout.candidateCtx ctx width) shape :=
    (read2).underWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.gcdCtx ctx width).canonicalFreshKey_fresh
  have agreed3 : read3 = FirstAccepted.cellRead output3 :=
    (congrArg (fun reference : CInputRef (Layout.gcdCtx ctx width) shape =>
      reference.underWorkspace (Layout.gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
        (Layout.gcdCtx ctx width).canonicalFreshKey_fresh) agreed2).trans
      (cellRead_underWorkspace output2 (Layout.gcdCtx ctx width).canonicalFreshKey
        (.unsignedWord width)
        (Layout.gcdCtx ctx width).canonicalFreshKey_fresh)
  let output4 : CWriteRef (Layout.extendedCtx ctx width) shape :=
    output3.underWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
      (Layout.candidateCtx ctx width).canonicalFreshKey_fresh
  let read4 : CInputRef (Layout.extendedCtx ctx width) shape :=
    (read3).underWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
      (Layout.candidateCtx ctx width).canonicalFreshKey_fresh
  have agreed4 : read4 = FirstAccepted.cellRead output4 :=
    (congrArg (fun reference : CInputRef (Layout.candidateCtx ctx width) shape =>
      reference.underWorkspace (Layout.candidateCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
        (Layout.candidateCtx ctx width).canonicalFreshKey_fresh) agreed3).trans
      (cellRead_underWorkspace output3 (Layout.candidateCtx ctx width).canonicalFreshKey
        (.unsignedWord (width + 1))
        (Layout.candidateCtx ctx width).canonicalFreshKey_fresh)
  let output5 : CWriteRef (Layout.positiveCtx ctx width) shape :=
    output4.underWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
      (Layout.extendedCtx ctx width).canonicalFreshKey_fresh
  let read5 : CInputRef (Layout.positiveCtx ctx width) shape :=
    (read4).underWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
      (Layout.extendedCtx ctx width).canonicalFreshKey_fresh
  have agreed5 : read5 = FirstAccepted.cellRead output5 :=
    (congrArg (fun reference : CInputRef (Layout.extendedCtx ctx width) shape =>
      reference.underWorkspace (Layout.extendedCtx ctx width).canonicalFreshKey .bit
        (Layout.extendedCtx ctx width).canonicalFreshKey_fresh) agreed4).trans
      (cellRead_underWorkspace output4 (Layout.extendedCtx ctx width).canonicalFreshKey .bit
        (Layout.extendedCtx ctx width).canonicalFreshKey_fresh)
  let output6 : CWriteRef (Layout.belowCtx ctx width) shape :=
    output5.underWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
      (Layout.positiveCtx ctx width).canonicalFreshKey_fresh
  let read6 : CInputRef (Layout.belowCtx ctx width) shape :=
    (read5).underWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
      (Layout.positiveCtx ctx width).canonicalFreshKey_fresh
  have agreed6 : read6 = FirstAccepted.cellRead output6 :=
    (congrArg (fun reference : CInputRef (Layout.positiveCtx ctx width) shape =>
      reference.underWorkspace (Layout.positiveCtx ctx width).canonicalFreshKey .bit
        (Layout.positiveCtx ctx width).canonicalFreshKey_fresh) agreed5).trans
      (cellRead_underWorkspace output5 (Layout.positiveCtx ctx width).canonicalFreshKey .bit
        (Layout.positiveCtx ctx width).canonicalFreshKey_fresh)
  let output7 : CWriteRef (Layout.eligibleCtx ctx width) shape :=
    output6.underWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
      (Layout.belowCtx ctx width).canonicalFreshKey_fresh
  let read7 : CInputRef (Layout.eligibleCtx ctx width) shape :=
    (read6).underWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
      (Layout.belowCtx ctx width).canonicalFreshKey_fresh
  have agreed7 : read7 = FirstAccepted.cellRead output7 :=
    (congrArg (fun reference : CInputRef (Layout.belowCtx ctx width) shape =>
      reference.underWorkspace (Layout.belowCtx ctx width).canonicalFreshKey .bit
        (Layout.belowCtx ctx width).canonicalFreshKey_fresh) agreed6).trans
      (cellRead_underWorkspace output6 (Layout.belowCtx ctx width).canonicalFreshKey .bit
        (Layout.belowCtx ctx width).canonicalFreshKey_fresh)
  let output8 : CWriteRef (Layout.acceptedCtx ctx width) shape :=
    output7.underWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
      (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh
  let read8 : CInputRef (Layout.acceptedCtx ctx width) shape :=
    (read7).underWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
      (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh
  have agreed8 : read8 = FirstAccepted.cellRead output8 :=
    (congrArg (fun reference : CInputRef (Layout.eligibleCtx ctx width) shape =>
      reference.underWorkspace (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
        (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh) agreed7).trans
      (cellRead_underWorkspace output7 (Layout.eligibleCtx ctx width).canonicalFreshKey .bit
        (Layout.eligibleCtx ctx width).canonicalFreshKey_fresh)
  let output9 : CWriteRef (Layout.selectedCtx ctx width) shape :=
    output8.underWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh
  let read9 : CInputRef (Layout.selectedCtx ctx width) shape :=
    (read8).underWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh
  have agreed9 : read9 = FirstAccepted.cellRead output9 :=
    (congrArg (fun reference : CInputRef (Layout.acceptedCtx ctx width) shape =>
      reference.underWorkspace (Layout.acceptedCtx ctx width).canonicalFreshKey
        (.unsignedWord width)
        (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh) agreed8).trans
      (cellRead_underWorkspace output8 (Layout.acceptedCtx ctx width).canonicalFreshKey
        (.unsignedWord width)
        (Layout.acceptedCtx ctx width).canonicalFreshKey_fresh)
  let output10 : CWriteRef (Layout.availableCtx ctx width) shape :=
    output9.underWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
      (Layout.selectedCtx ctx width).canonicalFreshKey_fresh
  let read10 : CInputRef (Layout.availableCtx ctx width) shape :=
    (read9).underWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
      (Layout.selectedCtx ctx width).canonicalFreshKey_fresh
  have agreed10 : read10 = FirstAccepted.cellRead output10 :=
    (congrArg (fun reference : CInputRef (Layout.selectedCtx ctx width) shape =>
      reference.underWorkspace (Layout.selectedCtx ctx width).canonicalFreshKey .bit
        (Layout.selectedCtx ctx width).canonicalFreshKey_fresh) agreed9).trans
      (cellRead_underWorkspace output9 (Layout.selectedCtx ctx width).canonicalFreshKey .bit
        (Layout.selectedCtx ctx width).canonicalFreshKey_fresh)
  let output11 : CWriteRef (Layout.context ctx width) shape :=
    output10.underWorkspace (Layout.availableCtx ctx width).canonicalFreshKey .bit
      (Layout.availableCtx ctx width).canonicalFreshKey_fresh
  let read11 : CInputRef (Layout.context ctx width) shape :=
    (read10).underWorkspace (Layout.availableCtx ctx width).canonicalFreshKey .bit
      (Layout.availableCtx ctx width).canonicalFreshKey_fresh
  have agreed11 : read11 = FirstAccepted.cellRead output11 :=
    (congrArg (fun reference : CInputRef (Layout.availableCtx ctx width) shape =>
      reference.underWorkspace (Layout.availableCtx ctx width).canonicalFreshKey .bit
        (Layout.availableCtx ctx width).canonicalFreshKey_fresh) agreed10).trans
      (cellRead_underWorkspace output10 (Layout.availableCtx ctx width).canonicalFreshKey .bit
        (Layout.availableCtx ctx width).canonicalFreshKey_fresh)
  exact agreed11

private lemma pop_output_read {shape : CShape} (output : CWriteRef ctx shape)
    (width : Nat) (store : Store (Layout.context ctx width)) :
    (Layout.popStore width store).read (FirstAccepted.cellRead output) =
      store.read (FirstAccepted.cellRead (Layout.underWrite output width)) :=
  (Layout.samplerLayout_pop_read (FirstAccepted.cellRead output) width store).trans
    (congrArg (fun reference => store.read reference) (underRead_cellRead output width))

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual initialized inner instruction sequence writes the source value. -/
lemma samplerInner_from_scope_read (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    (innerStep (model := model) N sample output (Layout.pushStore (modulusBits N) store)).1.read
      (FirstAccepted.cellRead (Layout.underWrite output (modulusBits N))) =
        parameterValue input value :=
  Decision.samplerDecision_source (model := model)
    input value (Layout.underWrite output (modulusBits N))
    (Scan.step (model := model) N sample (Layout.pushStore (modulusBits N) store)).1
    (Scan.samplerScan_from_scope (model := model) input sample store value sampled)
    (Scan.samplerScan_modulus (model := model)
      input sample (Layout.pushStore (modulusBits N) store))
    (Scan.samplerScan_from_scope_zero (model := model) sample store)

/-- Releasing the eleven real scopes preserves the complete parameter written for the caller. -/
lemma samplerProgram_read (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N))) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    (step (model := model) N sample output store).1.read (FirstAccepted.cellRead output) =
      parameterValue input value := by
  refine (congrArg (fun current : Store ctx => current.read (FirstAccepted.cellRead output))
    (samplerProgram_store_projection (model := model) N sample output store)).trans ?_
  exact (pop_output_read output (modulusBits N)
    (innerStep (model := model) N sample output (Layout.pushStore (modulusBits N) store)).1).trans
      (samplerInner_from_scope_read (model := model) input sample output store value sampled)

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

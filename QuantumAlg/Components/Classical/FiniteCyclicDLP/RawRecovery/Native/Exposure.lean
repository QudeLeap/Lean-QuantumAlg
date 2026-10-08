/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Base.Model
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Util.Classical.Modular.Basic
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native

/-!
# Actual three-cell raw-recovery exposure

Actual preparation and checked inversion feed the existing status-selected
recovery. A real fresh payload retains its candidate and reconstruction bit.
The original bit-copy, word-copy and bit-copy expose all three observations
before every private scope is released. The unused optional-result pack is
omitted; the successful payload's original product pack remains and is charged.
The independent optional-result entry point is unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original three copies consume the actual selected status and payload components. -/
def exposureCopyBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (.bit .copy ctx success inverseSuccess))
    (.seq (BitWord.instruction (execution := model) (.wordUnary .copy width ctx
      recoveredCandidate candidate))
      (BitWord.instruction (execution := model) (.bit .copy ctx verified reconstruction)))

/-- All three actual native outputs follow the original chronological copy stores. -/
def exposureCopyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (success : CInputRef ctx .bit)
    (recoveredCandidate : CInputRef ctx (.unsignedWord width)) (verified : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) (before : Store ctx) :
    Store ctx × (exposureCopyBody (model := model) success recoveredCandidate verified
      inverseSuccess candidate reconstruction).Path :=
  let first := BitWord.instructionStep (execution := model)
    (.bit .copy ctx success inverseSuccess) before
  let second := BitWord.instructionStep (execution := model)
    (.wordUnary .copy width ctx recoveredCandidate candidate) first.1
  let third := BitWord.instructionStep (execution := model)
    (.bit .copy ctx verified reconstruction) second.1
  (third.1, (first.2, (second.2, third.2)))

/-- Status-selected actual recovery precedes the original three chronological copy instructions. -/
def exposureBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (payload : CWriteRef ctx (FiniteCyclicDLP.OutputShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (.branch success (selectedRecoveryChoice (model := model) input modulus payload))
    (exposureCopyBody (model := model) success (.first (scaleRead payload)) (.second (scaleRead
      payload))
      inverseSuccess candidate reconstruction)

/-- Real payload initialization supplies the original zero candidate and false flag on failure. -/
def withSelectedExposure {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (FiniteCyclicDLP.InputShape width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1))) (success : CInputRef ctx .bit)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (FiniteCyclicDLP.OutputShape width)
    ctx.canonicalFreshKey_fresh
    (exposureBody (model := model) (underSelection input width) (underSelection modulus width)
      (underSelection success width) (selectionPayloadCell ctx width)
      (writeUnderSelection inverseSuccess width) (writeUnderSelection candidate width)
      (writeUnderSelection reconstruction width))

/-- The real checked outputs feed recovery before all three original observations are copied. -/
def checkedExposureBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (NumberTheory.Checked.Native.withCheckedInverse (model := model) spec left success inverse)
    (withSelectedExposure (model := model) (.product left (.product negatedRight (scaleRead
      inverse)))
      modulus (scaleRead success) inverseSuccess candidate reconstruction)

/-- Two actual checked-output cells stay live through exposure and are then released. -/
def withCheckedExposure {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width) (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  withCells ctx (checkedResultShapes width) fun cells _ transport _ =>
    checkedExposureBody (model := model) spec (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells)
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction)

/-- Actual raw measured values produce the three caller observations without caller workspace. -/
public def singleIntoCells {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  withPreparation (model := model) spec input fun refs transport =>
    withCheckedExposure (model := model) spec refs (transport.liftWrite inverseSuccess)
      (transport.liftWrite candidate) (transport.liftWrite reconstruction)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

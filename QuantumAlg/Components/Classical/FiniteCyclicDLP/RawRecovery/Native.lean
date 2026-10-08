/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Preparation.Placement
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native

/-!
# Actual raw Fourier recovery through the shared checked inverse

The original preparation consumes the actual measured finite binary values.
Two actual result cells retain the checked status and inverse while the
selected normalized recovery runs. The checked subcall includes its original
independent modulus loader. The outer prepared modulus stays live for the
original normalized-recovery multiplication and reconstruction.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original checked result allocation enters status first and then inverse. -/
def checkedResultShapes (width : Nat) : List CShape := [.unsignedWord width, .bit]

/-- Actual checked status retained through the selected recovery branch. -/
def checkedSuccessCell (cells : Cells ctx (checkedResultShapes width)) : CWriteRef ctx .bit :=
  cells.tail.head.ref

/-- Actual inverse result retained through both normalized multiplication calls. -/
def checkedInverseCell (cells : Cells ctx (checkedResultShapes width)) :
    CWriteRef ctx (.unsignedWord width) :=
  cells.head.ref

/-- The original checked inverse executes before status-selected normalized recovery. -/
def checkedSelectionBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width)) : Circuit model ctx ctx :=
  .seq (NumberTheory.Checked.Native.withCheckedInverse (model := model) spec left success inverse)
    (withSelectedRecovery (model := model) (.product left (.product negatedRight (scaleRead
      inverse)))
      modulus (scaleRead success) result)

/-- The two actual checked outputs remain live until the original optional result is written. -/
def withCheckedSelection {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width)) :
    Circuit model ctx ctx :=
  withCells ctx (checkedResultShapes width) fun cells _ transport _ =>
    checkedSelectionBody (model := model) spec (transport.liftInput (scaleRead refs.left))
      (transport.liftInput (scaleRead refs.negatedRight))
      (transport.liftInput (scaleRead refs.modulusWide))
      (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result)

/-- Actual preparation, shared checked inverse and selected recovery write the caller result. -/
def singleIntoResult {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (result : CWriteRef ctx (OutputShape width)) : Circuit model ctx ctx :=
  withPreparation (model := model) spec input fun refs transport =>
    withCheckedSelection (model := model) spec refs (transport.liftWrite result)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure

/-!
# Actual nearest raw-recovery preparation and checked exposure

One additional real lexical word stores the resized half denominator.  The
existing measured-bit decode, modulus and denominator loaders, final sign
normalization, checked inverse, recovery multiplication and result exposure
remain actual consumers.  Both nearest scalings reuse the same four scratch
words.  Every scope is allocated and released by this program.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open RawRecovery.Native (PreparationRefs preparationRefs preparationShapes scaleRead)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One extra full-product-width half word accompanies the thirteen original cells. -/
def preparationShapes (width : Nat) : List CShape :=
  .unsignedWord (width + (width + 1)) :: RawRecovery.Native.preparationShapes width

/-- The original physical raw and result cells feed one nearest scaling. -/
def scaleRefs (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1))))
    (right : Bool) : ScaleRefs ctx width where
  raw := scaleRead (if right then refs.rawRight else refs.rawLeft)
  order := scaleRead refs.modulusWide
  denominator := scaleRead refs.denominator
  product := refs.product
  half := half
  division := refs.division
  output := if right then refs.right else refs.left

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Two paid nearest scalings share one actual half, product and division workspace. -/
def preparationScale (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1)))) : Circuit model ctx ctx :=
  .seq (scaleBody (model := model) (scaleRefs refs half false))
    (scaleBody (model := model) (scaleRefs refs half true))

/-- Original measured decode and paid constants precede nearest normalization
and the original actual zero-test/sign-normalization branch. -/
def preparationBody (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (refs : PreparationRefs ctx width)
    (half : CWriteRef ctx (.unsignedWord (width + (width + 1)))) : Circuit model ctx ctx :=
  .seq (RawRecovery.Native.preparationDecodeSeed (model := model) spec input refs)
    (.seq (preparationScale (model := model) refs half)
      (RawRecovery.Native.preparationFinalize (model := model) refs))

/-- The complete actual allocation retains all fourteen preparation cells
through the checked recovery consumer and then releases them. -/
def withPreparation (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (consumer : ∀ {inner : RuntimeCtx model.kind}, PreparationRefs inner width →
      Transport ctx inner → Circuit model inner inner) : Circuit model ctx ctx :=
  withCells (model := model) ctx (preparationShapes width) fun cells _ transport _ =>
    .seq (preparationBody (model := model) spec (transport.liftInput input)
      (preparationRefs cells.tail) cells.head.ref)
      (consumer (preparationRefs cells.tail) transport)

/-- Actual nearest-rescaled measured values feed the original checked inverse,
candidate reconstruction and three existing caller result cells. -/
def singleIntoCells (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  withPreparation (model := model) spec input fun refs transport =>
    RawRecovery.Native.withCheckedExposure (model := model) spec refs
      (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
      (transport.liftWrite reconstruction)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

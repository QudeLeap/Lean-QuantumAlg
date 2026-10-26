/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub
import all QuantumAlg.Components.Classical.Modular.Reduce.Native.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction

/-!
# Exact paid native coordinates of shared-modulus subtraction

Two resizes, add-with-carry, subtract-with-borrow, quotient/remainder and
remainder resize are the six actual operations. Their ordered coordinates
are retained through every lexical scratch allocation and release.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Four actual arithmetic coordinates followed by the same actual two-operation reduction. -/
def subTrace (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.addCarry (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.subBorrow (width + 1)))] ++
      reductionEvents model (width + 1) width

private lemma stage_trace (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width)
    (path : (Circuit.forRange 4 (subStage (model := model) left right scratch)).Path) :
    (Circuit.forRange 4 (subStage (model := model) left right scratch)).eventTrace path =
      (subTrace model width).take 4 := by
  change (Circuit.seq (BitWord.instruction (execution := model) (subtractionLeftOp left scratch))
    (Circuit.seq (BitWord.instruction (execution := model) (subtractionRightOp right scratch))
      (Circuit.seq (BitWord.instruction (execution := model) (subtractionAugmentOp scratch))
        (Circuit.seq (BitWord.instruction (execution := model) (subtractionDifferenceOp scratch))
          (.id ctx))))).Path at path
  change (BitWord.instruction (execution := model) (subtractionLeftOp left scratch)).eventTrace
      path.1 ++
    ((BitWord.instruction (execution := model) (subtractionRightOp right scratch)).eventTrace
      path.2.1 ++
    ((BitWord.instruction (execution := model) (subtractionAugmentOp scratch)).eventTrace
      path.2.2.1 ++
    ((BitWord.instruction (execution := model) (subtractionDifferenceOp scratch)).eventTrace
      path.2.2.2.1 ++ []))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma body_trace (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (output : CWriteRef ctx (.unsignedWord width))
    (path : (subBody (model := model) left right scratch output).Path) :
    (subBody (model := model) left right scratch output).eventTrace path = subTrace model width :=
  congrArg₂ List.append (stage_trace left right scratch path.1)
    (reduceWord_eventTrace (.first (reductionRead scratch.difference))
      (reductionRead scratch.modulus) output path.2)

/-- The actual allocated subtraction retains all six native operation coordinates. -/
lemma sharedSubIntoWord_eventTrace (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) left right modulus output).Path) :
    (subIntoWord (model := model) left right modulus output).eventTrace path =
      subTrace model width := by
  exact withCellsFrom_property (Transport.id ctx) (subShapes width)
    (fun cells _ transport _ => subBody (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = subTrace model width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => body_trace _ _ _ _ selected) path

/-- Exact classification is a projection of this actual six-operation trace. -/
lemma sharedSubIntoWord_resourcePool (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) left right modulus output).Path) :
    (subIntoWord (model := model) left right modulus output).resourcePool path =
      ResourcePool.ofList (subTrace model width) :=
  congrArg ResourcePool.ofList (sharedSubIntoWord_eventTrace left right modulus output path)

/-- Each actual closed native operation contributes one, including both reduction operations. -/
lemma sharedSubIntoWord_eventCount (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) left right modulus output).Path) :
    ((subIntoWord (model := model) left right modulus output).eventTrace path).length = 6 := by
  rw [sharedSubIntoWord_eventTrace]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

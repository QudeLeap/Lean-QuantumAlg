/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add.Resources

/-!
# Exact paid native coordinates of shared-modulus addition

The real arithmetic prefix contributes two resizes and one add-with-carry.
The real reduction contributes one quotient/remainder and one remainder
resize. Both allocation scopes preserve this same five-operation trace.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The five actual coordinates, with the shared modulus loader charged by its caller. -/
def addTrace (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    List (Resource.Event model) :=
  additionPrefixTrace model width ++ reductionEvents model (width + 1) width

private lemma prefix_trace (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width)
    (path : (Circuit.forRange 3 (additionStage (model := model) left right scratch)).Path) :
    (Circuit.forRange 3 (additionStage (model := model) left right scratch)).eventTrace path =
      additionPrefixTrace model width := by
  change (Circuit.seq (BitWord.instruction (execution := model) (additionLeftOp left scratch))
    (Circuit.seq (BitWord.instruction (execution := model) (additionRightOp right scratch))
      (Circuit.seq (BitWord.instruction (execution := model) (additionSumOp scratch))
        (.id ctx)))).Path at path
  change (BitWord.instruction (execution := model) (additionLeftOp left scratch)).eventTrace
      path.1 ++
    ((BitWord.instruction (execution := model) (additionRightOp right scratch)).eventTrace
      path.2.1 ++
    ((BitWord.instruction (execution := model) (additionSumOp scratch)).eventTrace
      path.2.2.1 ++ [])) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma body_trace (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width))
    (path : (addBody (model := model) left right modulus scratch output).Path) :
    (addBody (model := model) left right modulus scratch output).eventTrace path =
      addTrace model width :=
  congrArg₂ List.append (prefix_trace left right scratch path.1)
    (reduceWord_eventTrace (.first (reductionRead scratch.sum)) modulus output path.2)

/-- The same five events survive all actual scratch allocations and releases. -/
lemma sharedAddIntoWord_eventTrace (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) left right modulus output).Path) :
    (addIntoWord (model := model) left right modulus output).eventTrace path =
      addTrace model width := by
  exact withCellsFrom_property (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => addBody (transport.liftInput left) (transport.liftInput right)
      (transport.liftInput modulus) (additionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = addTrace model width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => body_trace _ _ _ _ _ selected) path

/-- Exact classification comes from this actual trace and retains every width coordinate. -/
lemma sharedAddIntoWord_resourcePool (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) left right modulus output).Path) :
    (addIntoWord (model := model) left right modulus output).resourcePool path =
      ResourcePool.ofList (addTrace model width) :=
  congrArg ResourcePool.ofList (sharedAddIntoWord_eventTrace left right modulus output path)

/-- Each of the five real closed arithmetic instructions contributes one native operation. -/
lemma sharedAddIntoWord_eventCount (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) left right modulus output).Path) :
    ((addIntoWord (model := model) left right modulus output).eventTrace path).length = 5 := by
  rw [sharedAddIntoWord_eventTrace]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

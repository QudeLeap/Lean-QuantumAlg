/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Actual original raw field-addition resources

The two widenings and add-with-carry precede the original loaded reduction
trace. Both full operand snapshots, the carry pair, the real modulus and the
full division pair are charged with their actual lexical lifetimes.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original three arithmetic events before the modulus is loaded. -/
def additionPrefixTrace (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.addCarry (width + 1)))]

/-- The exact original raw field-addition event order. -/
def additionTrace (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : List (Resource.Event model) :=
  additionPrefixTrace model width ++ loadedReductionTrace model (width + 1) spec

/-- Original later reduction storage, excluding the three persistent arithmetic cells. -/
def additionReductionSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord (width + 1)) +
    SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width)

private theorem additionPrefix_eventTrace (left right : CInputRef ctx (.unsignedWord width))
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

private theorem additionPrefix_depth (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (duration : Resource.Event model → Nat)
    (path : (Circuit.forRange 3 (additionStage (model := model) left right scratch)).Path) :
    (Circuit.forRange 3 (additionStage (model := model) left right scratch)).depth duration path =
      ((additionPrefixTrace model width).map duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model) (additionLeftOp left scratch))
    (Circuit.seq (BitWord.instruction (execution := model) (additionRightOp right scratch))
      (Circuit.seq (BitWord.instruction (execution := model) (additionSumOp scratch))
        (.id ctx)))).Path at path
  change (BitWord.instruction (execution := model) (additionLeftOp left scratch)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (additionRightOp right scratch)).depth
      duration path.2.1 +
    ((BitWord.instruction (execution := model) (additionSumOp scratch)).depth
      duration path.2.2.1 + 0)) = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_depth]
  rfl

private theorem additionBody_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody (model := model) spec left right scratch output).Path) :
    (additionBody (model := model) spec left right scratch output).eventTrace path =
      additionTrace model spec :=
  congrArg₂ List.append (additionPrefix_eventTrace left right scratch path.1)
    (fieldReduceIntoWord_eventTrace spec (.first (Modular.Reduce.Native.reductionRead scratch.sum))
      output path.2)

/-- Real allocation and release preserve the complete original native field-addition trace. -/
theorem fieldAddIntoWord_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) spec left right output).Path) :
    (addIntoWord (model := model) spec left right output).eventTrace path =
      additionTrace model spec := by
  exact withCellsFrom_property (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = additionTrace model spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => additionBody_eventTrace _ _ _ _ _ selected) path

/-- Native counts are projected from the same actual original execution trace. -/
theorem addIntoWord_resourcePool (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) spec left right output).Path) :
    (addIntoWord (model := model) spec left right output).resourcePool path =
      ResourcePool.ofList (additionTrace model spec) :=
  congrArg ResourcePool.ofList (fieldAddIntoWord_eventTrace spec left right output path)

private theorem additionBody_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (additionBody (model := model) spec left right scratch output).Path) :
    (additionBody (model := model) spec left right scratch output).depth duration path =
      ((additionTrace model spec).map duration).sum := by
  refine (congrArg₂ Nat.add (additionPrefix_depth left right scratch duration path.1)
    (reduceIntoWord_durationDepth spec (.first (Modular.Reduce.Native.reductionRead scratch.sum))
      output duration path.2)).trans ?_
  simp only [additionTrace, List.map_append, List.sum_append]
  rfl

/-- Every original native duration contributes in its actual serial order. -/
theorem addIntoWord_durationDepth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (addIntoWord (model := model) spec left right output).Path) :
    (addIntoWord (model := model) spec left right output).depth duration path =
      ((additionTrace model spec).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((additionTrace model spec).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => additionBody_depth _ _ _ _ _ duration selected) path

private theorem additionBody_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody (model := model) spec left right scratch output).Path) :
    (additionBody (model := model) spec left right scratch output).peakResidentSpace path ≤
      additionReductionSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_resident_le 3 (additionStage left right scratch)
      ctx.residentSpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index <;> exact (Circuit.peakResidentSpace_classical _ selected).le
  · exact (reduceIntoWord_resident _ _ _ path.2).le

private theorem additionBody_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody (model := model) spec left right scratch output).Path) :
    (additionBody (model := model) spec left right scratch output).peakAuxiliarySpace path ≤
      additionReductionSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_auxiliary_le 3 (additionStage left right scratch)
      ctx.auxiliarySpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index <;> exact (Circuit.peakAuxiliarySpace_classical _ selected).le
  · exact (reduceIntoWord_auxiliary _ _ _ path.2).le

/-- All original arithmetic and reduction cells bound the actual resident peak. -/
theorem addIntoWord_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) spec left right output).Path) :
    (addIntoWord (model := model) spec left right output).peakResidentSpace path ≤
      ((additionShapes width).map SpacePool.ofShape).sum +
        additionReductionSpace model.kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (additionReductionSpace model.kind width)
    (fun cells _ transport _ selected => additionBody_resident _ _ _ _ _ selected) path

/-- Every original scratch cell retains its actual auxiliary ownership role. -/
theorem addIntoWord_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord (model := model) spec left right output).Path) :
    (addIntoWord (model := model) spec left right output).peakAuxiliarySpace path ≤
      ((additionShapes width).map SpacePool.ofShape).sum +
        additionReductionSpace model.kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (additionReductionSpace model.kind width)
    (fun cells _ transport _ selected => additionBody_auxiliary _ _ _ _ _ selected) path

omit [BitWord.Selected model] in
/-- The original two snapshots, sum/carry, modulus and division pair require this capacity. -/
theorem additionScratch_classicalBits :
    (((additionShapes width).map (SpacePool.ofShape (kind := model.kind))).sum +
      additionReductionSpace model.kind width) .classicalBits = 6 * width + 7 := by
  simp [additionShapes, additionReductionSpace, Modular.Reduce.Native.divisionShape,
    SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

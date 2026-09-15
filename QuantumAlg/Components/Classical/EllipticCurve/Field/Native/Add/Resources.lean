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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original three arithmetic events before the modulus is loaded. -/
def additionPrefixTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.addCarry (width + 1))]

/-- The exact original raw field-addition event order. -/
def additionTrace (kind : ProblemKind) (spec : ModulusSpec width) : List (Resource.Event kind) :=
  additionPrefixTrace width ++ loadedReductionTrace kind (width + 1) spec

/-- Original later reduction storage, excluding the three persistent arithmetic cells. -/
def additionReductionSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord (width + 1)) +
    SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width)

private theorem additionPrefix_eventTrace (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width)
    (path : (Circuit.forRange 3 (additionStage left right scratch)).Path) :
    (Circuit.forRange 3 (additionStage left right scratch)).eventTrace path =
      additionPrefixTrace width := rfl

private theorem additionPrefix_depth (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (duration : Resource.Event kind → Nat)
    (path : (Circuit.forRange 3 (additionStage left right scratch)).Path) :
    (Circuit.forRange 3 (additionStage left right scratch)).depth duration path =
      ((additionPrefixTrace width).map duration).sum := rfl

private theorem additionBody_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody spec left right scratch output).Path) :
    (additionBody spec left right scratch output).eventTrace path = additionTrace kind spec :=
  congrArg₂ List.append (additionPrefix_eventTrace left right scratch path.1)
    (fieldReduceIntoWord_eventTrace spec (.first (Modular.Reduce.Native.reductionRead scratch.sum))
      output path.2)

/-- Real allocation and release preserve the complete original native field-addition trace. -/
theorem fieldAddIntoWord_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord spec left right output).Path) :
    (addIntoWord spec left right output).eventTrace path = additionTrace kind spec := by
  exact withCellsFrom_property (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = additionTrace kind spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => additionBody_eventTrace _ _ _ _ _ selected) path

/-- Native counts are projected from the same actual original execution trace. -/
theorem addIntoWord_resourcePool (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord spec left right output).Path) :
    (addIntoWord spec left right output).resourcePool path =
      ResourcePool.ofList (additionTrace kind spec) :=
  congrArg ResourcePool.ofList (fieldAddIntoWord_eventTrace spec left right output path)

private theorem additionBody_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (additionBody spec left right scratch output).Path) :
    (additionBody spec left right scratch output).depth duration path =
      ((additionTrace kind spec).map duration).sum := by
  refine (congrArg₂ Nat.add (additionPrefix_depth left right scratch duration path.1)
    (reduceIntoWord_durationDepth spec (.first (Modular.Reduce.Native.reductionRead scratch.sum))
      output duration path.2)).trans ?_
  simp only [additionTrace, List.map_append, List.sum_append]
  rfl

/-- Every original native duration contributes in its actual serial order. -/
theorem addIntoWord_durationDepth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event kind → Nat) (path : (addIntoWord spec left right output).Path) :
    (addIntoWord spec left right output).depth duration path =
      ((additionTrace kind spec).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((additionTrace kind spec).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => additionBody_depth _ _ _ _ _ duration selected) path

private theorem additionBody_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody spec left right scratch output).Path) :
    (additionBody spec left right scratch output).peakResidentSpace path ≤
      additionReductionSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_resident_le 3 (additionStage left right scratch)
      ctx.residentSpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index <;> exact (Circuit.peakResidentSpace_classical _ selected).le
  · exact (reduceIntoWord_resident _ _ _ path.2).le

private theorem additionBody_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (additionBody spec left right scratch output).Path) :
    (additionBody spec left right scratch output).peakAuxiliarySpace path ≤
      additionReductionSpace kind width + ctx.auxiliarySpace := by
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
    (path : (addIntoWord spec left right output).Path) :
    (addIntoWord spec left right output).peakResidentSpace path ≤
      ((additionShapes width).map SpacePool.ofShape).sum + additionReductionSpace kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (additionReductionSpace kind width)
    (fun cells _ transport _ selected => additionBody_resident _ _ _ _ _ selected) path

/-- Every original scratch cell retains its actual auxiliary ownership role. -/
theorem addIntoWord_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (addIntoWord spec left right output).Path) :
    (addIntoWord spec left right output).peakAuxiliarySpace path ≤
      ((additionShapes width).map SpacePool.ofShape).sum + additionReductionSpace kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (additionReductionSpace kind width)
    (fun cells _ transport _ selected => additionBody_auxiliary _ _ _ _ _ selected) path

/-- The original two snapshots, sum/carry, modulus and division pair require this capacity. -/
theorem additionScratch_classicalBits :
    (((additionShapes width).map (SpacePool.ofShape (kind := kind))).sum +
      additionReductionSpace kind width) .classicalBits = 6 * width + 7 := by
  simp [additionShapes, additionReductionSpace, Modular.Reduce.Native.divisionShape,
    SpacePool.ofShape, CShape.bitWidth]
  omega

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

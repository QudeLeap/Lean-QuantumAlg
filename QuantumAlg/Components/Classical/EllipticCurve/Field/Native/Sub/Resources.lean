/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Actual original raw field-subtraction resources

The two widenings and add-with-carry precede the original loaded reduction
trace. Both full operand snapshots, the carry pair, the real modulus and the
full division pair are charged with their actual lexical lifetimes.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original two widenings, first modulus load and two flagged arithmetic operations. -/
def subtractionPrefixTrace (kind : ProblemKind) (spec : ModulusSpec width) :
    List (Resource.Event kind) :=
  [.classicalOperation (.wordResize width (width + 1)),
    .classicalOperation (.wordResize width (width + 1))] ++
      ConstantWord.loaderTrace kind (width + 1)
        (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) ++
      [.classicalOperation (.addCarry (width + 1)),
        .classicalOperation (.subBorrow (width + 1))]

/-- The exact original raw field-subtraction event order retains the second modulus load. -/
def subtractionTrace (kind : ProblemKind) (spec : ModulusSpec width) : List (Resource.Event kind) :=
  subtractionPrefixTrace kind spec ++ loadedReductionTrace kind (width + 1) spec

/-- Original later reduction storage, excluding the five persistent arithmetic cells. -/
def subtractionReductionSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord (width + 1)) +
    SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width)

private theorem subtractionPrefix_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (path : (Circuit.forRange 5 (subtractionStage spec left right scratch)).Path) :
    (Circuit.forRange 5 (subtractionStage spec left right scratch)).eventTrace path =
      subtractionPrefixTrace kind spec := by
  have loaded := ConstantWord.constantFold_eventTrace scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.2.2.1
  change [.classicalOperation (.wordResize width (width + 1))] ++
    ([.classicalOperation (.wordResize width (width + 1))] ++
      ((ConstantWord.circuit scratch.modulus spec.modulus).eventTrace path.2.2.1 ++
        ([.classicalOperation (.addCarry (width + 1))] ++
          ([.classicalOperation (.subBorrow (width + 1))] ++ [])))) = _
  change .classicalOperation (.wordResize width (width + 1)) ::
    .classicalOperation (.wordResize width (width + 1)) ::
      ((ConstantWord.circuit scratch.modulus spec.modulus).eventTrace path.2.2.1 ++
        [.classicalOperation (.addCarry (width + 1)),
          .classicalOperation (.subBorrow (width + 1))]) = _
  exact congrArg (fun events =>
    .classicalOperation (.wordResize width (width + 1)) ::
      .classicalOperation (.wordResize width (width + 1)) ::
        (events ++ [.classicalOperation (.addCarry (width + 1)),
          .classicalOperation (.subBorrow (width + 1))])) loaded

private theorem subtractionPrefix_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (duration : Resource.Event kind → Nat)
    (path : (Circuit.forRange 5 (subtractionStage spec left right scratch)).Path) :
    (Circuit.forRange 5 (subtractionStage spec left right scratch)).depth duration path =
      ((subtractionPrefixTrace kind spec).map duration).sum := by
  have loaded := ConstantWord.constantFold_depth scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) duration path.2.2.1
  change duration (.classicalOperation (.wordResize width (width + 1))) +
    (duration (.classicalOperation (.wordResize width (width + 1))) +
      ((ConstantWord.circuit scratch.modulus spec.modulus).depth duration path.2.2.1 +
        (duration (.classicalOperation (.addCarry (width + 1))) +
          (duration (.classicalOperation (.subBorrow (width + 1))) + 0)))) = _
  refine (congrArg (fun depth =>
    duration (.classicalOperation (.wordResize width (width + 1))) +
      (duration (.classicalOperation (.wordResize width (width + 1))) +
        (depth + (duration (.classicalOperation (.addCarry (width + 1))) +
          (duration (.classicalOperation (.subBorrow (width + 1))) + 0))))) loaded).trans ?_
  simp [subtractionPrefixTrace]

private theorem subtractionBody_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody spec left right scratch output).Path) :
    (subtractionBody spec left right scratch output).eventTrace path = subtractionTrace kind spec :=
  congrArg₂ List.append
    (subtractionPrefix_eventTrace spec left right scratch path.1)
    (fieldReduceIntoWord_eventTrace spec
      (.first (Modular.Reduce.Native.reductionRead scratch.difference))
      output path.2)

/-- Real allocation and release preserve the complete original native field-subtraction trace. -/
theorem fieldSubIntoWord_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord spec left right output).Path) :
    (subIntoWord spec left right output).eventTrace path = subtractionTrace kind spec := by
  exact withCellsFrom_property (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = subtractionTrace kind spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => subtractionBody_eventTrace _ _ _ _ _ selected) path

/-- Native counts are projected from the same actual original execution trace. -/
theorem subIntoWord_resourcePool (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord spec left right output).Path) :
    (subIntoWord spec left right output).resourcePool path =
      ResourcePool.ofList (subtractionTrace kind spec) :=
  congrArg ResourcePool.ofList (fieldSubIntoWord_eventTrace spec left right output path)

private theorem subtractionBody_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (subtractionBody spec left right scratch output).Path) :
    (subtractionBody spec left right scratch output).depth duration path =
      ((subtractionTrace kind spec).map duration).sum := by
  refine (congrArg₂ Nat.add
    (subtractionPrefix_depth spec left right scratch duration path.1)
    (reduceIntoWord_durationDepth spec
      (.first (Modular.Reduce.Native.reductionRead scratch.difference))
      output duration path.2)).trans ?_
  simp only [subtractionTrace, List.map_append, List.sum_append]
  rfl

/-- Every original native duration contributes in its actual serial order. -/
theorem subIntoWord_durationDepth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event kind → Nat) (path : (subIntoWord spec left right output).Path) :
    (subIntoWord spec left right output).depth duration path =
      ((subtractionTrace kind spec).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((subtractionTrace kind spec).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => subtractionBody_depth _ _ _ _ _ duration selected) path

private theorem subtractionBody_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody spec left right scratch output).Path) :
    (subtractionBody spec left right scratch output).peakResidentSpace path ≤
      subtractionReductionSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_resident_le 5 (subtractionStage spec left right scratch)
      ctx.residentSpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index
    all_goals first
      | exact ConstantWord.constantWord_resident_le scratch.modulus spec.modulus selected
      | exact (Circuit.peakResidentSpace_classical _ selected).le
  · exact (reduceIntoWord_resident _ _ _ path.2).le

private theorem subtractionBody_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody spec left right scratch output).Path) :
    (subtractionBody spec left right scratch output).peakAuxiliarySpace path ≤
      subtractionReductionSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_auxiliary_le 5 (subtractionStage spec left right scratch)
      ctx.auxiliarySpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index
    all_goals first
      | exact ConstantWord.constantWord_auxiliary_le scratch.modulus spec.modulus selected
      | exact (Circuit.peakAuxiliarySpace_classical _ selected).le
  · exact (reduceIntoWord_auxiliary _ _ _ path.2).le

/-- All original arithmetic and reduction cells bound the actual resident peak. -/
theorem subIntoWord_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord spec left right output).Path) :
    (subIntoWord spec left right output).peakResidentSpace path ≤
      ((subtractionShapes width).map SpacePool.ofShape).sum + subtractionReductionSpace kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (subtractionReductionSpace kind width)
    (fun cells _ transport _ selected => subtractionBody_resident _ _ _ _ _ selected) path

/-- Every original scratch cell retains its actual auxiliary ownership role. -/
theorem subIntoWord_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord spec left right output).Path) :
    (subIntoWord spec left right output).peakAuxiliarySpace path ≤
      ((subtractionShapes width).map SpacePool.ofShape).sum + subtractionReductionSpace kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (subtractionReductionSpace kind width)
    (fun cells _ transport _ selected => subtractionBody_auxiliary _ _ _ _ _ selected) path

/-- The original five arithmetic cells, later modulus and division pair require this capacity. -/
theorem subtractionScratch_classicalBits :
    (((subtractionShapes width).map (SpacePool.ofShape (kind := kind))).sum +
      subtractionReductionSpace kind width) .classicalBits = 8 * width + 10 := by
  simp [subtractionShapes, subtractionReductionSpace, Modular.Reduce.Native.divisionShape,
    SpacePool.ofShape, CShape.bitWidth]
  omega

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

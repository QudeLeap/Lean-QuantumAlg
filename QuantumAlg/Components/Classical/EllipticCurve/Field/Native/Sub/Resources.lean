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

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original two widenings, first modulus load and two flagged arithmetic operations. -/
def subtractionPrefixTrace (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize width (width + 1)))] ++
      ConstantWord.loaderTrace model (width + 1)
        (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) ++
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.addCarry (width + 1))),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.subBorrow (width + 1)))]

/-- The exact original raw field-subtraction event order retains the second modulus load. -/
def subtractionTrace (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : List (Resource.Event model) :=
  subtractionPrefixTrace model spec ++ loadedReductionTrace model (width + 1) spec

/-- Original later reduction storage, excluding the five persistent arithmetic cells. -/
def subtractionReductionSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord (width + 1)) +
    SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width)

private lemma subtractionPrefix_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (path : (Circuit.forRange 5
      (subtractionStage (model := model) spec left right scratch)).Path) :
    (Circuit.forRange 5 (subtractionStage (model := model) spec left right scratch)).eventTrace
      path = subtractionPrefixTrace model spec := by
  have loaded := ConstantWord.constantFold_eventTrace scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.2.2.1
  change (Circuit.seq (BitWord.instruction (execution := model) (subtractionLeftOp left scratch))
    (Circuit.seq (BitWord.instruction (execution := model) (subtractionRightOp right scratch))
      (Circuit.seq (ConstantWord.fold (model := model) scratch.modulus
          (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)))
        (Circuit.seq (BitWord.instruction (execution := model) (subtractionAugmentOp scratch))
          (Circuit.seq (BitWord.instruction (execution := model)
            (subtractionDifferenceOp scratch)) (.id ctx)))))).Path at path
  change (BitWord.instruction (execution := model) (subtractionLeftOp left scratch)).eventTrace
      path.1 ++
    ((BitWord.instruction (execution := model) (subtractionRightOp right scratch)).eventTrace
      path.2.1 ++
    ((ConstantWord.fold (model := model) scratch.modulus
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).eventTrace path.2.2.1 ++
    ((BitWord.instruction (execution := model) (subtractionAugmentOp scratch)).eventTrace
      path.2.2.2.1 ++
    ((BitWord.instruction (execution := model) (subtractionDifferenceOp scratch)).eventTrace
      path.2.2.2.2.1 ++ [])))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace, loaded]
  rfl

private lemma subtractionPrefix_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (duration : Resource.Event model → Nat)
    (path : (Circuit.forRange 5
      (subtractionStage (model := model) spec left right scratch)).Path) :
    (Circuit.forRange 5 (subtractionStage (model := model) spec left right scratch)).depth
      duration path = ((subtractionPrefixTrace model spec).map duration).sum := by
  have loaded := ConstantWord.constantFold_depth scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) duration path.2.2.1
  change (Circuit.seq (BitWord.instruction (execution := model) (subtractionLeftOp left scratch))
    (Circuit.seq (BitWord.instruction (execution := model) (subtractionRightOp right scratch))
      (Circuit.seq (ConstantWord.fold (model := model) scratch.modulus
          (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)))
        (Circuit.seq (BitWord.instruction (execution := model) (subtractionAugmentOp scratch))
          (Circuit.seq (BitWord.instruction (execution := model)
            (subtractionDifferenceOp scratch)) (.id ctx)))))).Path at path
  change (BitWord.instruction (execution := model) (subtractionLeftOp left scratch)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (subtractionRightOp right scratch)).depth
      duration path.2.1 +
    ((ConstantWord.fold (model := model) scratch.modulus
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))).depth
        duration path.2.2.1 +
    ((BitWord.instruction (execution := model) (subtractionAugmentOp scratch)).depth
      duration path.2.2.2.1 +
    ((BitWord.instruction (execution := model) (subtractionDifferenceOp scratch)).depth
      duration path.2.2.2.2.1 + 0)))) = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth, loaded]
  simp [subtractionPrefixTrace, subtractionLeftOp, subtractionRightOp,
    subtractionAugmentOp, subtractionDifferenceOp, ClassicalOp.label]

private lemma subtractionBody_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody (model := model) spec left right scratch output).Path) :
    (subtractionBody (model := model) spec left right scratch output).eventTrace path =
      subtractionTrace model spec :=
  congrArg₂ List.append
    (subtractionPrefix_eventTrace spec left right scratch path.1)
    (fieldReduceIntoWord_eventTrace spec
      (.first (Modular.Reduce.Native.reductionRead scratch.difference))
      output path.2)

/-- Real allocation and release preserve the complete original native field-subtraction trace. -/
lemma fieldSubIntoWord_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) spec left right output).Path) :
    (subIntoWord (model := model) spec left right output).eventTrace path =
      subtractionTrace model spec := by
  exact withCellsFrom_property (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = subtractionTrace model spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => subtractionBody_eventTrace _ _ _ _ _ selected) path

/-- Native counts are projected from the same actual original execution trace. -/
lemma subIntoWord_resourcePool (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) spec left right output).Path) :
    (subIntoWord (model := model) spec left right output).resourcePool path =
      ResourcePool.ofList (subtractionTrace model spec) :=
  congrArg ResourcePool.ofList (fieldSubIntoWord_eventTrace spec left right output path)

private lemma subtractionBody_depth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event model → Nat)
    (path : (subtractionBody (model := model) spec left right scratch output).Path) :
    (subtractionBody (model := model) spec left right scratch output).depth duration path =
      ((subtractionTrace model spec).map duration).sum := by
  refine (congrArg₂ Nat.add
    (subtractionPrefix_depth spec left right scratch duration path.1)
    (reduceIntoWord_durationDepth spec
      (.first (Modular.Reduce.Native.reductionRead scratch.difference))
      output duration path.2)).trans ?_
  simp only [subtractionTrace, List.map_append, List.sum_append]
  rfl

/-- Every original native duration contributes in its actual serial order. -/
lemma subIntoWord_durationDepth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (subIntoWord (model := model) spec left right output).Path) :
    (subIntoWord (model := model) spec left right output).depth duration path =
      ((subtractionTrace model spec).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((subtractionTrace model spec).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => subtractionBody_depth _ _ _ _ _ duration selected) path

private lemma subtractionBody_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody (model := model) spec left right scratch output).Path) :
    (subtractionBody (model := model) spec left right scratch output).peakResidentSpace path ≤
      subtractionReductionSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_resident_le 5 (subtractionStage spec left right scratch)
      ctx.residentSpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index
    · change (BitWord.instruction (execution := model) _).peakResidentSpace selected ≤ _
      exact (Circuit.peakResidentSpace_classical _ selected).le
    · change (BitWord.instruction (execution := model) _).peakResidentSpace selected ≤ _
      exact (Circuit.peakResidentSpace_classical _ selected).le
    · change (ConstantWord.circuit (model := model) scratch.modulus spec.modulus).peakResidentSpace
        selected ≤ _
      exact ConstantWord.constantWord_resident_le scratch.modulus spec.modulus selected
    · change (BitWord.instruction (execution := model) _).peakResidentSpace selected ≤ _
      exact (Circuit.peakResidentSpace_classical _ selected).le
    · change (BitWord.instruction (execution := model) _).peakResidentSpace selected ≤ _
      exact (Circuit.peakResidentSpace_classical _ selected).le
  · exact (reduceIntoWord_resident _ _ _ path.2).le

private lemma subtractionBody_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subtractionBody (model := model) spec left right scratch output).Path) :
    (subtractionBody (model := model) spec left right scratch output).peakAuxiliarySpace path ≤
      subtractionReductionSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · apply (Circuit.forRange_auxiliary_le 5 (subtractionStage spec left right scratch)
      ctx.auxiliarySpace le_rfl ?_ path.1).trans le_add_self
    intro index selected
    fin_cases index
    · change (BitWord.instruction (execution := model) _).peakAuxiliarySpace selected ≤ _
      exact (Circuit.peakAuxiliarySpace_classical _ selected).le
    · change (BitWord.instruction (execution := model) _).peakAuxiliarySpace selected ≤ _
      exact (Circuit.peakAuxiliarySpace_classical _ selected).le
    · change (ConstantWord.circuit (model := model) scratch.modulus spec.modulus).peakAuxiliarySpace
        selected ≤ _
      exact ConstantWord.constantWord_auxiliary_le scratch.modulus spec.modulus selected
    · change (BitWord.instruction (execution := model) _).peakAuxiliarySpace selected ≤ _
      exact (Circuit.peakAuxiliarySpace_classical _ selected).le
    · change (BitWord.instruction (execution := model) _).peakAuxiliarySpace selected ≤ _
      exact (Circuit.peakAuxiliarySpace_classical _ selected).le
  · exact (reduceIntoWord_auxiliary _ _ _ path.2).le

/-- All original arithmetic and reduction cells bound the actual resident peak. -/
lemma subIntoWord_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) spec left right output).Path) :
    (subIntoWord (model := model) spec left right output).peakResidentSpace path ≤
      ((subtractionShapes width).map SpacePool.ofShape).sum +
        subtractionReductionSpace model.kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (subtractionReductionSpace model.kind width)
    (fun cells _ transport _ selected => subtractionBody_resident _ _ _ _ _ selected) path

/-- Every original scratch cell retains its actual auxiliary ownership role. -/
lemma subIntoWord_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (subIntoWord (model := model) spec left right output).Path) :
    (subIntoWord (model := model) spec left right output).peakAuxiliarySpace path ≤
      ((subtractionShapes width).map SpacePool.ofShape).sum +
        subtractionReductionSpace model.kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (subtractionReductionSpace model.kind width)
    (fun cells _ transport _ selected => subtractionBody_auxiliary _ _ _ _ _ selected) path

omit [BitWord.Selected model] in
/-- The original five arithmetic cells, later modulus and division pair require this capacity. -/
lemma subtractionScratch_classicalBits :
    (((subtractionShapes width).map (SpacePool.ofShape (kind := model.kind))).sum +
      subtractionReductionSpace model.kind width) .classicalBits = 8 * width + 10 := by
  simp [subtractionShapes, subtractionReductionSpace, Modular.Reduce.Native.divisionShape,
    SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

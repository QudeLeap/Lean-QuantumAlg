/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Bound
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources

/-!
# Actual arithmetic peaks beneath the four reused scalar words

The complete original coefficient scope is the common independent
allowance. Actual shared add/subtract scopes and full-product division
scopes are smaller at every native axis; their bounds include each real
lexical temporary and preserve the caller's resident/auxiliary roles.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open Field.Native Field.Native.Shared
open Modular.NativePower Modular.Reduce.Native

noncomputable section

private lemma addSpace_le (kind : ProblemKind) (width : Nat) :
    ((additionShapes width).map (SpacePool.ofShape (kind := kind))).sum +
        SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width) ≤
      coefficientScratchSpace kind width := by
  intro axis
  cases axis with
  | classicalBits =>
      rw [show coefficientScratchSpace kind width SpaceAxis.classicalBits = _ from
        coefficientScratchSpace_classicalBits kind width]
      simp [additionShapes, Modular.Reduce.Native.divisionShape, SpacePool.ofShape]
      omega
  | quantumSystems dimension => simp [additionShapes, SpacePool.ofShape]

private lemma subSpace_le (kind : ProblemKind) (width : Nat) :
    ((subShapes width).map (SpacePool.ofShape (kind := kind))).sum +
        SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width) ≤
      coefficientScratchSpace kind width := by
  intro axis
  cases axis with
  | classicalBits =>
      rw [show coefficientScratchSpace kind width SpaceAxis.classicalBits = _ from
        coefficientScratchSpace_classicalBits kind width]
      simp [subShapes, Modular.Reduce.Native.divisionShape, SpacePool.ofShape]
      omega
  | quantumSystems dimension => simp [subShapes, SpacePool.ofShape]

private lemma multiplySpace_le (kind : ProblemKind) (width : Nat) :
    additionalSpace kind width ≤ coefficientScratchSpace kind width := by
  intro axis
  cases axis with
  | classicalBits =>
      rw [show coefficientScratchSpace kind width SpaceAxis.classicalBits = _ from
        coefficientScratchSpace_classicalBits kind width]
      simp [additionalSpace, SpacePool.ofShape]
      omega
  | quantumSystems dimension => simp [additionalSpace, SpacePool.ofShape]

private lemma multiplyContexts_resident {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) (visited : RuntimeCtx kind)
    (member : visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width]) :
    visited.residentSpace ≤ additionalSpace kind width + ctx.residentSpace := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;> simp [additionalSpace, productCtx, divisionCtx,
      Modular.NativePower.divisionShape, SpacePool.ofShape] <;> omega

private lemma multiplyContexts_auxiliary {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width : Nat) (visited : RuntimeCtx kind)
    (member : visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width]) :
    visited.auxiliarySpace ≤ additionalSpace kind width + ctx.auxiliarySpace := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;> simp [additionalSpace, productCtx, divisionCtx,
      Modular.NativePower.divisionShape, SpacePool.ofShape] <;> omega

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual original loaded coefficient routine fits precisely its original live allowance. -/
lemma coefficient (spec : ModulusSpec width) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (coefficientScratchSpace model.kind width)
      (coefficientIntoWord (model := model) spec input output) := by
  intro path
  exact ⟨coefficientIntoWord_resident_le spec input output path,
    coefficientIntoWord_auxiliary_le spec input output path⟩

private lemma reduction {sourceWidth : Nat}
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (SpacePool.ofShape (Modular.Reduce.Native.divisionShape sourceWidth width))
      (reduceWord (model := model) input modulus output) := by
  intro path
  exact ⟨(reduceWord_resident input modulus output path).le,
    (reduceWord_auxiliary input modulus output path).le⟩

private lemma addBody_bound (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width))
      (addBody (model := model) left right modulus scratch output) := by
  apply seq
  · apply range
    intro index
    fin_cases index <;> exact (instruction _).mono zero_le
  · exact reduction _ _ _

/-- Shared addition retains all three snapshots and the actual quotient/remainder pair. -/
lemma add (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (coefficientScratchSpace model.kind width)
      (addIntoWord (model := model) left right modulus output) := by
  have actual := allocate (Transport.id ctx) (additionShapes width)
    (fun cells _ lift _ => addBody (lift.liftInput left) (lift.liftInput right)
      (lift.liftInput modulus) (additionScratch cells) (lift.liftWrite output))
    (SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width))
    (fun cells _ lift _ => addBody_bound _ _ _ _ _)
  exact actual.mono (addSpace_le model.kind width)

private lemma subBody_bound (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width))
      (subBody (model := model) left right scratch output) := by
  apply seq
  · apply range
    intro index
    fin_cases index <;> exact (instruction _).mono zero_le
  · exact reduction _ _ _

/-- Shared subtraction retains four actual arithmetic snapshots and its full division pair. -/
lemma sub (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (coefficientScratchSpace model.kind width)
      (subIntoWord (model := model) left right modulus output) := by
  have actual := allocate (Transport.id ctx) (subShapes width)
    (fun cells _ lift _ => subBody (lift.liftInput left) (lift.liftInput right)
      (subScratch cells (lift.liftWrite modulus)) (lift.liftWrite output))
    (SpacePool.ofShape (Modular.Reduce.Native.divisionShape (width + 1) width))
    (fun cells _ lift _ => subBody_bound _ _ _ _)
  exact actual.mono (subSpace_le model.kind width)

/-- Actual full-product and quotient/remainder cells are released together after multiplication. -/
lemma multiply (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Bound (coefficientScratchSpace model.kind width)
      (scopedMultiply (model := model) left right modulus output) := by
  have actual : Bound (additionalSpace model.kind width)
      (scopedMultiply (model := model) left right modulus output) := by
    intro path
    constructor
    · apply Circuit.peakResidentSpace_le_of_visited
      intro visited present
      have options := nativePower_scopedMultiply_visited left right modulus output
        path visited present
      exact multiplyContexts_resident ctx width visited options
    · apply Circuit.peakAuxiliarySpace_le_of_visited
      intro visited present
      have options := nativePower_scopedMultiply_visited left right modulus output
        path visited present
      exact multiplyContexts_auxiliary ctx width visited options
  exact actual.mono (multiplySpace_le model.kind width)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace

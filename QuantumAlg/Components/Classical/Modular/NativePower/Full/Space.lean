/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Construction
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete live classical space of native modular power

The modulus, raw base and accumulator use `3 * width + 1` real lexical bits.
During each actual multiplication, the full product and division pair add
`5 * width + 1` bits. The independent extra peak is therefore `8 * width + 2`,
with all original storage retained and every quantum coordinate unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- Independent capacity for all simultaneously live power and multiplication scratch cells. -/
def powerSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (8 * width + 2))

/-- Every actual visited context is one of the six concrete lexical allocation stages. -/
lemma nativePower_into_visited (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) spec base exponent output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into (model := model) spec base exponent output).visitedContexts path) :
    visited ∈ [ctx, modulusCtx ctx width, baseCtx ctx width, powerCtx ctx width,
      productCtx (powerCtx ctx width) width, divisionCtx (powerCtx ctx width) width] := by
  have member : visited ∈ [ctx, modulusCtx ctx width, baseCtx ctx width, powerCtx ctx width] ++
      ((ConstantWord.circuit (model := model) (modulusCell ctx width) spec.modulus).visitedContexts
        path.2.1 ++
        ([powerCtx ctx width] ++
          ((exponentCircuit (model := model) (wordRead (baseCell ctx width))
            (underPower exponent width)
            (wordRead (modulusCell ctx width)) (accumulatorCell ctx width)).visitedContexts
              path.2.2.2.1 ++
            [powerCtx ctx width, baseCtx ctx width, modulusCtx ctx width, ctx]))) := by
    simpa only [into, powerBody, BitWord.instruction, Circuit.visitedContexts, List.cons_append,
      List.append_assoc,
      List.nil_append] using present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | loaded | rfl | powered | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · have same := ConstantWord.constantWord_fold_visited (modulusCell ctx width)
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) path.2.1 visited loaded
    rw [same]
    simp
  · simp
  · have inner := nativePower_fold_visited (wordRead (baseCell ctx width))
      (wordRead (modulusCell ctx width)) (accumulatorCell ctx width)
      (List.ofFn (fun index : Fin exponentWidth =>
        CInputRef.wordBitGet (underPower exponent width) index)) path.2.2.2.1 visited powered
    exact List.mem_append_right [ctx, modulusCtx ctx width, baseCtx ctx width] inner
  · simp
  · simp
  · simp
  · simp

/-- Resident peak counts all original entries and the actual simultaneous lexical scratch. -/
lemma nativePower_into_resident_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) spec base exponent output).Path) :
    (into (model := model) spec base exponent output).peakResidentSpace path ≤
      ctx.residentSpace + powerSpace model.kind width := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have member := nativePower_into_visited spec base exponent output path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases model <;> intro axis
    all_goals cases axis <;> simp [powerSpace, modulusCtx, baseCtx, powerCtx,
      productCtx, divisionCtx,
      divisionShape, SpacePool.ofShape] <;> omega

/-- The actual added bits are all auxiliary while every original storage role is retained. -/
lemma nativePower_into_auxiliary_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (into (model := model) spec base exponent output).Path) :
    (into (model := model) spec base exponent output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + powerSpace model.kind width := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have member := nativePower_into_visited spec base exponent output path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases model <;> intro axis
    all_goals cases axis <;> simp [powerSpace, modulusCtx, baseCtx, powerCtx,
      productCtx, divisionCtx,
      divisionShape, SpacePool.ofShape] <;> omega

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower

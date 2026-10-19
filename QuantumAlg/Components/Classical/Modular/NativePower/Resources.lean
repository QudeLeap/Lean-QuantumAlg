/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Circuit
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent native budgets for finite square-and-multiply

Each declared exponent slot executes one square and at most one selected base
multiplication. Each reduction consists of full multiplication, division and
remainder resizing. The two scratch scopes require `5 * width + 1` classical
bits at peak and are reused across all slots; no quantum wire is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent three-coordinate allowance for one exact full-product reduction. -/
def multiplyEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.mulFull width width))) +
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem (width + width) (width + 1)))) +
    ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width)))

/-- A square is mandatory; a second multiplication is allowed only on the selected true path. -/
def bitEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : ResourcePool
  model :=
  multiplyEnvelope model width + multiplyEnvelope model width

/-- Width-only allowance for visiting every declared exponent slot. -/
def exponentEnvelope (model : ExecutionModel) [BitWord.Selected model] (width exponentWidth :
  Nat) : ResourcePool model :=
  ResourcePool.scale exponentWidth (bitEnvelope model width)

/-- Independent extra live capacity of the full product and quotient/remainder pair. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (5 * width + 1))

/-- The lexical reduction emits exactly its three actual operation coordinates. -/
lemma nativePower_scopedMultiply_pool
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scopedMultiply (model := model) left right modulus output).Path) :
    (scopedMultiply (model := model) left right modulus output).resourcePool path =
      multiplyEnvelope model width := by
  change (multiplyBody (model := model) (underMultiply left width) (underMultiply right width)
    (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
    (writeUnderMultiply output width)).Path at path
  change ResourcePool.ofList
    ((multiplyBody (model := model) (underMultiply left width) (underMultiply right width)
      (underMultiply modulus width) (productCell ctx width) (divisionCell ctx width)
      (writeUnderMultiply output width)).eventTrace path) = _
  rw [nativePowerMultiply_eventTrace]
  simp only [multiplyEvents, ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero,
    multiplyEnvelope, add_assoc]

/-- Selected paths retain the mandatory square and at most one real base multiplication. -/
lemma nativePower_bit_pool_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (path : (bitCircuit (model := model) base modulus output bit).Path) :
    (bitCircuit (model := model) base modulus output bit).resourcePool path ≤ bitEnvelope model
      width := by
  rcases path with ⟨squarePath, value, selectedPath⟩
  change ResourcePool.ofList
    ((scopedMultiply (model := model) (wordRead output) (wordRead output) modulus
      output).eventTrace squarePath ++
      (multiplyChoice (model := model) base modulus output value).eventTrace selectedPath) ≤ _
  rw [ResourcePool.ofList_append]
  cases value with
  | bit value =>
      cases value
      · change (scopedMultiply (model := model) (wordRead output) (wordRead output) modulus
        output).resourcePool
          squarePath + 0 ≤ _
        rw [nativePower_scopedMultiply_pool, add_zero]
        exact le_self_add
      · change (scopedMultiply (model := model) (wordRead output) base modulus
          output).Path at selectedPath
        change (scopedMultiply (model := model) (wordRead output) (wordRead output) modulus
          output).resourcePool
          squarePath + (scopedMultiply (model := model) (wordRead output) base modulus
            output).resourcePool
            selectedPath ≤ _
        rw [nativePower_scopedMultiply_pool, nativePower_scopedMultiply_pool]
        exact le_rfl

/-- All actual branches of the finite fold fit the explicit per-slot coordinate allowance. -/
lemma nativePower_fold_pool_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit)) :
    ∀ path : (foldBits (model := model) base modulus output bits).Path,
      (foldBits (model := model) base modulus output bits).resourcePool path ≤
        ResourcePool.scale bits.length (bitEnvelope model width) := by
  induction bits with
  | nil => intro path; exact le_rfl
  | cons bit rest ih =>
      intro path
      change ResourcePool.ofList
        ((bitCircuit (model := model) base modulus output bit).eventTrace path.1 ++
          (foldBits (model := model) base modulus output rest).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      simp only [List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (nativePower_bit_pool_le base modulus output bit path.1) (ih path.2)

/-- Each source-addressed exponent uses its declared width in the independent budget. -/
lemma nativePower_exponent_pool_le {exponentWidth : Nat}
    (base : CInputRef ctx (.unsignedWord width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (exponentCircuit (model := model) base exponent modulus output).Path) :
    (exponentCircuit (model := model) base exponent modulus output).resourcePool path ≤
      exponentEnvelope model width exponentWidth := by
  simpa only [exponentCircuit, exponentEnvelope, List.length_ofFn] using
    nativePower_fold_pool_le base modulus output
      (List.ofFn (fun index : Fin exponentWidth => CInputRef.wordBitGet exponent index)) path

/-- The two actual scopes visit only the parent, product and division contexts. -/
lemma nativePower_scopedMultiply_visited
    (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (scopedMultiply (model := model) left right modulus output).Path) (visited :
      RuntimeCtx model.kind)
    (present : visited ∈ (scopedMultiply (model := model) left right modulus
      output).visitedContexts path) :
    visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width] := by
  change visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width, divisionCtx ctx width,
    divisionCtx ctx width, productCtx ctx width, ctx] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present ⊢
  tauto

/-- Either selected bit path reuses the same two scratch cells. -/
lemma nativePower_bit_visited (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (path : (bitCircuit (model := model) base modulus output bit).Path) (visited : RuntimeCtx
      model.kind)
    (present : visited ∈ (bitCircuit (model := model) base modulus output bit).visitedContexts
      path) :
    visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width] := by
  rcases path with ⟨squarePath, value, selectedPath⟩
  change visited ∈
    (scopedMultiply (model := model) (wordRead output) (wordRead output) modulus
      output).visitedContexts
        squarePath ++
      (multiplyChoice (model := model) base modulus output value).visitedContexts selectedPath
        at present
  rcases List.mem_append.mp present with square | selected
  · exact nativePower_scopedMultiply_visited _ _ _ _ squarePath visited square
  · cases value with
    | bit value =>
        cases value
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp selected))
        · exact nativePower_scopedMultiply_visited _ _ _ _ selectedPath visited selected

/-- No iteration retains a prior iteration's scratch cells. -/
lemma nativePower_fold_visited (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit)) :
    ∀ (path : (foldBits (model := model) base modulus output bits).Path) (visited : RuntimeCtx
      model.kind),
      visited ∈ (foldBits (model := model) base modulus output bits).visitedContexts path →
        visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width] := by
  induction bits with
  | nil =>
      intro path visited present
      exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp present))
  | cons bit rest ih =>
      intro path visited present
      change visited ∈ (bitCircuit (model := model) base modulus output bit).visitedContexts
        path.1 ++
        (foldBits (model := model) base modulus output rest).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | later
      · exact nativePower_bit_visited base modulus output bit path.1 visited first
      · exact ih path.2 visited later

private lemma resident_of_multiply_context {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (visited : RuntimeCtx kind)
    (member : visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width]) :
    visited.residentSpace ≤ ctx.residentSpace + additionalSpace kind width := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;> simp [additionalSpace, productCtx, divisionCtx, divisionShape,
      SpacePool.ofShape] <;> omega

private lemma auxiliary_of_multiply_context {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (visited : RuntimeCtx kind)
    (member : visited ∈ [ctx, productCtx ctx width, divisionCtx ctx width]) :
    visited.auxiliarySpace ≤ ctx.auxiliarySpace + additionalSpace kind width := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;> simp [additionalSpace, productCtx, divisionCtx, divisionShape,
      SpacePool.ofShape] <;> omega

/-- Peak resident capacity includes both actual scratch cells and every parent entry. -/
lemma nativePower_fold_resident_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (path : (foldBits (model := model) base modulus output bits).Path) :
    (foldBits (model := model) base modulus output bits).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace model.kind width := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact resident_of_multiply_context ctx width visited
    (nativePower_fold_visited base modulus output bits path visited present)

/-- All actual extra cells are auxiliary; the original storage roles stay unchanged. -/
lemma nativePower_fold_auxiliary_le (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (path : (foldBits (model := model) base modulus output bits).Path) :
    (foldBits (model := model) base modulus output bits).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace model.kind width := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact auxiliary_of_multiply_context ctx width visited
    (nativePower_fold_visited base modulus output bits path visited present)

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower

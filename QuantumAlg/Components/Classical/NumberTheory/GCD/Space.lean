/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete live storage of the actual GCD schedule

The actual peak includes the retained result word, two lexical state words,
the stored branch bit and the active branch's quotient/remainder pair. Thus
the independent additional allowance is `5 * width + 1` classical bits.
Every quantum-system coordinate keeps precisely its original allowance.
Inactive branches allocate no division pair; the bound also covers width zero.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual temporary pair context, entered only by a selected remainder operation. -/
def divisionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh

/-- Independent extra classical capacity of the retained result and all simultaneously live work. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (5 * width + 1))

private theorem workspace_visited {key : StorageKey} {shape : CShape}
    {fresh : key ∉ ctx.keys}
    (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (path : (Circuit.workspace ctx key shape fresh body).Path)
    (property : RuntimeCtx kind → Prop) (parent : property ctx)
    (inner : ∀ visited ∈ body.visitedContexts path, property visited)
    (visited : RuntimeCtx kind)
    (present : visited ∈ (Circuit.workspace ctx key shape fresh body).visitedContexts path) :
    property visited := by
  change visited ∈ ctx :: body.visitedContexts path ++ [ctx] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (same | member) | same
  · exact same.symm ▸ parent
  · exact inner visited member
  · exact same.symm ▸ parent

private theorem guarded_visited (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (guardedRemainder first second zero active).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (guardedRemainder first second zero active).visitedContexts path) :
    visited = ctx ∨ visited = divisionCtx ctx width := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Or.inl (List.mem_singleton.mp present)
      · have actual : visited ∈ [ctx] ++
            (List.replicate 5 (divisionCtx ctx width) ++ [ctx]) := present
        rcases List.mem_append.mp actual with original | rest
        · exact Or.inl (List.mem_singleton.mp original)
        · rcases List.mem_append.mp rest with inner | original
          · exact Or.inr (List.eq_of_mem_replicate inner)
          · exact Or.inl (List.mem_singleton.mp original)

private theorem loop_visited (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) (path : (Circuit.iterate count (guardedRemainder first second zero active)).Path)
    (visited : RuntimeCtx kind)
    (present : visited ∈
      (Circuit.iterate count (guardedRemainder first second zero active)).visitedContexts path) :
    visited = ctx ∨ visited = divisionCtx ctx width := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin count =>
    (guardedRemainder first second zero active).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with same | inner
  · exact Or.inl same
  · rcases List.mem_flatten.mp inner with ⟨contexts, listed, member⟩
    rcases List.mem_ofFn.mp listed with ⟨index, rfl⟩
    exact guarded_visited first second zero active (path index) visited member

private theorem scheduled_visited (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (path : (scheduledBody input first second active result).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (scheduledBody input first second active result).visitedContexts path) :
    visited = ctx ∨ visited = divisionCtx ctx width := by
  change visited ∈ [ctx, ctx, ctx, ctx] ++
    ((Circuit.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedRemainder first second (cellRead result) active)).visitedContexts path.2.1 ++ [ctx])
    at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at present
  rcases present with original | inner | original
  · exact Or.inl original
  · exact loop_visited first second (cellRead result) active _ path.2.1 visited inner
  · exact Or.inl original

private theorem lexical_visited (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width))
    (path : (lexicalBody input result).Path) (property : RuntimeCtx kind → Prop)
    (base : property ctx) (current : property (currentCtx ctx width))
    (previous : property (previousCtx ctx width)) (loop : property (loopCtx ctx width))
    (division : property (divisionCtx (loopCtx ctx width) width)) (visited : RuntimeCtx kind)
    (present : visited ∈ (lexicalBody input result).visitedContexts path) : property visited := by
  exact workspace_visited (ctx := ctx) _ path property base
    (fun atCurrent inCurrent =>
      workspace_visited (ctx := currentCtx ctx width) _ path property current
        (fun atPrevious inPrevious =>
          workspace_visited (ctx := previousCtx ctx width) _ path property previous
            (fun atLoop inLoop => by
              rcases scheduled_visited (underLoop input width) (currentCell ctx width)
                (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
                path atLoop inLoop with same | same
              · exact same.symm ▸ loop
              · exact same.symm ▸ division)
            atPrevious inPrevious)
        atCurrent inCurrent)
    visited present

/-- Every real context belongs to the six actual allocation stages of this circuit. -/
theorem gcdRetained_visited (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (retainedCircuit input key fresh).visitedContexts path) :
    visited ∈ [ctx, retainedCtx ctx width key fresh,
      currentCtx (retainedCtx ctx width key fresh) width,
      previousCtx (retainedCtx ctx width key fresh) width,
      loopCtx (retainedCtx ctx width key fresh) width,
      divisionCtx (loopCtx (retainedCtx ctx width key fresh) width) width] := by
  change visited ∈ [ctx, retainedCtx ctx width key fresh] ++
    (lexicalBody (input.underRetained key (.unsignedWord width) fresh)
      (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with allocation | execution
  · rcases List.mem_cons.mp allocation with same | same
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp same)))
  · exact lexical_visited (input.underRetained key (.unsignedWord width) fresh)
      (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) path.2
      (fun candidate => candidate ∈ _) (by simp [retainedCtx]) (by simp [retainedCtx])
      (by simp [retainedCtx]) (by simp [retainedCtx]) (by simp [retainedCtx])
      visited execution

/-- Resident capacity counts the result, two state words, condition and temporary division pair. -/
theorem gcdRetained_resident_le (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace kind width := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have member := gcdRetained_visited input key fresh path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [additionalSpace, retainedCtx, currentCtx, previousCtx, loopCtx, divisionCtx,
        operandShape, SpacePool.ofShape] <;> omega

/-- The same actual allocations all count as auxiliary storage, including the retained result. -/
theorem gcdRetained_auxiliary_le (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace kind width := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have member := gcdRetained_visited input key fresh path visited present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro axis
    cases axis <;>
      simp [additionalSpace, retainedCtx, currentCtx, previousCtx, loopCtx, divisionCtx,
        operandShape, SpacePool.ofShape] <;> omega

/-- Independent capacity for the two state words, branch flag and live division pair. -/
def lexicalAdditionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (4 * width + 1))

/-- The lexical GCD counts all live work while its caller already owns the result cell. -/
theorem gcdLexical_resident_le (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (path : (lexicalBody input result).Path) :
    (lexicalBody input result).peakResidentSpace path ≤
      ctx.residentSpace + lexicalAdditionalSpace kind width := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  refine lexical_visited input result path
    (fun candidate => candidate.residentSpace ≤ ctx.residentSpace +
      lexicalAdditionalSpace kind width) ?_ ?_ ?_ ?_ ?_ visited present
  all_goals
    intro axis
    cases axis <;>
      simp [lexicalAdditionalSpace, currentCtx, previousCtx, loopCtx, divisionCtx,
        operandShape, SpacePool.ofShape] <;> omega

/-- All actual lexical GCD work contributes to the same additional auxiliary allowance. -/
theorem gcdLexical_auxiliary_le (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (path : (lexicalBody input result).Path) :
    (lexicalBody input result).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + lexicalAdditionalSpace kind width := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  refine lexical_visited input result path
    (fun candidate => candidate.auxiliarySpace ≤ ctx.auxiliarySpace +
      lexicalAdditionalSpace kind width) ?_ ?_ ?_ ?_ ?_ visited present
  all_goals
    intro axis
    cases axis <;>
      simp [lexicalAdditionalSpace, currentCtx, previousCtx, loopCtx, divisionCtx,
        operandShape, SpacePool.ofShape] <;> omega

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD

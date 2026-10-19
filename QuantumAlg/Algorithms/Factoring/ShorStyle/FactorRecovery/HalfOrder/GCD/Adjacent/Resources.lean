/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual resources of adjacent half-power arithmetic

Both directions widen the stored word and apply their own native adjacent
instruction. Only the predecessor can additionally execute a real self-XOR
when its stored underflow bit selects that arm. These are respectively two
and at most three serial native events, with no added live storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width : Nat}

/-- Independent native coordinates for widening, the chosen direction and possible trimming. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (successor : Bool) (width :
  Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + 1)))) +
    (ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model) (.wordUnary (if successor then .increment
        else .decrement) (width + 1)))) +
      if successor then 0 else
        ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution :=
          model) (.wordBinary .bitXor (width + 1)))))

private lemma trim_pool_le (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim (model := model) output).Path) :
    (trim (model := model) output).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor (width + 1)))) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact zero_le
      · change (BitWord.instruction (execution := model) (clearOp output)).Path at path
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (clearOp output)).eventTrace path) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        exact le_rfl

private lemma tail_pool_le (successor : Bool)
    (output : CWriteRef ctx (.unsignedWord (width + 1))) (path : (tail (model := model) successor
      output).Path) :
    (tail (model := model) successor output).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation
        (BitWord.selectedCoordinate (execution := model) (.wordUnary (if successor then .increment
          else .decrement) (width + 1)))) +
        if successor then 0 else
          ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution :=
            model) (.wordBinary .bitXor (width + 1)))) := by
  cases successor
  · change ((BitWord.instruction (execution := model) (adjacentOp false output)).seq
      (trim (model := model) output)).Path at path
    change ResourcePool.ofList
      ((BitWord.instruction (execution := model) (adjacentOp false output)).eventTrace path.1 ++
        (trim (model := model) output).eventTrace path.2) ≤ _
    rw [ResourcePool.ofList_append, BitWord.bitWord_instruction_eventTrace]
    exact add_le_add le_rfl (trim_pool_le output path.2)
  · change (BitWord.instruction (execution := model) (adjacentOp true output)).Path at path
    change ResourcePool.ofList
      ((BitWord.instruction (execution := model) (adjacentOp true output)).eventTrace path) ≤ _
    rw [BitWord.bitWord_instruction_eventTrace]
    exact (add_zero _).symm.le

/-- Every actual path fits the direction's independent native coordinate allowance. -/
lemma code_pool_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code (model := model) successor input output).Path) :
    (code (model := model) successor input output).resourcePool path ≤ eventEnvelope model
      successor width := by
  change ResourcePool.ofList ((code (model := model) successor input output).eventTrace path) ≤ _
  rw [code_eventTrace, ResourcePool.ofList_cons]
  exact add_le_add le_rfl (tail_pool_le successor output path.2)

private lemma trim_unitDepth_le (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim (model := model) output).Path) : (trim (model := model) output).depth (fun _ =>
      1) path ≤ 1 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact le_rfl

/-- The genuine successor has two serial events and the predecessor has at most three. -/
lemma code_unitDepth_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code (model := model) successor input output).Path) :
    (code (model := model) successor input output).depth (fun _ => 1) path ≤ if successor then 2
      else 3 := by
  cases successor
  · change 1 + (1 + (trim (model := model) output).depth (fun _ => 1) path.2.2) ≤ 3
    have actual := trim_unitDepth_le (model := model) output path.2.2
    omega
  · exact le_rfl

private lemma trim_visited (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim (model := model) output).Path) : (trim (model := model) output).visitedContexts
      path = [ctx] := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Every actually visited context is the original context, including the selected trim arm. -/
lemma code_visited (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code (model := model) successor input output).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (code (model := model) successor input output).visitedContexts path) :
      visited = ctx := by
  cases successor
  · change visited ∈ [ctx, ctx] ++ (trim (model := model) output).visitedContexts path.2.2
      at present
    rw [trim_visited] at present
    change visited ∈ [ctx, ctx, ctx] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  · change visited ∈ [ctx, ctx] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- Adjacent arithmetic uses only the resident cells already present in its real input context. -/
lemma code_resident_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code (model := model) successor input output).Path) :
    (code (model := model) successor input output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (code_visited successor input output path visited present) ▸ le_rfl

/-- The same actual trace introduces no auxiliary cells beyond its original frame. -/
lemma code_auxiliary_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code (model := model) successor input output).Path) :
    (code (model := model) successor input output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
      by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (code_visited successor input output path visited present) ▸ le_rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

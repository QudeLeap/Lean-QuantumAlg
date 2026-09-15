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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native coordinates for widening, the chosen direction and possible trimming. -/
def eventEnvelope (kind : ProblemKind) (successor : Bool) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordResize width (width + 1))) +
    (ResourcePool.singleton (.classicalOperation
      (.wordUnary (if successor then .increment else .decrement) (width + 1))) +
      if successor then 0 else
        ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor (width + 1))))

private theorem trim_pool_le (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim output).Path) :
    (trim output).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor (width + 1))) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact zero_le
      · exact le_rfl

private theorem tail_pool_le (successor : Bool)
    (output : CWriteRef ctx (.unsignedWord (width + 1))) (path : (tail successor output).Path) :
    (tail successor output).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation
        (.wordUnary (if successor then .increment else .decrement) (width + 1))) +
        if successor then 0 else
          ResourcePool.singleton (.classicalOperation (.wordBinary .bitXor (width + 1))) := by
  cases successor
  · change ResourcePool.singleton (.classicalOperation (.wordUnary .decrement (width + 1))) +
      (trim output).resourcePool path.2 ≤ _
    exact add_le_add le_rfl (trim_pool_le output path.2)
  · exact (add_zero _).symm.le

/-- Every actual path fits the direction's independent native coordinate allowance. -/
theorem code_pool_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) :
    (code successor input output).resourcePool path ≤ eventEnvelope kind successor width := by
  change ResourcePool.singleton (.classicalOperation (.wordResize width (width + 1))) +
    (tail successor output).resourcePool path.2 ≤ _
  exact add_le_add le_rfl (tail_pool_le successor output path.2)

private theorem trim_unitDepth_le (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim output).Path) : (trim output).depth (fun _ => 1) path ≤ 1 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact le_rfl

/-- The genuine successor has two serial events and the predecessor has at most three. -/
theorem code_unitDepth_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) :
    (code successor input output).depth (fun _ => 1) path ≤ if successor then 2 else 3 := by
  cases successor
  · change 1 + (1 + (trim output).depth (fun _ => 1) path.2.2) ≤ 3
    have actual := trim_unitDepth_le output path.2.2
    omega
  · exact le_rfl

private theorem trim_visited (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (trim output).Path) : (trim output).visitedContexts path = [ctx] := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value => cases value <;> rfl

/-- Every actually visited context is the original context, including the selected trim arm. -/
theorem code_visited (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (code successor input output).visitedContexts path) : visited = ctx := by
  cases successor
  · change visited ∈ [ctx, ctx] ++ (trim output).visitedContexts path.2.2 at present
    rw [trim_visited] at present
    change visited ∈ [ctx, ctx, ctx] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  · change visited ∈ [ctx, ctx] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- Adjacent arithmetic uses only the resident cells already present in its real input context. -/
theorem code_resident_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) :
    (code successor input output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (code_visited successor input output path visited present) ▸ le_rfl

/-- The same actual trace introduces no auxiliary cells beyond its original frame. -/
theorem code_auxiliary_le (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) :
    (code successor input output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (code_visited successor input output path visited present) ▸ le_rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

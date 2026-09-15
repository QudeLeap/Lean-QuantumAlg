/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Construction
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Independent native event budget of the actual square root

Every round contributes an addition, full multiplication, comparison and
right shift, together with a copy only on the accepted arm. The literal
increment loader has its independent two-event allowance per input bit.
The actual widening and final copy are also charged. Thus the independent
coordinatewise envelope has cardinality `7 * width + 2`; no square-root
opcode, quantum oracle or synthetic padding event appears in the circuit.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The three unconditional arithmetic coordinates preceding actual selection. -/
def roundPrefixEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .add width),
    .classicalOperation (.mulFull width width),
    .classicalOperation (.wordBinary .lessThan (width + width))]

/-- Independent coordinate allowance for either actual selected refinement path. -/
def roundEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (roundPrefixEvents kind width) +
    (ResourcePool.singleton (.classicalOperation (.wordUnary .copy width)) +
      ResourcePool.singleton (.classicalOperation (.wordUnary .shiftRight width)))

/-- Independent native budget for initialization, all rounds and the final copy. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.singleton (.classicalOperation (.wordResize width (width + width))) +
    (ConstantWord.envelope kind width +
      (ResourcePool.scale width (roundEnvelope kind width) +
        ResourcePool.singleton (.classicalOperation (.wordUnary .copy width))))

/-- Actual conditional selection charges precisely zero or one native word copy. -/
theorem nativeSqrt_select_pool_le (refs : RoundRefs ctx width) (path : (select refs).Path) :
    (select refs).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation (.wordUnary .copy width)) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit flag =>
      cases flag
      · exact le_rfl
      · exact zero_le

/-- Every actual round fits the five real operation coordinates at their declared widths. -/
theorem nativeSqrt_round_pool_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (path : (round input refs).Path) :
    (round input refs).resourcePool path ≤ roundEnvelope kind width := by
  change ResourcePool.ofList (roundPrefixEvents kind width ++
    ((select refs).eventTrace path.2.2.2.1 ++
      [.classicalOperation (.wordUnary .shiftRight width)])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl
    (add_le_add (nativeSqrt_select_pool_le refs path.2.2.2.1) le_rfl)

/-- The real finite iteration spends at most one round allowance at each actual index. -/
theorem nativeSqrt_iteration_pool_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) :
    ∀ path : (Circuit.iterate count (round input refs)).Path,
      (Circuit.iterate count (round input refs)).resourcePool path ≤
        ResourcePool.scale count (roundEnvelope kind width) := by
  induction count with
  | zero => intro path; exact le_rfl
  | succ count inductionHypothesis =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (round input refs).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (nativeSqrt_round_pool_le input refs (path 0))
        (inductionHypothesis (fun index => path index.succ))

/-- The actual initialized body includes both its initial widening and its final caller copy. -/
theorem nativeSqrt_body_pool_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (body input output).Path) :
    (body input output).resourcePool path ≤ nativeEnvelope kind width := by
  change ResourcePool.ofList
    ([.classicalOperation (.wordResize width (width + width))] ++
      ((ConstantWord.circuit (halfCell ctx width) (initialHalf width)).eventTrace path.2.1 ++
        ((rounds ctx width).eventTrace path.2.2.1 ++
          [.classicalOperation (.wordUnary .copy width)]))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (ConstantWord.constantWord_pool_le (halfCell ctx width) (initialHalf width) path.2.1)
    (add_le_add (nativeSqrt_iteration_pool_le
      (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width) width path.2.2.1) le_rfl))

/-- Every lexical scope is accounted for by its actual body; it emits no hidden arithmetic. -/
theorem nativeSqrt_into_pool_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path) :
    (into input output).resourcePool path ≤ nativeEnvelope kind width :=
  nativeSqrt_body_pool_le input output path

/-- The independent envelope has the explicit linear total-event allowance at every width. -/
theorem nativeSqrt_nativeEnvelope_card (kind : ProblemKind) (width : Nat) :
    (nativeEnvelope kind width).card = 7 * width + 2 := by
  simp [nativeEnvelope, roundEnvelope, roundPrefixEvents,
    ConstantWord.envelope, ConstantWord.bitEnvelope,
    ResourcePool.singleton, ResourcePool.scale, ResourcePool.ofList]
  omega

/-- Actual paths, including width zero, obey the total-event bound of the native ledger. -/
theorem nativeSqrt_into_eventCount_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into input output).Path) :
    ((into input output).resourcePool path).card ≤ 7 * width + 2 :=
  (Multiset.card_le_card (nativeSqrt_into_pool_le input output path)).trans_eq
    (nativeSqrt_nativeEnvelope_card kind width)

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

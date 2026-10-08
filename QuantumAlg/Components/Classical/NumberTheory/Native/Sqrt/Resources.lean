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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The three unconditional arithmetic coordinates preceding actual selection. -/
def roundPrefixEvents (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .add width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.mulFull width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .lessThan
      (width + width)))]

/-- Independent coordinate allowance for either actual selected refinement path. -/
def roundEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.ofList (roundPrefixEvents (model := model) width) +
    (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width))) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .shiftRight width))))

/-- Independent native budget for initialization, all rounds and the final copy. -/
def nativeEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize width (width + width)))) +
    (ConstantWord.envelope (model := model) width +
      (ResourcePool.scale width (roundEnvelope (model := model) width) +
        ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution :=
          model) (.wordUnary .copy width)))))

/-- Actual conditional selection charges precisely zero or one native word copy. -/
theorem nativeSqrt_select_pool_le (refs : RoundRefs ctx width) (path : (select (model := model)
  refs).Path) :
    (select (model := model) refs).resourcePool path ≤
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .copy width))) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit flag =>
      cases flag
      · change (BitWord.instruction (execution := model) (copyOp refs)).Path at path
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (copyOp refs)).eventTrace path) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        exact le_rfl
      · exact zero_le

/-- Every actual round fits the five real operation coordinates at their declared widths. -/
theorem nativeSqrt_round_pool_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (path : (round (model := model) input refs).Path) :
    (round (model := model) input refs).resourcePool path ≤ roundEnvelope (model := model) width :=
      by
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (addOp refs)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model) (squareOp refs)).eventTrace path.2.1 ++
        ((BitWord.instruction (execution := model) (compareOp input refs)).eventTrace path.2.2.1 ++
          ((select (model := model) refs).eventTrace path.2.2.2.1 ++
            (BitWord.instruction (execution := model) (shiftOp refs)).eventTrace path.2.2.2.2)))) ≤
              _
  simp only [BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList (roundPrefixEvents (model := model) width ++
    ((select (model := model) refs).eventTrace path.2.2.2.1 ++
      [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .shiftRight
        width))])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl
    (add_le_add (nativeSqrt_select_pool_le refs path.2.2.2.1) le_rfl)

/-- The real finite iteration spends at most one round allowance at each actual index. -/
theorem nativeSqrt_iteration_pool_le
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) :
    ∀ path : (Circuit.iterate count (round (model := model) input refs)).Path,
      (Circuit.iterate count (round (model := model) input refs)).resourcePool path ≤
        ResourcePool.scale count (roundEnvelope (model := model) width) := by
  induction count with
  | zero => intro path; exact le_rfl
  | succ count inductionHypothesis =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (round (model := model) input refs).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (nativeSqrt_round_pool_le input refs (path 0))
        (inductionHypothesis (fun index => path index.succ))

/-- The actual initialized body includes both its initial widening and its final caller copy. -/
theorem nativeSqrt_body_pool_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (body (model := model) input
      output).Path) :
    (body (model := model) input output).resourcePool path ≤ nativeEnvelope (model := model) width
      := by
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (widenOp input)).eventTrace path.1 ++
      ((ConstantWord.circuit (model := model) (halfCell ctx width)
        (initialHalf width)).eventTrace path.2.1 ++
        ((rounds (model := model) ctx width).eventTrace path.2.2.1 ++
          (BitWord.instruction (execution := model) (finishOp output)).eventTrace path.2.2.2))) ≤ _
  simp only [BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList
    ([.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize width
      (width + width)))] ++
      ((ConstantWord.circuit (model := model) (halfCell ctx width) (initialHalf width)).eventTrace
        path.2.1 ++
        ((rounds (model := model) ctx width).eventTrace path.2.2.1 ++
          [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy
            width))]))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (ConstantWord.constantWord_pool_le (halfCell ctx width) (initialHalf width) path.2.1)
    (add_le_add (nativeSqrt_iteration_pool_le
      (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width) width path.2.2.1) le_rfl))

/-- Every lexical scope is accounted for by its actual body; it emits no hidden arithmetic. -/
theorem nativeSqrt_into_pool_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) input
      output).Path) :
    (into (model := model) input output).resourcePool path ≤ nativeEnvelope (model := model) width
      :=
  nativeSqrt_body_pool_le input output path

/-- The independent envelope has the explicit linear total-event allowance at every width. -/
theorem nativeSqrt_nativeEnvelope_card (width : Nat) :
    (nativeEnvelope (model := model) width).card = 7 * width + 2 := by
  simp [nativeEnvelope, roundEnvelope, roundPrefixEvents,
    ConstantWord.envelope, ConstantWord.bitEnvelope,
    ResourcePool.singleton, ResourcePool.scale, ResourcePool.ofList]
  omega

/-- Actual paths, including width zero, obey the total-event bound of the native ledger. -/
theorem nativeSqrt_into_eventCount_le (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (path : (into (model := model) input
      output).Path) :
    ((into (model := model) input output).resourcePool path).card ≤ 7 * width + 2 :=
  (Multiset.card_le_card (nativeSqrt_into_pool_le input output path)).trans_eq
    (nativeSqrt_nativeEnvelope_card (model := model) width)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

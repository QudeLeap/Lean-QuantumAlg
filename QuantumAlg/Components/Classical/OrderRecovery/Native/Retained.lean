/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Correctness
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Preservation
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Resources
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Space
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Retained native continued-fraction recovery

One actual allocation supplies the option result. The borrowed base and phase
sample are lifted structurally across that allocation, then the complete native
recovery writes the real result before releasing its thirteen cursor fields.
The store equation keeps arbitrary initial histories and external references.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {modulusWidth phaseBits : Nat}

/-- Allocate the actual optional word and execute native recovery into that cell. -/
def retainedCircuit (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit model ctx (ctx.addRetained key (outputShape phaseBits) fresh) :=
  .seq (.retain ctx key (outputShape phaseBits) fresh)
    (into (model := model) spec
      (.first (input.underRetained key (outputShape phaseBits) fresh))
      (.second (input.underRetained key (outputShape phaseBits) fresh))
      (CWriteRef.retainedHead ctx key (outputShape phaseBits) fresh))

/-- Retaining the result emits no arithmetic event beyond the independent native allowance. -/
lemma nativeRecovery_retained_pool_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit (model := model) spec input key fresh).Path) :
    (retainedCircuit (model := model) spec input key fresh).resourcePool path ≤
      eventEnvelope model modulusWidth phaseBits := by
  exact nativeRecovery_into_pool_le spec _ _ _ path.2

/-- The retained option and reused recovery workspace are counted in resident storage. -/
lemma nativeRecovery_retained_resident_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit (model := model) spec input key fresh).Path) :
    (retainedCircuit (model := model) spec input key fresh).peakResidentSpace path ≤
      (ctx.addRetained key (outputShape phaseBits) fresh).residentSpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  change visited ∈ [ctx, ctx.addRetained key (outputShape phaseBits) fresh] ++ _ at present
  rcases List.mem_append.mp present with allocation | recovery
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at allocation
    rcases allocation with rfl | rfl
    all_goals intro axis; cases model <;> cases axis <;> simp [SpacePool.ofShape] <;> omega
  · exact (nativeRecovery_into_visited_space_le spec _ _ _ path.2 visited recovery).1

/-- The actual result remains auxiliary storage after the temporary fields have been released. -/
lemma nativeRecovery_retained_auxiliary_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit (model := model) spec input key fresh).Path) :
    (retainedCircuit (model := model) spec input key fresh).peakAuxiliarySpace path ≤
      (ctx.addRetained key (outputShape phaseBits) fresh).auxiliarySpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  change visited ∈ [ctx, ctx.addRetained key (outputShape phaseBits) fresh] ++ _ at present
  rcases List.mem_append.mp present with allocation | recovery
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at allocation
    rcases allocation with rfl | rfl
    all_goals intro axis; cases model <;> cases axis <;> simp [SpacePool.ofShape] <;> omega
  · exact (nativeRecovery_into_visited_space_le spec _ _ _ path.2 visited recovery).2

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The store and actual path produced by allocation and the same complete native recovery. -/
def retainedStep (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx) :
    Store (ctx.addRetained key (outputShape phaseBits) fresh) ×
      (retainedCircuit (model := model) spec input key fresh).Path :=
  let recovered := intoStep (model := model) spec
    (.first (input.underRetained key (outputShape phaseBits) fresh))
    (.second (input.underRetained key (outputShape phaseBits) fresh))
    (CWriteRef.retainedHead ctx key (outputShape phaseBits) fresh)
    (store.pushRetained key (outputShape phaseBits) fresh)
  (recovered.1, ((), recovered.2))

/-- Every complete density block follows the actual retained store and path. -/
lemma nativeRecovery_retained_execute
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState
      × History)) :
    (retainedCircuit (model := model) spec input key fresh).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((retainedStep (model := model) spec input key fresh entry.1).1,
          (entry.2.1, (entry.2.2, (retainedStep (model := model) spec input key fresh
            entry.1).2)))) := by
  simp only [retainedCircuit, Circuit.execute_seq, Circuit.execute_retain,
    nativeRecovery_into_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def, retainedStep]
  congr 1
  exact Subsingleton.elim _ _

/-- The real retained option is precisely the first accepted source denominator, or none. -/
lemma nativeRecovery_retained_result
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (source : ClassicalAlgorithms.OrderRecovery.Input spec)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx)
    (represented : store.read input = encodeInput source) :
    (retainedStep (model := model) spec input key fresh store).1.read
      (cellRead (CWriteRef.retainedHead ctx key (outputShape phaseBits) fresh)) =
        encodeOutput (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder spec source) := by
  apply nativeRecovery_into_result spec source
  · change ((store.pushRetained key (outputShape phaseBits) fresh).read
      (input.underRetained key (outputShape phaseBits) fresh)).first = _
    rw [Store.read_pushRetained_underRetained, represented]
    rfl
  · change ((store.pushRetained key (outputShape phaseBits) fresh).read
      (input.underRetained key (outputShape phaseBits) fresh)).second = _
    rw [Store.read_pushRetained_underRetained, represented]
    rfl

/-- Allocation and native recovery jointly restore all borrowed data with every reference. -/
lemma nativeRecovery_retained_borrowedRestored
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : CInputRef ctx (inputShape modulusWidth phaseBits))
    (key : StorageKey) (fresh : key ∉ ctx.keys) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState
      × History)) :
    (retainedCircuit (model := model) spec input key fresh).BorrowedRestored Reference state
      ((retainedCircuit (model := model) spec input key fresh).execute
      environment Reference state) := by
  unfold retainedCircuit
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact Circuit.borrowedRestored_retain
      (environment := environment) key (outputShape phaseBits) fresh state
  · exact nativeRecovery_into_borrowedRestored spec _ _ _ Reference _

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

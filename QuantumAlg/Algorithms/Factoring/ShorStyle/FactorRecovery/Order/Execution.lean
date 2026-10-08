/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Branches
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution

/-!
# Actual stored-base order recovery feeds the factor dispatch

The same actual parameter and measured phase references feed the existing
native order-recovery program. The resulting stored optional word is decoded
by its real nominal instruction before the actual priority branches execute.
All equations preserve complete quantum-reference blocks and genuine paths.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The actual optional-word unpack precedes the same real stored-flag dispatch. -/
def unpackedDispatchStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (BitWord.instruction (execution := model) (unpackOrderOp cells))
      (dispatch (model := model) source parameter cells output)).Path :=
  let unpacked := BitWord.instructionStep (execution := model) (unpackOrderOp cells) store
  let selected := dispatchStep (model := model) source parameter cells output unpacked.1
  (selected.1, (unpacked.2, selected.2))

/-- The real order-recovery record feeds the actual optional-word decode and factor dispatch. -/
def recoveryTailStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq
      (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
          cells.base.toCStorageRef)
        phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells)) (dispatch (model :=
          model) source parameter cells output))).Path :=
  let recovered := OrderRecovery.Native.intoStep (model := model) (recoverySpec source)
    (.storage cells.base.toCStorageRef) phase cells.order store
  let selected := unpackedDispatchStep (model := model) source parameter cells output recovered.1
  (selected.1, (recovered.2, selected.2))

/-- The complete non-exceptional record starts with the actual stored sampler-base pack. -/
def recoveredStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (recovered (model := model) source parameter phase cells output).Path :=
  let packed := BitWord.instructionStep (execution := model) (packBaseOp parameter cells) store
  let selected := recoveryTailStep (model := model) source parameter phase cells output packed.1
  (selected.1, (packed.2, selected.2))

private theorem unpackedDispatch_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (BitWord.instruction (execution := model) (unpackOrderOp cells))
      (dispatch (model := model) source parameter cells output)).execute Reference state =
      state.mapClassical (fun entry =>
        ((unpackedDispatchStep (model := model) source parameter cells output entry.1).1,
          (entry.2.1, (entry.2.2, (unpackedDispatchStep (model := model) source parameter cells
              output entry.1).2)))) := by
  rw [Circuit.execute_seq, dispatch_execute, BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private theorem recoveryTail_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq
      (OrderRecovery.Native.into (model := model) (recoverySpec source) (.storage
          cells.base.toCStorageRef)
        phase cells.order)
      (.seq (BitWord.instruction (execution := model) (unpackOrderOp cells))
        (dispatch (model := model) source parameter cells output))).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryTailStep (model := model) source parameter phase cells output entry.1).1,
          (entry.2.1, (entry.2.2, (recoveryTailStep (model := model) source parameter phase cells
              output entry.1).2)))) := by
  rw [Circuit.execute_seq, unpackedDispatch_execute,
    OrderRecovery.Native.nativeRecovery_into_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The real complete stored-outcome recovery prefix has its actual full CQ execution record. -/
theorem recovered_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (recovered (model := model) source parameter phase cells output).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveredStep (model := model) source parameter phase cells output entry.1).1,
          (entry.2.1, (entry.2.2, (recoveredStep (model := model) source parameter phase cells
              output entry.1).2)))) := by
  unfold recovered
  rw [Circuit.execute_seq, recoveryTail_execute, BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

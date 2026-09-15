/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Branches
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics
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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual optional-word unpack precedes the same real stored-flag dispatch. -/
def unpackedDispatchStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (.classical (unpackOrderOp cells))
      (dispatch source parameter cells output)).Path :=
  let selected := dispatchStep source parameter cells output (store.applyOp (unpackOrderOp cells))
  (selected.1, ((), selected.2))

/-- The real order-recovery record feeds the actual optional-word decode and factor dispatch. -/
def recoveryTailStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq
      (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
        phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output))).Path :=
  let recovered := OrderRecovery.Native.intoStep (recoverySpec source)
    (.storage cells.base.toCStorageRef) phase cells.order store
  let selected := unpackedDispatchStep source parameter cells output recovered.1
  (selected.1, (recovered.2, selected.2))

/-- The complete non-exceptional record starts with the actual stored sampler-base pack. -/
def recoveredStep (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (recovered source parameter phase cells output).Path :=
  let selected := recoveryTailStep source parameter phase cells output
    (store.applyOp (packBaseOp parameter cells))
  (selected.1, ((), selected.2))

private theorem unpackedDispatch_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (.classical (unpackOrderOp cells))
      (dispatch source parameter cells output)).execute Reference state =
      state.mapClassical (fun entry =>
        ((unpackedDispatchStep source parameter cells output entry.1).1,
          (entry.2, (unpackedDispatchStep source parameter cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (unpackOrderOp cells))
    (dispatch source parameter cells output)
    (fun store => (store.applyOp (unpackOrderOp cells), ()))
    (dispatchStep source parameter cells output)
    (fun reference _ _ initial =>
      NativeHalfPower.classical_path_execute (unpackOrderOp cells) reference initial _)
    (dispatch_execute source parameter cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq (.classical (unpackOrderOp cells))
          (dispatch source parameter cells output)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((unpackedDispatchStep source parameter cells output entry.1).1,
          (entry.2, (unpackedDispatchStep source parameter cells output entry.1).2))))
    (Subsingleton.elim _ _)

private theorem recoveryTail_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq
      (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
        phase cells.order)
      (.seq (.classical (unpackOrderOp cells))
        (dispatch source parameter cells output))).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryTailStep source parameter phase cells output entry.1).1,
          (entry.2, (recoveryTailStep source parameter phase cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
    (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output))
    (OrderRecovery.Native.intoStep (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
    (unpackedDispatchStep source parameter cells output)
    (OrderRecovery.Native.nativeRecovery_into_execute (recoverySpec source)
      (.storage cells.base.toCStorageRef) phase cells.order)
    (unpackedDispatch_execute source parameter cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History ×
        (Circuit.seq
          (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
            phase cells.order)
          (.seq (.classical (unpackOrderOp cells))
            (dispatch source parameter cells output))).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((recoveryTailStep source parameter phase cells output entry.1).1,
          (entry.2, (recoveryTailStep source parameter phase cells output entry.1).2))))
    (Subsingleton.elim _ _)

/-- The real complete stored-outcome recovery prefix has its actual full CQ execution record. -/
theorem recovered_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (recovered source parameter phase cells output).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveredStep source parameter phase cells output entry.1).1,
          (entry.2, (recoveredStep source parameter phase cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (packBaseOp parameter cells))
    (.seq (OrderRecovery.Native.into (recoverySpec source) (.storage cells.base.toCStorageRef)
      phase cells.order)
      (.seq (.classical (unpackOrderOp cells)) (dispatch source parameter cells output)))
    (fun store => (store.applyOp (packBaseOp parameter cells), ()))
    (recoveryTailStep source parameter phase cells output)
    (fun reference _ _ initial =>
      NativeHalfPower.classical_path_execute (packBaseOp parameter cells) reference initial _)
    (recoveryTail_execute source parameter phase cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store ctx × (History × (recovered source parameter phase cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((recoveredStep source parameter phase cells output entry.1).1,
          (entry.2, (recoveredStep source parameter phase cells output entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

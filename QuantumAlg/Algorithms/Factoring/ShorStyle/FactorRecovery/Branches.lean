/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Reduction
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution

/-!
# Real stored-order and early-factor branch execution

The dependent path records below follow only the arms selected by the actual
stored guard and sampler flags. Their complete CQ equations compose the same
guard, modular-power and GCD circuits; no source outcome or mathematical
selector replaces a branch of the actual interpreter.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Record only the actual reduction or absent-option arm of the stored guard. -/
def checkedArmStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then reduce source cells output
        else Circuit.classical (packOutputOp cells output)).Path
  | .bit false, store => (store.applyOp (packOutputOp cells output), ())
  | .bit true, store => reduceStep source cells output store

/-- Select the genuine guard branch with the actual bit read from its incoming store. -/
def guardChoiceStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).Path :=
  let value := store.read (activeRead cells)
  let selected := checkedArmStep source cells output value store
  (selected.1, ⟨value, selected.2⟩)

/-- Retain the exact five-event path of the actual guard store. -/
def guardStep (cells : Cells ctx N) (store : Store ctx) :
    Store ctx × (guardOrder cells).Path :=
  (guardStore cells store, ((), ((), ((), ((), ())))))

/-- The five actual guard writes precede their actual stored-bit branch. -/
def checkedStep (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (checkedOrder source cells output).Path :=
  let guarded := guardStep cells store
  let selected := guardChoiceStep source cells output guarded.1
  (selected.1, (guarded.2, selected.2))

private theorem guard_path_execute (cells : Cells ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (guardOrder cells).execute Reference state =
      state.mapClassical (fun entry => ((guardStep cells entry.1).1,
        (entry.2, (guardStep cells entry.1).2))) := by
  refine (guard_execute cells Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (guardOrder cells).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((guardStep cells entry.1).1, (entry.2, (guardStep cells entry.1).2))))
    (Subsingleton.elim _ _)

private theorem guardChoice_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.branch (activeRead cells)
      (fun value => if value.toBool then reduce source cells output
        else .classical (packOutputOp cells output))).execute Reference state =
      state.mapClassical (fun entry => ((guardChoiceStep source cells output entry.1).1,
        (entry.2, (guardChoiceStep source cells output entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (activeRead cells)
    (fun value => if value.toBool then reduce source cells output
      else .classical (packOutputOp cells output))
    (checkedArmStep source cells output) ?_ Reference state).trans ?_
  · intro value reference history _ initial
    cases value with
    | bit value =>
      cases value
      · exact NativeHalfPower.classical_path_execute (packOutputOp cells output)
          reference initial _
      · exact reduce_execute source cells output reference initial
  · exact congrArg
      (fun decision : DecidableEq (Store ctx × (History ×
          (Circuit.branch (activeRead cells)
            (fun value => if value.toBool then reduce source cells output
              else .classical (packOutputOp cells output))).Path)) =>
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
          (fun entry => ((guardChoiceStep source cells output entry.1).1,
            (entry.2, (guardChoiceStep source cells output entry.1).2)))) (Subsingleton.elim _ _)

/-- The actual guard and reduction branch preserve every full quantum-reference block. -/
theorem checked_execute (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (checkedOrder source cells output).execute Reference state =
      state.mapClassical (fun entry => ((checkedStep source cells output entry.1).1,
        (entry.2, (checkedStep source cells output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (guardOrder cells)
    (.branch (activeRead cells) (fun value => if value.toBool then reduce source cells output
      else .classical (packOutputOp cells output)))
    (guardStep cells)
    (guardChoiceStep source cells output) (guard_path_execute cells)
    (guardChoice_execute source cells output) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store ctx × (History × (checkedOrder source cells output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
        (fun entry => ((checkedStep source cells output entry.1).1,
          (entry.2, (checkedStep source cells output entry.1).2)))) (Subsingleton.elim _ _)

/-- Record the actual early-factor pack or the actual order-guard suffix. -/
def dispatchArmStep (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (value : CShape.Value .bit) → Store ctx → Store ctx ×
      (if value.toBool then Circuit.classical (packEarlyOp parameter output)
        else checkedOrder source cells output).Path
  | .bit false, store => checkedStep source cells output store
  | .bit true, store => (store.applyOp (packEarlyOp parameter output), ())

/-- Read the real sampler flag and preserve the path of its actually selected branch. -/
def dispatchStep (source : Input N) (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) : Store ctx × (dispatch source parameter cells output).Path :=
  let value := store.read (.first (.second parameter))
  let selected := dispatchArmStep source parameter cells output value store
  (selected.1, ⟨value, selected.2⟩)

/-- The real sampler flag selects the original priority branch on full CQ blocks. -/
theorem dispatch_execute (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (dispatch source parameter cells output).execute Reference state =
      state.mapClassical (fun entry => ((dispatchStep source parameter cells output entry.1).1,
        (entry.2, (dispatchStep source parameter cells output entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (.first (.second parameter))
    (fun value => if value.toBool then .classical (packEarlyOp parameter output)
      else checkedOrder source cells output)
    (dispatchArmStep source parameter cells output) ?_ Reference state).trans ?_
  · intro value reference history _ initial
    cases value with
    | bit value =>
      cases value
      · exact checked_execute source cells output reference initial
      · exact NativeHalfPower.classical_path_execute (packEarlyOp parameter output)
          reference initial _
  · exact congrArg
      (fun decision : DecidableEq
          (Store ctx × (History × (dispatch source parameter cells output).Path)) =>
        @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) decision state
          (fun entry => ((dispatchStep source parameter cells output entry.1).1,
            (entry.2, (dispatchStep source parameter cells output entry.1).2))))
      (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

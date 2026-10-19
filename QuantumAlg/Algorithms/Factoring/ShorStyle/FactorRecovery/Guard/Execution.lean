/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Construction
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual stored order-guard execution and its five native events

The zero initialization, low-bit complement, positivity comparison and two
Boolean conjunctions are the five real writes of the existing guard circuit.
Their record preserves complete quantum-reference blocks and every original
read outside the three actual written cells.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The exact store obtained from the five actual closed guard instructions. -/
def guardStore (cells : Cells ctx N) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (clearZeroOp cells)).applyOp (evenOrderOp cells)).applyOp
    (positiveOrderOp cells)).applyOp (positiveEvenOp cells)).applyOp (acceptedOrderOp cells)

/-- No structural read outside the actual zero and comparison cells changes in the guard. -/
lemma guard_read_other (cells : Cells ctx N) {shape : CShape} (other : CInputRef ctx shape)
    (zeroFree : cells.zero.key ∉ other.storageKeys)
    (activeFree : cells.active.key ∉ other.storageKeys)
    (positiveFree : cells.positive.key ∉ other.storageKeys) (store : Store ctx) :
    (guardStore cells store).read other = store.read other := by
  let cleared := store.applyOp (clearZeroOp cells)
  let even := cleared.applyOp (evenOrderOp cells)
  let positive := even.applyOp (positiveOrderOp cells)
  let combined := positive.applyOp (positiveEvenOp cells)
  exact (Store.read_applyOp_of_not_mem_storageKeys combined
    (acceptedOrderOp cells) other activeFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys positive (positiveEvenOp cells)
      other activeFree).trans
      ((Store.read_applyOp_of_not_mem_storageKeys even (positiveOrderOp cells)
        other positiveFree).trans
        ((Store.read_applyOp_of_not_mem_storageKeys cleared (evenOrderOp cells)
          other activeFree).trans
          (Store.read_applyOp_of_not_mem_storageKeys store (clearZeroOp cells) other zeroFree))))

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual five writes return their real values in chronological order. -/
def guardStep (cells : Cells ctx N) (store : Store ctx) :
    Store ctx × (guardOrder (model := model) cells).Path :=
  let cleared := BitWord.instructionStep (execution := model) (clearZeroOp cells) store
  let even := BitWord.instructionStep (execution := model) (evenOrderOp cells) cleared.1
  let positive := BitWord.instructionStep (execution := model) (positiveOrderOp cells) even.1
  let combined := BitWord.instructionStep (execution := model) (positiveEvenOp cells) positive.1
  let accepted := BitWord.instructionStep (execution := model) (acceptedOrderOp cells) combined.1
  (accepted.1, (cleared.2, (even.2, (positive.2, (combined.2, accepted.2)))))

/-- The actual returned record retains the original five-operation store update. -/
lemma guardStep_store (cells : Cells ctx N) (store : Store ctx) :
    (guardStep (model := model) cells store).1 = guardStore cells store := rfl

/-- The same real guard preserves history, service state and complete quantum-reference blocks. -/
lemma guard_execute (cells : Cells ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (guardOrder (model := model) cells).execute environment Reference state =
      state.mapClassical (fun entry =>
        let actual := guardStep (model := model) cells entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [guardOrder, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- All five native guard operations remain in their actual execution order. -/
lemma guard_eventTrace (cells : Cells ctx N)
    (path : (guardOrder (model := model) cells).Path) :
    (guardOrder (model := model) cells).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .bitXor (phaseBits N + 1))),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .lessThan (phaseBits N + 1))),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))] := by
  change (BitWord.instruction (execution := model) (clearZeroOp cells)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (evenOrderOp cells)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (positiveOrderOp cells)).eventTrace path.2.2.1 ++
        ((BitWord.instruction (execution := model) (positiveEvenOp cells)).eventTrace
            path.2.2.2.1 ++
          (BitWord.instruction (execution := model) (acceptedOrderOp cells)).eventTrace
            path.2.2.2.2))) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The real sequential guard has exactly five native unit-depth events. -/
lemma guard_unitDepth (cells : Cells ctx N)
    (path : (guardOrder (model := model) cells).Path) :
    (guardOrder (model := model) cells).depth (fun _ => 1) path = 5 := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

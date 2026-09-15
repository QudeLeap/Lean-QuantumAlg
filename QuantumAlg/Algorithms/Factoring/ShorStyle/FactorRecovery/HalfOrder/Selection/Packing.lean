/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection

/-!
# Actual nominal packaging of the selected GCD word

The final payload resize and nominal option pack are real instructions. The
comparison bit already stored by the actual checks is retained while the
payload is resized. The resulting closed option value includes both genuine
acceptance and rejection, with no inserted mathematical result.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual two-write store and physical packaging path. -/
def packStep (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (pack cells output).Path :=
  ((store.applyOp (resizeOp cells)).applyOp (packOp cells output), ((), ()))

/-- The actual payload resize and nominal pack preserve every full quantum-reference block. -/
theorem pack_execute (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (pack cells output).execute Reference state =
      state.mapClassical (fun entry => ((packStep cells output entry.1).1,
        (entry.2, (packStep cells output entry.1).2))) := by
  simp only [pack, Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def, packStep]
  congr 1
  exact Subsingleton.elim _ _

/-- The written option contains the actual previous comparison tag and resized candidate word. -/
theorem pack_result (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : cells.payload.key ≠ cells.lower.key) :
    (packStep cells output store).1.read (.storage output.toCStorageRef) =
      CShape.packOption
        (.product (store.read (.storage cells.lower.toCStorageRef))
          (CShape.wordResize (modulusBits N)
            (store.read (.storage cells.candidate.toCStorageRef)))) := by
  let resized := store.applyOp (resizeOp cells)
  have tagSame : resized.read (.storage cells.lower.toCStorageRef) =
      store.read (.storage cells.lower.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (resizeOp cells)
      (.storage cells.lower.toCStorageRef) (fun member => separate (List.mem_singleton.mp member))
  have payload : resized.read (.storage cells.payload.toCStorageRef) =
      CShape.wordResize (modulusBits N) (store.read (.storage cells.candidate.toCStorageRef)) :=
    Store.read_applyOp_output store (resizeOp cells)
  refine (Store.read_applyOp_output resized (packOp cells output)).trans ?_
  exact congrArg CShape.packOption (congrArg₂ CShape.Value.product tagSame payload)

/-- Packaging changes no structural read outside the actual payload and option cells. -/
theorem pack_read_other (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {shape : CShape} (other : CInputRef ctx shape)
    (payloadFree : cells.payload.key ∉ other.storageKeys)
    (outputFree : output.key ∉ other.storageKeys) (store : Store ctx) :
    (packStep cells output store).1.read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys (store.applyOp (resizeOp cells))
    (packOp cells output) other outputFree).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (resizeOp cells) other payloadFree)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

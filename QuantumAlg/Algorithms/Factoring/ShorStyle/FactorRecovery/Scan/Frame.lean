/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Frame
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual first-success scanning preserves the original sampled operands

Every visit changes only the surviving result and the four real selector
cells. Its complete order, power and GCD scratch is already released by the
factor-scope frame theorem. Thus later visits read the same stored parameter
and phase values even after arbitrary earlier branches and selections.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}

/-- Internal read support relative to the five actual surviving scan write destinations. -/
structure FrameFree (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) : Prop where
  candidate : cells.candidate.key ∉ other.storageKeys
  accepted : cells.accepted.key ∉ other.storageKeys
  selected : cells.selected.key ∉ other.storageKeys
  scratch : cells.scratch.key ∉ other.storageKeys
  result : result.key ∉ other.storageKeys

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual unpack and latch selection preserve every structural read outside their writes. -/
lemma selection_read_other (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells result other) (store : Store ctx) :
    (selectionStep (model := model) cells result store).1.read other = store.read other :=
  (FirstAccepted.firstAccepted_read_other (model := model) (selectorInputs cells) (selectorRefs
    cells)
    other free.scratch free.scratch free.accepted free.selected
    (store.applyOp (unpackOp cells result))).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (unpackOp cells result) other free.candidate)

/-- A real full recovery visit preserves the original sampled input frame. -/
lemma visit_read_other (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells result other) (store : Store ctx) :
    (visitStep (model := model) source inputs cells result store).1.read other = store.read other
      := by
  let recovered := FactorRecovery.NativeFactorScope.step (model := model) source
    inputs.parameter inputs.phase result store
  exact (selection_read_other cells result other free recovered.1).trans
    (FactorRecovery.NativeFactorScope.read_other (model := model) source inputs.parameter
      inputs.phase
      result other free.result store)

/-- The entire actual ordered scan preserves every original operand outside its five writes. -/
lemma scan_read_other (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells result other) (store : Store ctx) :
    (scanStep (model := model) source cells result inputs store).1.read other = store.read other :=
      by
  induction inputs generalizing store with
  | nil => rfl
  | cons inputs rest ih =>
      exact (ih (visitStep (model := model) source inputs cells result store).1).trans
        (visit_read_other source inputs cells result other free store)

/-- Initialization and the final option write obey the same complete original-frame guarantee. -/
lemma read_other (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells result other) (store : Store ctx) :
    (step (model := model) source inputs cells result store).1.read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys
    (scanStep (model := model) source cells result inputs (store.applyOp (clearAcceptedOp cells))).1
    (packOp cells result) other free.result).trans
    ((scan_read_other source inputs cells result other free
      (store.applyOp (clearAcceptedOp cells))).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (clearAcceptedOp cells) other free.accepted))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Records
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Initialization
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Keys
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Frame

/-!
# The actual complete GCD-selection scope preserves its original frame

All inner write-disjointness follows from the six actual fresh heads. The
original operand may read retained, borrowed or workspace storage. Only the
declared surviving output cell is excluded from its support.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}

private theorem frame_free (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) :
    NativeHalfFactor.FrameFree (cells ctx N) (liftWrite output) (liftInput other) := by
  constructor
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (5 : Fin 6))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (2 : Fin 6))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (1 : Fin 6))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (0 : Fin 6))
  · rw [liftInput_keys]
    exact separate

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem body_read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys)
    (store : Store (context ctx N)) :
    (bodyStep (model := model) halfPower output store).1.read (liftInput other) =
      store.read (liftInput other) :=
  (congrArg (fun final : Store (context ctx N) => final.read (liftInput other))
    (body_store (model := model) halfPower output store)).trans
      ((NativeHalfFactor.read_other (model := model) (liftInput halfPower) (cells ctx N)
          (liftWrite output)
        (liftInput other) (frame_free output other separate) (initialized (model := model)
            store)).trans
          (initialized_read_original (model := model) other store))

/-- After actual release, only the declared output can change in the original classical frame. -/
theorem read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step (model := model) halfPower output store).1.read other = store.read other :=
  (leave_read other (bodyStep (model := model) halfPower output (enter N store)).1).trans
    ((body_read_other (model := model) halfPower output other separate (enter N store)).trans
      (enter_read other store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

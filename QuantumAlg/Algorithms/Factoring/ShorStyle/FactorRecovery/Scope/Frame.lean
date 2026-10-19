/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Records
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Frame

/-!
# Full factor recovery preserves the actual original storage frame

The seven genuine workspace heads discharge every internal write-support
condition. After their real release, arbitrary retained, borrowed and outer
workspace reads agree with their initial values, except for the declared
surviving result cell. No source-value or scratch-initialization premise is
needed for this statement.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}

private lemma frame_free (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) :
    NativeFactorTail.FrameFree (cells ctx N) (liftWrite output) (liftInput other) := by
  constructor
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (6 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (5 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (4 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (3 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (2 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (1 : Fin 7))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (0 : Fin 7))
  · rw [liftInput_keys]
    exact separate

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private lemma body_read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys)
    (store : Store (context ctx N)) :
    (bodyStep (model := model) source parameter phase output store).1.read (liftInput other) =
      store.read (liftInput other) :=
  NativeFactorTail.read_other (model := model) source (liftInput parameter) (liftInput phase)
    (cells ctx N) (liftWrite output) (liftInput other) (frame_free output other separate) store

/-- The actual released factor scope changes no original operand outside its result cell. -/
lemma read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step (model := model) source parameter phase output store).1.read other = store.read other :=
  (leave_read other (bodyStep (model := model) source parameter phase output (enter N
    store)).1).trans
    ((body_read_other (model := model) source parameter phase output other separate (enter N
      store)).trans
      (enter_read other store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorScope

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopeExecution
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete actual execution of the half-order modular-power scope

The record below is the actual shift followed by the existing native power
record, between the real push and pop of the half-order cell. The execution
identity preserves every original complete quantum-reference density block.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

noncomputable section

open Execution ClassicalRoutines

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Actual shifted store and native modular-power path on the live half-order scope. -/
def bodyStep (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (store : Store (context ctx N)) :
    Store (context ctx N) × (body (model := model) source base order output).Path :=
  let shifted := BitWord.instructionStep (execution := model) (shiftOp order) store
  let powered := Modular.NativePower.intoStep (model := model) (modulusSpec source) (liftInput base)
    (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) shifted.1
  (powered.1, (shifted.2, powered.2))

/-- The real half-order scope enters and leaves exactly its own cell around that actual record. -/
def step (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (store : Store ctx) :
    Store ctx × (code (model := model) source base order output).Path :=
  let next := bodyStep (model := model) source base order output
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh next.1, next.2)

/-- The actual shifted half-order word is the exponent read by the native power execution. -/
lemma body_execute (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) source base order output).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((bodyStep (model := model) source base order output entry.1).1,
          (entry.2.1, (entry.2.2,
            (bodyStep (model := model) source base order output entry.1).2)))) := by
  simp only [body, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    Modular.NativePower.nativePower_into_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual scope execution preserves every full quantum-reference block and its genuine path. -/
lemma code_execute (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) source base order output).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((step (model := model) source base order output entry.1).1,
          (entry.2.1, (entry.2.2,
            (step (model := model) source base order output entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (environment := environment) ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
    (body (model := model) source base order output)
    (fun entry =>
      let next := bodyStep (model := model) source base order output entry.1
      ((next.1, entry.2), next.2))
    (body_execute source base order output) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

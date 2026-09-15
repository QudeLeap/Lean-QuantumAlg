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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem classical_path_execute {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (decision : DecidableEq (Store ctx × (History × (Circuit.classical op).Path))) :
    (Circuit.classical op).execute Reference state =
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
        decision state (fun entry =>
        (entry.1.applyOp op, (entry.2, (() : (Circuit.classical op).Path)))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  exact (Circuit.mapClassical_canonicalDecision _ state
    (fun entry => (entry.1.applyOp op, (entry.2, (() : (Circuit.classical op).Path))))).trans
    (Circuit.mapClassical_canonicalDecision _ state
      (fun entry => (entry.1.applyOp op, (entry.2, (() : (Circuit.classical op).Path))))).symm

/-- Actual shifted store and native modular-power path on the live half-order scope. -/
def bodyStep (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (store : Store (context ctx N)) :
    Store (context ctx N) × (body source base order output).Path :=
  let powered := Modular.NativePower.intoStep (modulusSpec source) (liftInput base)
    (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) (store.applyOp (shiftOp order))
  (powered.1, ((), powered.2))

/-- The real half-order scope enters and leaves exactly its own cell around that actual record. -/
def step (source : Input N) (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (store : Store ctx) :
    Store ctx × (code source base order output).Path :=
  let next := bodyStep source base order output
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh next.1, next.2)

/-- The actual shifted half-order word is the exponent read by the native power execution. -/
theorem body_execute (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx N) Reference History) :
    (body source base order output).execute Reference state =
      state.mapClassical (fun entry =>
        ((bodyStep source base order output entry.1).1,
          (entry.2, (bodyStep source base order output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (shiftOp order))
    (Modular.NativePower.into (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output))
    (fun store => (store.applyOp (shiftOp order), ()))
    (Modular.NativePower.intoStep (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output))
    (fun Reference _ _ state => classical_path_execute (shiftOp order) Reference state _)
    (Modular.NativePower.nativePower_into_execute (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)) Reference state).trans ?_
  exact (Circuit.mapClassical_canonicalDecision _ state
    (fun entry => ((bodyStep source base order output entry.1).1,
      (entry.2, (bodyStep source base order output entry.1).2)))).trans
    (Circuit.mapClassical_canonicalDecision _ state
      (fun entry => ((bodyStep source base order output entry.1).1,
        (entry.2, (bodyStep source base order output entry.1).2)))).symm

/-- Actual scope execution preserves every full quantum-reference block and its genuine path. -/
theorem code_execute (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code source base order output).execute Reference state =
      state.mapClassical (fun entry =>
        ((step source base order output entry.1).1,
          (entry.2, (step source base order output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh (body source base order output) (bodyStep source base order output)
    (body_execute source base order output) Reference state).trans ?_
  exact (Circuit.mapClassical_canonicalDecision _ state
    (fun entry => ((step source base order output entry.1).1,
      (entry.2, (step source base order output entry.1).2)))).trans
    (Circuit.mapClassical_canonicalDecision _ state
      (fun entry => ((step source base order output entry.1).1,
        (entry.2, (step source base order output entry.1).2)))).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

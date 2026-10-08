/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Semantics
import all QuantumAlg.Core.Execution.Reference.Weighted
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Unwritten classical observations through actual finite reset

The actual measured outcome and its stored-result correction retain every
weighted external-reference entry whenever the observation ignores writes
to that result cell. This extends through the direct basis corrections and finite
reset sequence, including aliased result cells and arbitrary incoming states.
-/

namespace QuantumAlg.QuditShift

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {gates : GateModel} {oracles : OracleModel}
variable {ctx : RuntimeCtx .quantum}

variable {implementations : ∀ wire,
  Realizations gates oracles ctx.quantumLayout wire}

/-- Actual measurement and correction preserve observations unaffected by the result write. -/
theorem resetCircuit_weighted_reference (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (weight : Store ctx → ℂ)
    (unchanged : ∀ store value, weight (store.write output value) = weight store)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((resetCircuit wire output (implementations wire)).execute
      Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  rw [resetCircuit_execute, ExecutionState.referenceFiberSum_mapClassical]
  simp only [resetCircuitRecord, unchanged]
  rw [ExecutionState.referenceFiberSum_applyLocalUnitary]
  exact ExecutionState.referenceFiberSum_measureZ state (fun basis => basis wire)
    (fun entry _ => weight entry.1.1) left right

/-- Direct correction preserves the same complete weighted reference matrix. -/
theorem resetWireToBasis_weighted_reference (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (weight : Store ctx → ℂ)
    (unchanged : ∀ store result, weight (store.write output result) = weight store)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((resetWireToBasis wire (implementations wire) output value).execute Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  rw [resetWireToBasis_execute, ExecutionState.referenceFiberSum_mapClassical]
  simp only [resetWireToBasisRecord, unchanged]
  rw [ExecutionState.referenceFiberSum_applyLocalUnitary]
  exact ExecutionState.referenceFiberSum_measureZ state (fun basis => basis wire)
    (fun entry _ => weight entry.1.1) left right

/-- Every stage preserves the observed classical weight together with both reference indices. -/
theorem resetToBasisOn_weighted_reference (count : Nat)
    (wires : Fin count → Fin ctx.systemCount)
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (weight : Store ctx → ℂ)
    (unchanged : ∀ wire store result, weight (store.write (outputs wire) result) = weight store)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((resetToBasisOn implementations count wires outputs label).execute Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  induction count generalizing History with
  | zero =>
      change ExecutionState.referenceFiberSum ((Circuit.id (model := .quantum gates oracles)
        ctx).execute Reference state)
        (fun entry _ => weight entry.1) left right = _
      simp only [Circuit.execute_id, ExecutionState.referenceFiberSum_mapClassical]
  | succ count ih =>
      exact (Circuit.referenceFiberSum_execute_seq _ _ state weight left right).trans
        ((ih (fun index => wires index.succ) _).trans
          (resetWireToBasis_weighted_reference (implementations := implementations) (wires 0)
            (outputs (wires 0)) (label (wires 0))
            state weight (unchanged (wires 0)) left right))

/-- Complete actual reset preserves every observation that ignores its overwritten cells. -/
theorem resetToBasis_weighted_reference
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (weight : Store ctx → ℂ)
    (unchanged : ∀ wire store result, weight (store.write (outputs wire) result) = weight store)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((resetToBasis implementations outputs label).execute
      Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right :=
  resetToBasisOn_weighted_reference (implementations := implementations) ctx.systemCount id
    outputs label state weight unchanged
    left right

end

end QuantumAlg.QuditShift

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Frame
import all QuantumAlg.Primitives.ZReset.Sequence.Semantics

/-!
# Register reuse with earlier classical results and references retained

The actual sequence resets every chosen quantum wire while allowing the same
finite result cell to be overwritten repeatedly. Any structural classical
read disjoint from those writes retains its complete joint observation with
the arbitrary external reference. The final quantum register is zero within
each such classical block, without an incoming independence assumption
[dW19, qcnotes.tex:5381,5409,5420].

Coverage and read separation are properties of the internal wiring list.
Every runtime entry remains present; these mathematical block projections
neither free storage nor hide a classical reset cell.
-/

namespace QuantumAlg.ZReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Every earlier untouched structural read commutes with the entire actual reset sequence. -/
theorem zReset_sequence_filter_read {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (implementations : ∀ wire,
      QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (readouts : List (ZReadout ctx)) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ item ∈ readouts, item.output.key ∉ observed.storageKeys)
    (value : shape.Value) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History)) :
    ((sequence implementations readouts).execute Reference state).filterClassical
        (fun entry => entry.1.read observed = value) =
      (sequence implementations readouts).execute Reference
        (state.filterClassical (fun entry => entry.1.read observed = value)) := by
  induction readouts generalizing Reference History with
  | nil =>
      change ((Circuit.id (model := .quantum gates oracles) ctx).execute
          Reference state).filterClassical (fun entry => entry.1.read observed = value) =
        (Circuit.id (model := .quantum gates oracles) ctx).execute Reference
          (state.filterClassical (fun entry => entry.1.read observed = value))
      rw [Circuit.execute_id, Circuit.execute_id]
      simp only [filter_map]
  | cons head tail ih =>
      exact filter_seq (circuit head.wire head.output (implementations head.wire))
        (sequence implementations tail)
        (fun store => store.read observed = value)
        (zReset_execute_filter_read head.wire head.output (implementations head.wire) observed
          (separate head (.head tail)) value)
        (fun reference {_history} _historyFinite initial =>
          ih (fun item present => separate item (.tail head present)) reference initial)
        Reference state

/-- The complete register becomes zero separately in every preserved classical-reference block.
This is the state equation required to reuse one actual register in later rounds. -/
theorem zReset_sequence_complete_read_entry {gates : GateModel} {oracles : OracleModel}
    {ctx : RuntimeCtx .quantum}
    (implementations : ∀ wire,
      QuditShift.Realizations gates oracles ctx.quantumLayout wire)
    (readouts : List (ZReadout ctx))
    (covers : ∀ wire : Fin ctx.systemCount, wire ∈ readouts.map ZReadout.wire)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ item ∈ readouts, item.output.key ∉ observed.storageKeys)
    (value : shape.Value) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (left right : ctx.quantumLayout.Basis)
    (leftRef rightRef : Reference.Index) :
    (((sequence implementations readouts).execute Reference state).filterClassical
      (fun entry => entry.1.read observed = value)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical
            (fun entry => entry.1.read observed = value)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  rw [zReset_sequence_filter_read implementations readouts observed separate value Reference state]
  exact zReset_sequence_complete_entry implementations readouts covers _
    left right leftRef rightRef

end

end QuantumAlg.ZReset

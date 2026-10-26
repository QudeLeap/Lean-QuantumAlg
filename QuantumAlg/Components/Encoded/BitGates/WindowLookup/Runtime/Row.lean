/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Semantics
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row

/-!
# Actual runtime row parity and stored physical feedback

The fixed row traversal reads each real table word, pays every AND/XOR and
then branches on the actual parity cells. The physical phase template uses
that same stored mask. A single supplied temporary classical bit is reused
by all columns and all rows, without adding any quantum system.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Every low column executes the same fixed full-width native parity program. -/
def rowProgram (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) : List (Fin columns) →
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false
  | [] => .id (model := .quantum AlgorithmGate.model oracles BitWord.model services) ctx
  | index :: rest => (RuntimeParity.program (parity index) temporary
      (RuntimeParity.inputs (table index) measured)).seq
        (rowProgram measured parity temporary table rest)

/-- All paid row instructions precede the actual stored-vector branch and physical phase. -/
def rowCircuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (rowProgram measured parity temporary table (List.ofFn fun index : Fin columns => index)).seq
    (.branch (MaskParity.rowInput parity) fun stored => SelectorFrame.placedCircuit
      physical sameWires (wordMaskParityPhaseProgram physical oracles target distinct
        selector outside (MaskParity.storedConstant stored) height))

/-- The actual chronological row record retains every native AND/XOR outcome. -/
def rowRecord (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) :
    (indices : List (Fin columns)) → Store ctx → Store ctx ×
      (rowProgram (oracles := oracles) (services := services)
        measured parity temporary table indices).Path
  | [], store => (store, ())
  | index :: rest, store => Circuit.sequenceStoreRecord
      (RuntimeParity.program (parity index) temporary (RuntimeParity.inputs (table index) measured))
      (rowProgram measured parity temporary table rest)
      (RuntimeParity.record (parity index) temporary (RuntimeParity.inputs (table index) measured))
      (rowRecord measured parity temporary table rest) store

/-- The fixed row keeps full Store/history/reference correlations through every real instruction. -/
lemma rowProgram_execute (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (indices : List (Fin columns))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (rowProgram measured parity temporary table indices).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := rowRecord (oracles := oracles) (services := services)
          measured parity temporary table indices entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction indices generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical environment Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons index rest ih =>
      exact Circuit.execute_sequenceStoreRecord _ _ environment
        (RuntimeParity.record (parity index) temporary
          (RuntimeParity.inputs (table index) measured))
        (rowRecord measured parity temporary table rest)
        (RuntimeParity.program_execute _ _ _ environment)
        (fun reference history _ current => ih reference current) Reference state

/-- The final branch value is read after all actual runtime table parity writes. -/
def rowCircuitRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (store : Store ctx) : Store ctx × (rowCircuit (oracles := oracles) (services := services)
      physical sameWires measured parity temporary table target distinct selector outside
        height).Path :=
  let computed := rowRecord (oracles := oracles) (services := services)
    measured parity temporary table (List.ofFn fun index : Fin columns => index) store
  (computed.1, (computed.2, ⟨computed.1.read (MaskParity.rowInput parity), ()⟩))

/-- Paid parity and physical feedback use the same returned Store and complete branch path. -/
lemma rowCircuit_execute (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (rowCircuit physical sameWires measured parity temporary table target distinct
      selector outside height).execute environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordMaskParityPhaseProgram physical oracles target distinct selector outside
            (MaskParity.storedConstant ((rowRecord (oracles := oracles) (services := services)
              measured parity temporary table (List.ofFn fun index : Fin columns => index)
                entry.1).1.read (MaskParity.rowInput parity))) height)).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
        let result := rowCircuitRecord (oracles := oracles) (services := services)
          physical sameWires measured parity temporary table target distinct selector outside
            height entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  unfold rowCircuit
  simp only [SelectorFrame.placedCircuit]
  rw [Circuit.execute_seq, rowProgram_execute, Circuit.selectedUnitary_execute,
    ExecutionState.applyUnitary_mapClassical]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

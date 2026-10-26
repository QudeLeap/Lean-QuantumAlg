/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Semantics
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase.Word
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Paid row parity followed by its actual stored-mask phase

Each low-address column computes the measured-mask dot product using the
actual native XOR fold in a supplied classical parity cell. The real fixed
vector read then selects the physical parity-phase program. That branch
consumes the computed cells rather than recomputing their contents for free.
The same classical cells may be reused by the next high-address row.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Structural reads of precisely the measured positions selected by one static table word. -/
def selectedInputs (measured : CInputRef ctx (.bits wordWidth))
    (constant : Fin (2 ^ wordWidth)) : List (CInputRef ctx .bit) :=
  (Word.constantOneIndices constant).map fun index => .bitsGet measured index

/-- Each selected low-address column computes parity in its actual supplied writable cell. -/
def rowProgram (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) : List (Fin columns) →
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false
  | [] => .id (model := .quantum AlgorithmGate.model oracles BitWord.model services) ctx
  | index :: rest => (program (parity index) (selectedInputs measured (table index))).seq
      (rowProgram measured parity table rest)

/-- The actual parity cells, in the same original low-address index order. -/
def rowInput (parity : Fin columns → CWriteRef ctx .bit) :
    CInputRef ctx (.fixedVector columns .bit) :=
  .fixedVector fun index => .storage (parity index).toCStorageRef

/-- Decode only the branch's actual stored bit vector, least significant position first. -/
def storedConstant (value : CShape.Value (.fixedVector columns .bit)) : Fin (2 ^ columns) :=
  ⟨Nat.ofBits (fun index : Fin columns => (value.get index).toBool), Nat.ofBits_lt_two_pow _⟩

/-- Every selected physical target position uses its corresponding actual stored parity bit. -/
lemma storedConstant_testBit (value : CShape.Value (.fixedVector columns .bit))
    (index : Fin columns) :
    (storedConstant value).val.testBit index.val = (value.get index).toBool := by
  exact Nat.testBit_ofBits_lt _ index.val index.isLt

/-- Run all paid row parity instructions, then read their actual results for physical feedback. -/
def rowCircuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (rowProgram measured parity table (List.ofFn fun index : Fin columns => index)).seq
    (.branch (rowInput parity) fun value => SelectorFrame.placedCircuit physical sameWires
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside
        (storedConstant value) height))

/-- Each actual classical row stage retains all native XOR outcomes and intermediate Stores. -/
def rowRecord (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) : (indices : List (Fin columns)) →
    Store ctx → Store ctx × (rowProgram (oracles := oracles) (services := services)
      measured parity table indices).Path
  | [], store => (store, ())
  | index :: rest, store => Circuit.sequenceStoreRecord
      (program (parity index) (selectedInputs measured (table index)))
      (rowProgram measured parity table rest)
      (record (parity index) (selectedInputs measured (table index)))
      (rowRecord measured parity table rest) store

/-- The row's real finite record preserves arbitrary incoming Store/history/reference blocks. -/
lemma rowProgram_execute (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (indices : List (Fin columns))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (rowProgram measured parity table indices).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := rowRecord (oracles := oracles) (services := services)
          measured parity table indices entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction indices generalizing Reference History with
  | nil =>
      exact (Circuit.execute_id_mapClassical environment Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons index rest ih =>
      exact Circuit.execute_sequenceStoreRecord _ _ environment
        (record (parity index) (selectedInputs measured (table index)))
        (rowRecord measured parity table rest)
        (program_execute (parity index) (selectedInputs measured (table index)) environment)
        (fun reference history _ current => ih reference current) Reference state

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity

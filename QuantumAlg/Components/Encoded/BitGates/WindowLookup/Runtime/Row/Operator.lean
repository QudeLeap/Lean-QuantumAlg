/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Store
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Operator

/-!
# The exact actual runtime-table feedback operator

The operator below is derived from the paid row's real stored parity vector.
Its original-table form is only an execution observation; it is never used
to choose circuit constructors. The selected physical H/CNOT/H program acts
on arbitrary dirty quantum data and preserves every external reference.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The real stored phase matrix expressed using the same original table and measured mask. -/
def rowOperator (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : oracles.Interpretation) (store : Store ctx) : UnitaryOperator ctx.register :=
  MaskParity.rowOperator physical sameWires measured (readTable table store)
    target distinct selector outside height environment store

/-- Actual parity, true final Store and exact physical matrix retain every original input fiber. -/
lemma rowCircuit_execute_original_table (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (parityDistinct : Function.Injective (fun index => (parity index).key))
    (temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key)
    (maskFree : ∀ index, (parity index).key ∉ measured.storageKeys)
    (temporaryMaskFree : temporary.key ∉ measured.storageKeys)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (tableFree : ∀ index column, (parity index).key ∉ (table column).storageKeys)
    (temporaryTableFree : ∀ column, temporary.key ∉ (table column).storageKeys)
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (rowCircuit physical sameWires measured parity temporary table target distinct selector
      outside height).execute environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (rowOperator physical sameWires measured table target distinct selector outside height
          environment.quantum entry.1) (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
        let result := rowCircuitRecord physical sameWires measured parity temporary table
          target distinct selector outside height entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  rw [rowCircuit_execute]
  simp only [storedRowConstant_eq measured parity temporary parityDistinct temporaryDifferent
    maskFree temporaryMaskFree table tableFree temporaryTableFree]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The derived original-table matrix has the exact full-data native phase on arbitrary inputs. -/
lemma rowOperator_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (covered : columns ≤ 2 ^ height) (environment : oracles.Interpretation)
    (store : Store ctx) (state : Data) :
    (rowOperator physical sameWires measured table target distinct selector outside height
      environment store).applyVec (SelectorFrame.ctxVector physical sameWires state) =
      (if selector.get state then
        (if wordMaskParity target
          (MaskParity.rowConstant (readTable table store) (store.read measured)) state then (-1 : ℂ)
          else 1) else 1) • SelectorFrame.ctxVector physical sameWires state :=
  MaskParity.rowOperator_applyVec physical sameWires measured (readTable table store)
    target distinct selector outside height covered environment store state

/-- The full physical branch adds no writes beyond those of the actual runtime parity row. -/
lemma rowCircuitRecord_read_other (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    {shape : CShape} (observed : CInputRef ctx shape)
    (freeParity : ∀ index, (parity index).key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (rowCircuitRecord (oracles := oracles) (services := services) physical sameWires measured
      parity temporary table target distinct selector outside height store).1.read observed =
      store.read observed :=
  rowRecord_read_other measured parity temporary table _ observed
    (fun index _ => freeParity index) freeTemporary store

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

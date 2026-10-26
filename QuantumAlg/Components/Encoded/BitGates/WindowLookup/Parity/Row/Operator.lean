/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Constant
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase.Operator

/-!
# Actual paid row operator and its original-mask scalar

The original-mask expression is derived from the actual paid XOR row and
its stored branch read. It is the same matrix in the complete execution
equation, retaining every old Store and reference block. Its native fan-in,
H/CNOT/H and inverse restore every quantum label with the exact mask phase.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The actual paid row's selected native matrix, expressed using its proved original-mask value. -/
def rowOperator (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (table : Fin columns → Fin (2 ^ wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : oracles.Interpretation) (store : Store ctx) : UnitaryOperator ctx.register :=
  (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (wordMaskParityPhaseProgram physical oracles target distinct selector outside
      (rowConstant table (store.read measured)) height)).matrix environment

/-- The original-mask matrix belongs to the same actual paid row and its complete real record. -/
lemma rowCircuit_execute_original_mask (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (parityDistinct : Function.Injective (fun index => (parity index).key))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (table : Fin columns → Fin (2 ^ wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    Circuit.execute
      (rowCircuit physical sameWires measured parity table target distinct selector outside height)
        environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (rowOperator physical sameWires measured table target distinct selector outside height
          environment.quantum entry.1) (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := rowCircuitRecord physical sameWires measured parity table target distinct
              selector outside height entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  rw [rowCircuit_execute]
  simp only [storedRowConstant_eq measured parity parityDistinct separate]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma vector_reindex_smul {Source Target : Register}
    (coordinates : Source.Index ≃ Target.Index) (scalar : ℂ) (vector : HilbertVector Source) :
    HilbertVector.reindex coordinates (scalar • vector) =
      scalar • HilbertVector.reindex coordinates vector := by
  ext index
  rfl

/-- The actual paid row matrix contributes exactly its original-mask phase on every dirty input. -/
lemma rowOperator_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (table : Fin columns → Fin (2 ^ wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (covered : columns ≤ 2 ^ height) (environment : oracles.Interpretation)
    (store : Store ctx) (state : Data) :
    (rowOperator physical sameWires measured table target distinct selector outside height
      environment store).applyVec (SelectorFrame.ctxVector physical sameWires state) =
      (if selector.get state then
        (if wordMaskParity target (rowConstant table (store.read measured)) state then (-1 : ℂ)
          else 1) else 1) • SelectorFrame.ctxVector physical sameWires state := by
  have native := wordMaskParityPhaseProgram_applyVec physical oracles target distinct
    selector outside (rowConstant table (store.read measured)) height covered environment state
  change UnitaryOperator.applyVec _
    (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode state))).vec = _ at native
  let coordinates : physical.toQuantum.register.Index ≃ ctx.register.Index :=
    basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
  have transported := congrArg
    (HilbertVector.reindex (R := physical.toQuantum.register) (S := ctx.register) coordinates)
    native
  rw [← UnitaryOperator.reindex_applyVec, HilbertVector.reindex_ket,
    vector_reindex_smul, HilbertVector.reindex_ket] at transported
  have scalar : (if selector.get state = true ∧
      wordMaskParity target (rowConstant table (store.read measured)) state = true then (-1 : ℂ)
      else 1) = if selector.get state then
        (if wordMaskParity target (rowConstant table (store.read measured)) state then -1 else 1)
        else 1 := by
    cases selector.get state <;>
      cases wordMaskParity target (rowConstant table (store.read measured)) state <;> simp
  rw [scalar] at transported
  unfold rowOperator
  rw [unitaryOfEqualWires_matrix]
  exact transported

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity

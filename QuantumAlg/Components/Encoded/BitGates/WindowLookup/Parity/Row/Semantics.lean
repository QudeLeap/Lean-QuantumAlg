/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Store

/-!
# Actual paid parity and stored physical feedback on every joint input block

The selected physical phase is evaluated from the actual chronological final
Store of the native XOR instructions. The output record retains all native
parity results and the actual stored-vector branch read. Every incoming
Store/history collision and arbitrary external reference remains explicit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The actual row circuit's complete deterministic native/classical branch record. -/
def rowCircuitRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (store : Store ctx) : Store ctx × (rowCircuit (oracles := oracles) (services := services)
      physical sameWires measured parity table target distinct selector outside height).Path :=
  let computed := rowRecord (oracles := oracles) (services := services) measured parity table
    (List.ofFn fun index : Fin columns => index) store
  (computed.1, (computed.2, ⟨computed.1.read (rowInput parity), ()⟩))

/-- The actual paid row phase is selected from each original Store's true computed parity cells. -/
lemma rowCircuit_execute (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
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
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordMaskParityPhaseProgram physical oracles target distinct selector outside
            (storedConstant ((rowRecord (oracles := oracles) (services := services)
              measured parity table (List.ofFn fun index : Fin columns => index) entry.1).1.read
                (rowInput parity))) height)).matrix environment.quantum)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := rowCircuitRecord (oracles := oracles) (services := services)
            physical sameWires measured parity table target distinct selector outside height entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  unfold rowCircuit
  simp only [SelectorFrame.placedCircuit]
  rw [Circuit.execute_seq, rowProgram_execute, Circuit.selectedUnitary_execute,
    ExecutionState.applyUnitary_mapClassical]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row

/-!
# Unconditional actual stored-mask operator of a runtime row

The operator is a mathematical observation of the row's actual chronological
Store and physical branch. Its full execution equation needs no clean-state
promise and retains all original history/reference blocks. Table preservation
and the intended measured character are established separately.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The actual native phase selected after every paid AND/XOR output has reached its real cell. -/
def actualOperator (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (target : Word encoding columns)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (environment : oracles.Interpretation) (store : Store ctx) : UnitaryOperator ctx.register :=
  (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (wordMaskParityPhaseProgram physical oracles target distinct selector outside
      (MaskParity.storedConstant ((rowRecord (oracles := oracles) (services := services)
        measured parity temporary table (List.ofFn fun index : Fin columns => index) store).1.read
          (MaskParity.rowInput parity))) height)).matrix environment

/-- Every original input fiber uses the actual selected phase and the same complete row record. -/
lemma rowCircuit_execute_actual_operator (physical : QubitLayout encoding.width)
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
    (rowCircuit physical sameWires measured parity temporary table target distinct selector
      outside height).execute environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (actualOperator (services := services) physical sameWires measured parity temporary table
          target distinct selector outside height environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
        let result := rowCircuitRecord physical sameWires measured parity temporary table target
          distinct selector outside height entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  rowCircuit_execute physical sameWires measured parity temporary table target distinct selector
    outside height environment Reference state

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

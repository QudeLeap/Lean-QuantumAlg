/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Execution
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Semantics

/-!
# Complete actual runtime high-half execution

The native selector retains every row's actual chronological Store, real
stored-mask branch and physical phase operator. These unconditional execution
equations preserve every original history and arbitrary quantum reference.
The intended table character is a separate correctness statement.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
  (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
    CInputRef ctx (.unsignedWord resultWidth))

/-- Every actual row outcome and stored-vector phase selection remains in the callback record. -/
def halfCallbackRecord (label : Fin (2 ^ highRemaining)) (store : Store ctx) :
    Store ctx × (halfCallback frame (services := services)
      physical sameWires measured parity temporary table label).Path :=
  RuntimeRow.rowCircuitRecord physical sameWires measured parity temporary (table label)
    frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth store

/-- The native phase is exactly the one selected by this callback's actual returned parity cells. -/
def halfCallbackOperator (environment : OracleModel.Interpretation .empty)
    (label : Fin (2 ^ highRemaining)) (store : Store ctx) : UnitaryOperator ctx.register :=
  RuntimeRow.actualOperator (services := services) physical sameWires measured parity temporary
    (table label) frame.lowWord frame.low.targetDistinct
    (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
    environment store

/-- The chronological actual traversal record includes every callback's preceding true Store. -/
def halfRecord (store : Store ctx) :
    Store ctx × (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path :=
  frame.high.circuitAtRecord physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- The same actual callback Store determines every factor of the native operator product. -/
def halfOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  frame.high.circuitAtOperator physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (halfCallbackOperator frame (services := services)
      physical sameWires measured parity temporary table environment)
    environment (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- Exact full high-half execution on arbitrary original Store/history/reference matrices. -/
lemma halfCircuit_execute
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (halfCircuit frame physical sameWires measured parity temporary table).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (halfOperator frame (services := services) physical sameWires measured parity temporary
          table environment.quantum entry.1) (1 : UnitaryOperator Reference)).mapClassical
        (fun entry =>
          let result := halfRecord frame (services := services) physical sameWires measured parity
            temporary table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact frame.high.circuitAt_execute physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (halfCallbackRecord frame (services := services)
      physical sameWires measured parity temporary table)
    (halfCallbackOperator frame (services := services)
      physical sameWires measured parity temporary table environment.quantum)
    environment (fun label Reference _ _ current =>
      RuntimeRow.rowCircuit_execute_actual_operator physical sameWires measured parity temporary
        (table label) frame.lowWord frame.low.targetDistinct
        (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
        environment Reference current)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) Reference state

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

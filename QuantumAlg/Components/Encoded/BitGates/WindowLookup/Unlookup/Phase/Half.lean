/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Operator
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row.Observation
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase.Address
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Observation

/-!
# Actual paid high-address half traversal

Every leaf computes its actual classical parity row and reads the stored
row to choose its native H/CNOT/H feedback. The chronological complete
record retains every overwrite. Clean prefixes select the phase at the
original full high address and restore every quantum data coordinate.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

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
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- Each leaf is precisely the paid row and its stored native feedback. -/
def halfCallback (label : Fin (2 ^ highRemaining)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  MaskParity.rowCircuit physical sameWires measured parity (table label)
    frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth

/-- The complete actual high-half circuit uses supplied existing prefix and result systems. -/
def halfCircuit :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  frame.high.circuit physical sameWires
    (frame.halfCallback (services := services)
      physical sameWires measured parity table) (SelectorTrie.full highRemaining)

/-- The actual leaf record retains its paid row's writes and stored feedback path. -/
def halfCallbackRecord (label : Fin (2 ^ highRemaining)) (store : Store ctx) :
    Store ctx × (frame.halfCallback (services := services)
      physical sameWires measured parity table label).Path :=
  MaskParity.rowCircuitRecord physical sameWires measured parity (table label)
    frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth store

/-- The actual leaf matrix, with its proved original-mask expression. -/
def halfCallbackOperator (environment : OracleModel.Interpretation .empty)
    (label : Fin (2 ^ highRemaining)) (store : Store ctx) : UnitaryOperator ctx.register :=
  MaskParity.rowOperator physical sameWires measured (table label)
    frame.lowWord frame.low.targetDistinct (frame.high.stack ⟨highRemaining, by omega⟩)
    (frame.highStack_lowWord _) lowWidth environment store

/-- The chronological full traversal record preserves every real intermediate Store. -/
def halfRecord (store : Store ctx) :
    Store ctx × (frame.halfCircuit (services := services)
      physical sameWires measured parity table).Path :=
  frame.high.circuitAtRecord physical sameWires
    (frame.halfCallback (services := services) physical sameWires measured parity table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity table)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- The native fork product includes the actual Store selected by every preceding paid row. -/
def halfOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  frame.high.circuitAtOperator physical sameWires
    (frame.halfCallback (services := services) physical sameWires measured parity table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity table)
    (frame.halfCallbackOperator physical sameWires measured table environment)
    environment (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- Exact full execution, including all old Store/history fibers and the arbitrary reference. -/
lemma halfCircuit_execute
    (parityDistinct : Function.Injective fun index => (parity index).key)
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (frame.halfCircuit (services := services)
      physical sameWires measured parity table).execute environment Reference
      state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (frame.halfOperator (services := services)
          physical sameWires measured parity table environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := frame.halfRecord (services := services)
            physical sameWires measured parity table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  have actual := frame.high.circuitAt_execute physical sameWires
    (frame.halfCallback (services := services) physical sameWires measured parity table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity table)
    (frame.halfCallbackOperator physical sameWires measured table environment.quantum)
    environment (fun label Reference _ _ state =>
      MaskParity.rowCircuit_execute_original_mask physical sameWires measured parity parityDistinct
        separate (table label) frame.lowWord frame.low.targetDistinct
        (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
        environment Reference state)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) Reference state
  exact actual

/-- Paid rows preserve the original measured mask throughout the true chronological traversal. -/
lemma halfRecord_read_mask
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys) (store : Store ctx) :
    (frame.halfRecord (services := services)
      physical sameWires measured parity table store).1.read measured =
      store.read measured :=
  frame.high.circuitAtRecord_observe physical sameWires
    (frame.halfCallback (services := services) physical sameWires measured parity table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity table)
    (fun store => store.read measured)
    (fun label store => MaskParity.rowCircuitRecord_read_other physical sameWires measured parity
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      measured separate store)
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store

/-- The parity scalar of a row uses the actual original measured mask. -/
def rowPhase (label : Fin (2 ^ highRemaining)) (value : CShape.Value (.bits resultWidth))
    (state : Data) : ℂ :=
  if wordMaskParity frame.lowWord (MaskParity.rowConstant (table label) value) state then -1 else 1

/-- Every temporary high-prefix flip is outside the reused result word and its exact phase. -/
lemma rowPhase_flip_stack (label : Fin (2 ^ highRemaining))
    (value : CShape.Value (.bits resultWidth)) (index : Fin (highRemaining + 1)) (state : Data) :
    frame.rowPhase table label value ((frame.high.stack index).flip state) =
      frame.rowPhase table label value state := by
  apply congrArg (fun bit : Bool => if bit then (-1 : ℂ) else 1)
  apply bitParity_congr
  intro bit member
  obtain ⟨target, _, rfl⟩ := List.mem_map.mp member
  exact EncodedBit.get_flip_of_wire_ne (frame.high.stack index) (frame.lowWord.bit target)
    (frame.highStack_lowWord index target) state

/-- The actual native traversal restores all data and contributes
exactly its selected row phase. -/
lemma halfOperator_applyVec
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (clean : frame.high.CleanFrom 0 state) :
    (frame.halfOperator (services := services)
      physical sameWires measured parity table environment store).applyVec
      (SelectorFrame.ctxVector physical sameWires state) =
      (if (frame.high.stack ⟨0, by omega⟩).get state then
        frame.rowPhase table
          (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
          (store.read measured) state else 1) •
          SelectorFrame.ctxVector physical sameWires state := by
  have actual := frame.high.circuitAtOperator_selectedPhase physical sameWires
    (frame.halfCallback (services := services) physical sameWires measured parity table)
    (frame.halfCallbackRecord (services := services) physical sameWires measured parity table)
    (frame.halfCallbackOperator physical sameWires measured table environment)
    (fun store => store.read measured)
    (fun label store => MaskParity.rowCircuitRecord_read_other physical sameWires measured parity
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      measured separate store)
    (frame.rowPhase table) (frame.rowPhase_flip_stack table)
    (fun label store state => MaskParity.rowOperator_applyVec physical sameWires measured
      (table label) frame.lowWord frame.low.targetDistinct
      (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _) lowWidth
      (Nat.le_refl _) environment store state)
    environment (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) store state clean
  rw [frame.high.selectedPhaseAt_full] at actual
  exact actual

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

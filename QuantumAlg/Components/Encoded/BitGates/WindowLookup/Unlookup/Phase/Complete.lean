/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Half
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Address

/-!
# Complete actual split-address phase feedback

The two real X gates reuse and restore the original top high-address bit.
Every half runs its full paid classical rows on the preceding actual Store.
The exact scalar selects the original full address, and every quantum data
coordinate is restored on the explicitly supplied clean-prefix subspace.
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
  (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))

/-- The actual native flip of the existing high-address top bit, on the same physical systems. -/
def topFlipProgram : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)

/-- Complete real records from both paid halves and the two original native flip paths. -/
def phaseRecord (store : Store ctx) : Store ctx ×
    (frame.phaseCircuit (services := services)
      physical sameWires measured parity table).Path :=
  let left := frame.halfRecord (services := services)
    physical sameWires measured parity (table false) store
  let right := frame.halfRecord (services := services)
    physical sameWires measured parity (table true) left.1
  (right.1, ((), (left.2, ((), right.2))))

/-- Exact physical operator product with the true chronological intermediate paid-row Store. -/
def phaseOperator (environment : OracleModel.Interpretation .empty) (store : Store ctx) :
    UnitaryOperator ctx.register :=
  let left := frame.halfRecord (services := services)
    physical sameWires measured parity (table false) store
  frame.halfOperator (services := services)
      physical sameWires measured parity (table true) environment left.1 *
    (frame.topFlipProgram physical sameWires).matrix environment *
    frame.halfOperator (services := services)
      physical sameWires measured parity (table false) environment store *
    (frame.topFlipProgram physical sameWires).matrix environment

private lemma reference_product {Local Reference : Register}
    (second first : UnitaryOperator Local) :
    UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) *
        UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) =
      UnitaryOperator.prodTensor (second * first) (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  change (UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) *
    (UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) = _
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, HilbertOperator.kronecker_identity_mul]
  rfl

/-- Both actual halves keep all old Store/history blocks and the arbitrary external reference. -/
lemma phaseCircuit_execute
    (parityDistinct : Function.Injective fun index => (parity index).key)
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (frame.phaseCircuit physical sameWires measured parity table).execute environment Reference
      state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (frame.phaseOperator (services := services)
          physical sameWires measured parity table environment.quantum entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := frame.phaseRecord (services := services)
            physical sameWires measured parity table entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  change ((Circuit.unitary (frame.topFlipProgram physical sameWires)).seq
    ((frame.halfCircuit physical sameWires measured parity (table false)).seq
      ((Circuit.unitary (frame.topFlipProgram physical sameWires)).seq
        (frame.halfCircuit physical sameWires measured parity (table true))))).execute
          environment Reference state = _
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq,
    frame.halfCircuit_execute physical sameWires measured parity (table false)
      parityDistinct separate, Circuit.execute_seq, Circuit.execute_unitary,
    frame.halfCircuit_execute physical sameWires measured parity (table true)
      parityDistinct separate]
  simp only [State.mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    ExecutionState.executionState_applyUnitary_comp, reference_product, mul_assoc,
    phaseOperator, phaseRecord]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both chronological traversals retain the actual original measured mask. -/
lemma phaseRecord_read_mask
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys) (store : Store ctx) :
    (frame.phaseRecord (services := services)
      physical sameWires measured parity table store).1.read measured = store.read measured := by
  exact (frame.halfRecord_read_mask (services := services) physical sameWires measured parity
    (table true) separate _).trans
    (frame.halfRecord_read_mask (services := services)
      physical sameWires measured parity (table false) separate store)

/-- Exact original full-address parity scalar of the actual paid two-half feedback circuit. -/
lemma phaseOperator_applyVec
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (clean : frame.high.CleanFrom 0 state) :
    (frame.phaseOperator (services := services)
      physical sameWires measured parity table environment store).applyVec
        (SelectorFrame.ctxVector physical sameWires state) =
      frame.rowPhase (table ((frame.high.stack ⟨0, by omega⟩).get state))
        (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
        (store.read measured) state • SelectorFrame.ctxVector physical sameWires state := by
  let flipped := (frame.high.stack ⟨0, by omega⟩).flip state
  let left := frame.halfRecord (services := services)
    physical sameWires measured parity (table false) store
  have first := SelectorFrame.placedProgram_applyVec physical sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)
    (frame.high.stack ⟨0, by omega⟩).flip environment
    (GateSpec.realizes physical .empty _ environment) state
  change ((frame.topFlipProgram physical sameWires).matrix environment).applyVec
    (SelectorFrame.ctxVector physical sameWires state) =
      SelectorFrame.ctxVector physical sameWires flipped at first
  have next := SelectorFrame.placedProgram_applyVec physical sameWires
    ((GateSpec.x (frame.high.stack ⟨0, by omega⟩)).program physical .empty)
    (frame.high.stack ⟨0, by omega⟩).flip environment
    (GateSpec.realizes physical .empty _ environment) flipped
  rw [EncodedBit.flip_flip] at next
  change ((frame.topFlipProgram physical sameWires).matrix environment).applyVec
    (SelectorFrame.ctxVector physical sameWires flipped) =
      SelectorFrame.ctxVector physical sameWires state at next
  have leftActual := frame.halfOperator_applyVec (services := services)
    physical sameWires measured parity (table false)
    separate environment store flipped (frame.high.cleanFrom_flip_enable state clean)
  have rightActual := frame.halfOperator_applyVec (services := services)
    physical sameWires measured parity (table true)
    separate environment left.1 state clean
  have observed := frame.halfRecord_read_mask (services := services)
    physical sameWires measured parity (table false)
    separate store
  change left.1.read measured = store.read measured at observed
  rw [observed] at rightActual
  change (frame.halfOperator (services := services)
      physical sameWires measured parity (table true) environment left.1 *
    (frame.topFlipProgram physical sameWires).matrix environment *
    frame.halfOperator (services := services)
      physical sameWires measured parity (table false) environment store *
    (frame.topFlipProgram physical sameWires).matrix environment).applyVec _ = _
  rw [UnitaryOperator.mul_applyVec, first, UnitaryOperator.mul_applyVec, leftActual,
    UnitaryOperator.applyVec_smul, UnitaryOperator.mul_applyVec, next, rightActual, smul_smul]
  have address := frame.high.addressLabelAt_flip_enable
    highRemaining 0 (by omega) 0 (by omega) state
  have scalar := frame.rowPhase_flip_stack (table false)
    (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
    (store.read measured) ⟨0, by omega⟩ state
  dsimp only [flipped] at *
  rw [EncodedBit.get_flip_self, address, scalar]
  cases (frame.high.stack ⟨0, by omega⟩).get state <;> simp

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition.Unitary

/-!
# Complete stored-value unitary semantics of the actual hybrid selector

Every classical callback runs on the true chronological incoming Store.
Its actual record supplies the next callback's Store and its stored-value
unitary supplies the exact quantum operator. Native selector gates remain
inside the same operator product and the complete real execution path.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

/-- Exact chronological hybrid-selector records, including every actual native fork path. -/
def circuitAtRecord (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (record : ∀ label, Store ctx → Store ctx × (callback label).Path) :
    {remaining : Nat} → (tree : SelectorTrie remaining) → (depth : Nat) →
      (fits : depth + remaining = width) → (offset : Nat) →
        (bounded : offset + 2 ^ remaining ≤ 2 ^ width) → Store ctx → Store ctx ×
          (frame.circuitAt physical sameWires callback tree depth fits offset bounded).Path
  | _, .skip _, _, _, _, _, store => (store, ())
  | 0, .leaf, _, _, offset, bounded, store =>
      record ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ store
  | remaining + 1, .fork left right, depth, fits, offset, bounded, store =>
      let leftResult := frame.circuitAtRecord physical sameWires callback record
        left (depth + 1) (by omega) offset (left_bound bounded) store
      let rightResult := frame.circuitAtRecord physical sameWires callback record
        right (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded) leftResult.1
      (rightResult.1, ((), (leftResult.2, ((), (rightResult.2, ())))))

/-- Exact operator product of the native forks and real intermediate-Store callback unitaries. -/
def circuitAtOperator (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (record : ∀ label, Store ctx → Store ctx × (callback label).Path)
    (operator : Fin (2 ^ width) → Store ctx → UnitaryOperator ctx.register)
    (environment : oracles.Interpretation) :
    {remaining : Nat} → (tree : SelectorTrie remaining) → (depth : Nat) →
      (fits : depth + remaining = width) → (offset : Nat) →
        (bounded : offset + 2 ^ remaining ≤ 2 ^ width) → Store ctx →
          UnitaryOperator ctx.register
  | _, .skip _, _, _, _, _, _ => 1
  | 0, .leaf, _, _, offset, bounded, store =>
      operator ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩ store
  | remaining + 1, .fork left right, depth, fits, offset, bounded, store =>
      let present : depth < width := by omega
      let leftResult := frame.circuitAtRecord physical sameWires callback record
        left (depth + 1) (by omega) offset (left_bound bounded) store
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        ((frame.clearGate depth present).program physical oracles)).matrix environment *
        (frame.circuitAtOperator physical sameWires callback record operator environment
          right (depth + 1) (by omega) (offset + 2 ^ remaining)
            (right_bound bounded) leftResult.1) *
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.nextGate depth present).program physical oracles)).matrix environment *
        (frame.circuitAtOperator physical sameWires callback record operator environment
          left (depth + 1) (by omega) offset (left_bound bounded) store) *
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (GateSpec.programList physical oracles
            (frame.leftGates depth present))).matrix environment

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

private lemma nativeFork_execute
    (first next clear : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout)
    (left right : Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (leftRecord : Store ctx → Store ctx × left.Path)
    (rightRecord : Store ctx → Store ctx × right.Path)
    (leftOperator rightOperator : Store ctx → UnitaryOperator ctx.register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    (leftEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      left.execute environment Reference state =
        (state.applyUnitary fun entry => UnitaryOperator.prodTensor (leftOperator entry.1)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := leftRecord entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (rightEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      right.execute environment Reference state =
        (state.applyUnitary fun entry => UnitaryOperator.prodTensor (rightOperator entry.1)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := rightRecord entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ((Circuit.unitary first).seq
      (left.seq ((Circuit.unitary next).seq (right.seq (Circuit.unitary clear))))).execute
        environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (clear.matrix environment.quantum * rightOperator (leftRecord entry.1).1 *
          next.matrix environment.quantum * leftOperator entry.1 * first.matrix environment.quantum)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let leftResult := leftRecord entry.1
          let rightResult := rightRecord leftResult.1
          (rightResult.1, (entry.2.1, (entry.2.2,
            ((), (leftResult.2, ((), (rightResult.2, ())))))))) := by
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq, leftEquation,
    Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq, rightEquation,
    Circuit.execute_unitary]
  simp only [State.mapHistory, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def,
    ExecutionState.executionState_applyUnitary_comp, reference_product, mul_assoc]

/-- Every true callback Store and complete retained path is present in the selector equation. -/
lemma circuitAt_execute (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (record : ∀ label, Store ctx → Store ctx × (callback label).Path)
    (operator : Fin (2 ^ width) → Store ctx → UnitaryOperator ctx.register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    (callbackEquation : ∀ label (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      (callback label).execute environment Reference state =
        (state.applyUnitary fun entry => UnitaryOperator.prodTensor (operator label entry.1)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := record label entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))))
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (frame.circuitAt physical sameWires callback tree depth fits offset bounded).execute
        environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (frame.circuitAtOperator physical sameWires callback record operator environment.quantum
          tree depth fits offset bounded entry.1) (1 : UnitaryOperator Reference)).mapClassical
            (fun entry =>
              let result := frame.circuitAtRecord physical sameWires callback record
                tree depth fits offset bounded entry.1
              (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction tree generalizing depth offset Reference History with
  | skip remaining =>
      simp only [circuitAt, Circuit.execute_id, circuitAtOperator, circuitAtRecord]
      have identity : UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
          (1 : UnitaryOperator Reference) = 1 := by
        apply Subtype.ext
        rw [unitaryOperator_prodTensor_identity]
        exact Matrix.one_kronecker_one
      have unchanged : state.applyUnitary (fun _ => UnitaryOperator.prodTensor
          (1 : UnitaryOperator ctx.register) (1 : UnitaryOperator Reference)) = state := by
        apply ExecutionState.ext
        intro entry
        rw [ExecutionState.applyUnitary_block, identity, DensityOperator.applyUnitary_one]
      rw [unchanged]
      exact ExecutionState.executionState_mapClassical_congr _ rfl
  | leaf => exact callbackEquation _ Reference state
  | @fork remaining left right leftIH rightIH =>
      have joined := nativeFork_execute
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (GateSpec.programList physical oracles (frame.leftGates depth (by omega))))
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.nextGate depth (by omega)).program physical oracles))
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.clearGate depth (by omega)).program physical oracles))
        (frame.circuitAt physical sameWires callback left (depth + 1) (by omega)
          offset (left_bound bounded))
        (frame.circuitAt physical sameWires callback right (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded))
        (frame.circuitAtRecord physical sameWires callback record left (depth + 1) (by omega)
          offset (left_bound bounded))
        (frame.circuitAtRecord physical sameWires callback record right (depth + 1) (by omega)
          (offset + 2 ^ remaining) (right_bound bounded))
        (frame.circuitAtOperator physical sameWires callback record operator environment.quantum
          left (depth + 1) (by omega) offset (left_bound bounded))
        (frame.circuitAtOperator physical sameWires callback record operator environment.quantum
          right (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded))
        environment
        (leftIH (depth + 1) (by omega) offset (left_bound bounded))
        (rightIH (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded))
        Reference state
      simp only [circuitAt, placedCircuit, circuitAtOperator, circuitAtRecord] at joined ⊢
      exact joined.trans (ExecutionState.executionState_mapClassical_congr _ rfl)

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

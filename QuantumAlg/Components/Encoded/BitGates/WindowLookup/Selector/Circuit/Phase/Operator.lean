/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Circuit.Phase.Selection

/-!
# Selected scalar of the actual hybrid selector operator

Each supplied callback operator is the one in its actual complete execution
equation. Its chronological record preserves the original measured-mask
observation. On clean prefixes the native traversal contributes exactly the
selected callback phase and restores the complete original physical label.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

/-- The original complete encoded vector on precisely the same physical runtime wires. -/
def ctxVector (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires) (state : Data) :
    HilbertVector ctx.register :=
  (NormalizedVector.ket (R := ctx.register)
    (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (physical.basisEquiv.symm (encoding.encode state)))).vec

/-- Actual callback operators select the original protected phase and restore all clean prefixes. -/
lemma circuitAtOperator_selectedPhase {Value : Type} (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (callback : Fin (2 ^ width) →
      Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx false)
    (record : ∀ label, Store ctx → Store ctx × (callback label).Path)
    (operator : Fin (2 ^ width) → Store ctx → UnitaryOperator ctx.register)
    (observe : Store ctx → Value)
    (preserved : ∀ label store, observe (record label store).1 = observe store)
    (phase : Fin (2 ^ width) → Value → Data → ℂ)
    (independent : ∀ label value index state,
      phase label value ((frame.stack index).flip state) = phase label value state)
    (callbacks : ∀ label store state,
      (operator label store).applyVec (ctxVector physical sameWires state) =
        (if (frame.stack ⟨width, by omega⟩).get state then phase label (observe store) state
          else 1) • ctxVector physical sameWires state)
    (environment : oracles.Interpretation)
    {remaining : Nat} (tree : SelectorTrie remaining) (depth : Nat)
    (fits : depth + remaining = width) (offset : Nat)
    (bounded : offset + 2 ^ remaining ≤ 2 ^ width) (store : Store ctx) (state : Data)
    (clean : frame.CleanFrom depth state) :
    (frame.circuitAtOperator physical sameWires callback record operator environment
      tree depth fits offset bounded store).applyVec (ctxVector physical sameWires state) =
        (if (frame.stack ⟨depth, by omega⟩).get state then
          frame.selectedPhaseAt (fun label => phase label (observe store))
            tree depth fits offset bounded state else 1) • ctxVector physical sameWires state := by
  induction tree generalizing depth offset store state with
  | skip remaining =>
      simp only [circuitAtOperator, selectedPhaseAt, UnitaryOperator.one_applyVec,
        ite_self, one_smul]
  | leaf =>
      have current : depth = width := by omega
      subst depth
      exact callbacks _ store state
  | @fork remaining left right leftIH rightIH =>
      let present : depth < width := by omega
      let prepared := zeroChildStep (frame.enableAt depth present) (frame.addressAt depth present)
        (frame.prefixAt depth present) state
      let switched := (frame.nextGate depth present).step prepared
      let leftStore := (frame.circuitAtRecord physical sameWires callback record left
        (depth + 1) (by omega) offset (left_bound bounded) store).1
      have preparedClean := frame.cleanFrom_zeroChild depth present state clean
      have switchedClean := frame.cleanFrom_next depth present prepared preparedClean
      have leftActual := leftIH (depth + 1) (by omega) offset (left_bound bounded)
        store prepared preparedClean
      have rightActual := rightIH (depth + 1) (by omega) (offset + 2 ^ remaining)
        (right_bound bounded) leftStore switched switchedClean
      have originalObservation := frame.circuitAtRecord_observe physical sameWires callback record
        observe preserved left (depth + 1) (by omega) offset (left_bound bounded) store
      change observe leftStore = observe store at originalObservation
      rw [originalObservation] at rightActual
      have firstActual := placedProgram_applyVec physical sameWires
        (GateSpec.programList physical oracles (frame.leftGates depth present))
        (GateSpec.stepList (frame.leftGates depth present)) environment
        (GateSpec.realizesList physical oracles _ environment) state
      rw [frame.leftGates_step] at firstActual
      have nextActual := placedProgram_applyVec physical sameWires
        ((frame.nextGate depth present).program physical oracles)
        (frame.nextGate depth present).step environment
        (GateSpec.realizes physical oracles _ environment) prepared
      have clearActual := placedProgram_applyVec physical sameWires
        ((frame.clearGate depth present).program physical oracles)
        (frame.clearGate depth present).step environment
        (GateSpec.realizes physical oracles _ environment) switched
      have restored := frame.nativeFork_step_clean remaining depth fits offset bounded state clean
      rw [frame.leftGates_step] at restored
      change (frame.clearGate depth present).step switched = state at restored
      rw [restored] at clearActual
      change UnitaryOperator.applyVec _ (ctxVector physical sameWires state) =
        ctxVector physical sameWires prepared at firstActual
      change UnitaryOperator.applyVec _ (ctxVector physical sameWires prepared) =
        ctxVector physical sameWires switched at nextActual
      change UnitaryOperator.applyVec _ (ctxVector physical sameWires switched) =
        ctxVector physical sameWires state at clearActual
      change ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.clearGate depth present).program physical oracles)).matrix environment *
        frame.circuitAtOperator physical sameWires callback record operator environment right
          (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded) leftStore *
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          ((frame.nextGate depth present).program physical oracles)).matrix environment *
        frame.circuitAtOperator physical sameWires callback record operator environment left
          (depth + 1) (by omega) offset (left_bound bounded) store *
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (GateSpec.programList physical oracles (frame.leftGates depth present))).matrix
            environment).applyVec (ctxVector physical sameWires state) = _
      rw [UnitaryOperator.mul_applyVec, firstActual, UnitaryOperator.mul_applyVec, leftActual,
        UnitaryOperator.applyVec_smul, UnitaryOperator.mul_applyVec, nextActual,
        UnitaryOperator.mul_applyVec, rightActual, UnitaryOperator.applyVec_smul, clearActual]
      have leftPhase := frame.selectedPhaseAt_zeroChild
        (fun label => phase label (observe store)) (fun label index value =>
          independent label (observe store) index value)
        left (depth + 1) (by omega) offset (left_bound bounded) depth present state
      have rightPhase := (frame.selectedPhaseAt_nextChild
        (fun label => phase label (observe store)) (fun label index value =>
          independent label (observe store) index value)
        right (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
          depth present prepared).trans
        (frame.selectedPhaseAt_zeroChild
          (fun label => phase label (observe store)) (fun label index value =>
            independent label (observe store) index value)
          right (depth + 1) (by omega) (offset + 2 ^ remaining) (right_bound bounded)
            depth present state)
      rw [leftPhase, rightPhase, smul_smul]
      apply congrArg (fun scalar : ℂ => scalar • ctxVector physical sameWires state)
      have prefixZero := clean ⟨depth, present⟩ (Nat.le_refl _)
      change (frame.prefixAt depth present).get state = false at prefixZero
      have prefixValues := frame.nativeFork_prefix_values depth present state prefixZero
      change (if (frame.prefixAt depth present).get prepared then _ else 1) *
        (if (frame.prefixAt depth present).get switched then _ else 1) = _
      rw [prefixValues.1, prefixValues.2]
      change (if (frame.enableAt depth present).get state &&
          !(frame.addressAt depth present).get state then _ else 1) *
        (if (frame.enableAt depth present).get state &&
          (frame.addressAt depth present).get state then _ else 1) =
        if (frame.enableAt depth present).get state then
          (if (frame.addressAt depth present).get state then _ else _) else 1
      cases enabled : (frame.enableAt depth present).get state <;>
        cases selected : (frame.addressAt depth present).get state <;> simp

end

end QuantumAlg.EncodedBit.WindowLookup.SelectorFrame

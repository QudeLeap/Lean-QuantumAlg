/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout

/-!
# Actual controlled high-word complement in the HRS bridge

One CNOT per high bit performs the conditional inversion used to cancel the
unknown initial dirty control [HRS16, paper.tex:224-226]. The entire low word
and the dirty bit are preserved. The same list proves action and resources.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

private def highWord (low high : Nat) : EncodedBit.Word (bridgeEncoding low high) high :=
  ⟨bridgeHighBit low high⟩

private def highOnes (high : Nat) : Fin (2 ^ high) :=
  ⟨2 ^ high - 1, by have := Nat.two_pow_pos high; omega⟩

private theorem highOnes_testBit (high : Nat) (bit : Fin high) :
    (highOnes high).val.testBit bit.val = true := by
  simp [highOnes, bit.isLt]

/-- Literal dirty-controlled CNOT list, including the empty high word. -/
def controlledComplementGates (low high : Nat) :
    List (EncodedBit.GateSpec (bridgeEncoding low high)) :=
  List.ofFn fun bit : Fin high =>
    .cnot (bridgeDirtyBit low high) (bridgeHighBit low high bit)
      (Ne.symm (hrsBridgeHighDirty_disjoint low high bit))

/-- Compile the actual CNOT list on the shared low/high/dirty carrier. -/
def controlledComplementProgram (low high : Nat) :
    UnitaryCircuit (Qubits (bridgeEncoding low high).width) :=
  programList (controlledComplementGates low high)

private theorem gates_eq_constantXor (low high : Nat) :
    controlledComplementGates low high =
      EncodedBit.Word.controlledXorConstantGates (bridgeDirtyBit low high)
        (highWord low high) (highOnes high)
        (fun bit => Ne.symm (hrsBridgeHighDirty_disjoint low high bit)) := by
  have hbits : (fun bit : Fin high => (highOnes high).val.testBit bit.val) =
      fun _ => true := by
    funext bit
    exact highOnes_testBit high bit
  simp only [EncodedBit.Word.controlledXorConstantGates,
    EncodedBit.Word.constantOneIndices, hbits]
  simp [controlledComplementGates, highWord, Function.comp_def]

/-- Every joint input, including an arbitrary dirty control, has the required action. -/
theorem hrsControlledComplement_step (low high : Nat)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    stepList (controlledComplementGates low high) state = bridgeComplementStep state := by
  rw [gates_eq_constantXor]
  change EncodedBit.Word.controlledXorConstantStep (bridgeDirtyBit low high)
    (highWord low high) (highOnes high) _ state = _
  by_cases hdirty : state.2 = true
  · simp only [bridgeComplementStep, hdirty, if_true]
    apply Prod.ext
    · apply Prod.ext
      · apply Nat.FixedWidth.word_eq_of_testBit_eq
        intro bit
        have h := EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
          (bridgeDirtyBit low high) (highWord low high) (highOnes high)
          (fun bit => Ne.symm (hrsBridgeHighDirty_disjoint low high bit))
          (bridgeLowBit low high bit)
          (fun other => Ne.symm (hrsBridgeLowHigh_disjoint low high bit other)) state
        simpa only [hrsBridgeLowBit_get] using h
      · apply Nat.FixedWidth.word_eq_of_testBit_eq
        intro bit
        have h := EncodedBit.Word.controlledXorConstantStep_get_target
          (bridgeDirtyBit low high) (highWord low high) (highOnes high)
          (fun bit => Ne.symm (hrsBridgeHighDirty_disjoint low high bit)) bit
          (fun other hne => hrsBridgeHighHigh_disjoint low high other bit hne) state
        change (bridgeHighBit low high bit).get _ =
          ((bridgeHighBit low high bit).get state ^^
            ((bridgeDirtyBit low high).get state && (highOnes high).val.testBit bit.val)) at h
        simpa only [hrsBridgeHighBit_get, hrsBridgeDirtyBit_get, hdirty,
          highOnes_testBit, Bool.true_and, Bool.xor_true, hrsComplementWord_testBit] using h
    · have h := EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (bridgeDirtyBit low high) (highWord low high) (highOnes high)
        (fun bit => Ne.symm (hrsBridgeHighDirty_disjoint low high bit))
        (bridgeDirtyBit low high) (hrsBridgeHighDirty_disjoint low high) state
      simpa only [hrsBridgeDirtyBit_get, hdirty] using h
  · have hfalse : state.2 = false := Bool.eq_false_iff.mpr hdirty
    simp only [bridgeComplementStep, hfalse, Bool.false_eq_true, if_false]
    exact EncodedBit.Word.controlledXorConstantStep_eq_self_of_control_false
      (bridgeDirtyBit low high) (highWord low high) (highOnes high)
      (fun bit => Ne.symm (hrsBridgeHighDirty_disjoint low high bit)) state hfalse

/-- The real CNOT program realizes the exact conditional complement without phase. -/
theorem hrsControlledComplement_realizes (low high : Nat) :
    UnitaryCircuit.Realizes (bridgeEncoding low high)
      (controlledComplementProgram low high) bridgeComplementStep :=
  realizesList_congrStep (controlledComplementGates low high)
    (hrsControlledComplement_step low high)

/-- Native coordinates of the actual high-word CNOT list. -/
theorem hrsControlledComplement_native_count (low high : Nat)
    (focus : Resource.Event .quantum) :
    ResourcePool.count focus (controlledComplementProgram low high).eventCost =
      high * (if (.gate (.builtin "cnot") : Resource.Event .quantum) = focus then 1 else 0) := by
  rw [controlledComplementProgram, programList_event_count_eq_sum_eventMultiplicity]
  by_cases h : (.gate (.builtin "cnot") : Resource.Event .quantum) = focus
  · simp [controlledComplementGates, eventMultiplicity, event, List.sum_ofFn, h]
  · simp [controlledComplementGates, eventMultiplicity, event, List.sum_ofFn, h]

/-- A shared dirty control is executed serially, once per high bit. -/
theorem hrsControlledComplement_serial_resources (low high : Nat) :
    (controlledComplementProgram low high).eventCost.card = high ∧
      (controlledComplementProgram low high).evaluatedEventDepth (fun _ => 1) = high := by
  change (programList (controlledComplementGates low high)).eventCost.card = high ∧
    (programList (controlledComplementGates low high)).evaluatedEventDepth (fun _ => 1) = high
  rw [programList_eventCost_card, programList_evaluatedEventDepth_unit]
  simp [controlledComplementGates]

end

end QuantumAlg.MAU.Addition.HRS

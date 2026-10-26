/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase.Program
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Resources

/-!
# Actual masked parity-phase native counts and parallel depth

A nonempty mask of weight m executes 2m-1 CNOTs and the pivot's two literal
Hadamards. The original independent layers and their actual inverse give
quantum depth at most twice the binary height plus three. Empty masks emit
identity, and no target initialization or additional quantum system is used.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Transposition and reversed traversal retain every actual original CNOT occurrence. -/
lemma parityFanInWord_size (layers : List (CnotLayer encoding)) :
    layerWordSize (parityFanInWord layers) = layerWordSize layers := by
  simp only [parityFanInWord, layerWordSize, List.map_map, Function.comp_def,
    CnotLayer.transpose, List.length_map, List.map_reverse, List.sum_reverse]

/-- The literal native trace includes every fan-in CNOT, both H gates, and the inverse CNOTs. -/
lemma conjugatedParityPhaseProgram_eventTrace (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire) :
    (conjugatedParityPhaseProgram physical oracles layers selector pivot different).eventTrace =
      List.replicate (layerWordSize layers) (.gate .cnot) ++
        ([.gate .singleQubit, .gate .cnot, .gate .singleQubit] ++
          List.replicate (layerWordSize layers) (.gate .cnot)) := by
  rw [conjugatedParityPhaseProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace,
    layerWordProgram_eventTrace, layerWordProgram_eventTrace, inverseLayerWord_size,
    controlledZ, conjugateHadamard_eventTrace, GateSpec.program_eventTrace]
  rfl

/-- Every actual CNOT is retained in the mask-parity construction's selected coordinate. -/
lemma conjugatedParityPhaseProgram_cnot_count (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (conjugatedParityPhaseProgram physical oracles layers selector pivot different).eventCost =
        2 * layerWordSize layers + 1 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    conjugatedParityPhaseProgram_eventTrace]
  simp [ResourcePool.ofList, ResourcePool.count]
  omega

/-- Both pivot Hadamards are actual single-qubit events, with no omitted basis change. -/
lemma conjugatedParityPhaseProgram_singleQubit_count (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (conjugatedParityPhaseProgram physical oracles layers selector pivot different).eventCost =
        2 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    conjugatedParityPhaseProgram_eventTrace]
  have differentEvent : (Resource.Event.gate .singleQubit :
      Resource.Event (.quantum AlgorithmGate.model oracles)) ≠ .gate .cnot := by
    intro same
    have coordinates := Resource.Event.gate.inj same
    cases coordinates
  simp [ResourcePool.ofList, ResourcePool.count, List.count_replicate, beq_iff_eq,
    Ne.symm differentEvent]

/-- The actual parallel fan-in, three native pivot gates, and actual inverse retain dependency. -/
lemma conjugatedParityPhaseProgram_quantumTime_le (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (conjugatedParityPhaseProgram physical oracles layers selector pivot different) ≤
        2 * layers.length + 3 := by
  have forward := layerWordProgram_quantumTime_le physical oracles layers
  have backward := layerWordProgram_quantumTime_le physical oracles (inverseLayerWord layers)
  rw [inverseLayerWord_length] at backward
  have pivotTime : (selector.controlledZ physical oracles pivot different).evaluatedEventDepth
      Resource.Event.quantumDuration = 3 := rfl
  rw [conjugatedParityPhaseProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, pivotTime]
  omega

variable {count : Nat}

/-- A complete selected mask retains exactly 2m-1 actual CNOTs, or zero for an empty mask. -/
lemma maskedParityPhaseProgram_cnot_count (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (maskedParityPhaseProgram physical oracles target distinct selector outside
        height).eventCost =
        if count = 0 then 0 else 2 * count - 1 := by
  unfold maskedParityPhaseProgram
  split
  · rw [conjugatedParityPhaseProgram_cnot_count, parityFanInWord_size]
    have size := doublingWord_size target distinct height
    rw [Nat.min_eq_left ‹0 < count›, Nat.min_eq_right covered] at size
    rw [if_neg (by omega)]
    omega
  · have empty : count = 0 := by omega
    subst count
    rfl

/-- Only a nonempty mask executes its two literal pivot Hadamards. -/
lemma maskedParityPhaseProgram_singleQubit_count (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (maskedParityPhaseProgram physical oracles target distinct selector outside
        height).eventCost =
        if count = 0 then 0 else 2 := by
  unfold maskedParityPhaseProgram
  split
  · rw [conjugatedParityPhaseProgram_singleQubit_count, if_neg (by omega)]
  · have empty : count = 0 := by omega
    subst count
    rfl

/-- The concrete actual fan-in has logarithmic native quantum depth on arbitrary targets. -/
lemma maskedParityPhaseProgram_quantumTime_le (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (maskedParityPhaseProgram physical oracles target distinct selector outside height) ≤
        2 * height + 3 := by
  unfold maskedParityPhaseProgram
  split
  · have actual := conjugatedParityPhaseProgram_quantumTime_le physical oracles
      (parityFanInWord (doublingWord target distinct height)) selector (target ⟨0, ‹0 < count›⟩)
        (outside ⟨0, ‹0 < count›⟩)
    simpa only [parityFanInWord_length, doublingWord_length] using actual
  · exact Nat.zero_le _

end

end QuantumAlg.EncodedBit.WindowLookup

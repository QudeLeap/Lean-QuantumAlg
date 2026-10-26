/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Count

/-!
# Actual paid-row native quantum coordinate counts

The actual classical AND/XOR rows emit no quantum gate coordinate. The stored parity vector
selects the actual masked fan-in phase on its same supplied result wires.
The selected native program contributes no Toffoli, at most two H events,
and at most twice the original unary range minus one CNOT events.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Paid native classical parity rows emit no quantum gate coordinates. -/
lemma rowProgram_gate_count (coordinate : AlgorithmGate.Coordinate)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (indices : List (Fin columns))
    (path : (rowProgram (oracles := oracles) (services := services)
      measured parity temporary table indices).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate)
        ((rowProgram measured parity temporary table indices).resourcePool path) = 0 := by
  induction indices with
  | nil =>
      dsimp only [rowProgram, Circuit.Path] at path
      cases path
      simp [rowProgram, Circuit.resourcePool, Circuit.eventTrace]
  | cons index rest ih =>
      dsimp only [rowProgram, Circuit.Path] at path
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
        (((RuntimeParity.program (oracles := oracles) (services := services)
          (parity index) temporary (RuntimeParity.inputs (table index) measured)).seq
            (rowProgram measured parity temporary table rest)).resourcePool path) = 0
      rw [Circuit.resourcePool_count_seq, RuntimeParity.program_gate_count, ih, Nat.zero_add]

/-- Every actual stored parity branch pays precisely its selected native program's gate bound. -/
lemma rowCircuit_gate_count_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (coordinate : AlgorithmGate.Coordinate) (bound : Nat)
    (nativeBound : ∀ value, ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate coordinate)
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside value
        height).eventCost ≤ bound)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity temporary table target distinct selector outside height).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate coordinate) ((rowCircuit physical sameWires measured parity temporary table target
        distinct
        selector outside height).resourcePool path) ≤ bound := by
  dsimp only [rowCircuit, SelectorFrame.placedCircuit, Circuit.Path] at path
  have first := rowProgram_gate_count coordinate measured parity temporary table
    (List.ofFn fun index : Fin columns => index) path.1
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
    (ResourcePool.ofList
    ((rowProgram (oracles := oracles) (services := services) measured parity temporary table
      (List.ofFn fun index : Fin columns => index)).eventTrace path.1 ++
        (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordMaskParityPhaseProgram physical oracles target distinct selector outside
            (MaskParity.storedConstant path.2.1) height)).eventTrace BitWord.model services)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model oracles BitWord.model services) (.gate coordinate)
    ((rowProgram (oracles := oracles) (services := services) measured parity temporary table
      (List.ofFn fun index : Fin columns => index)).resourcePool path.1) + _ ≤ _
  rw [first, Nat.zero_add,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    unitaryOfEqualWires_cost, UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  exact nativeBound _

private lemma wordPhase_toffoli_count (physical : QubitLayout encoding.width)
    (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (value : Fin (2 ^ columns)) (height : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside value
        height).eventCost = 0 := by
  unfold wordMaskParityPhaseProgram maskedParityPhaseProgram
  split
  · rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      conjugatedParityPhaseProgram_eventTrace, ResourcePool.count_ofList]
    simp [List.count_append, List.count_replicate, beq_iff_eq]
  · rfl

/-- No actual row feedback path contains a native Toffoli event. -/
lemma rowCircuit_toffoli_count (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity temporary table target distinct selector outside height).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate .toffoli) ((rowCircuit physical sameWires measured parity temporary table target
        distinct
        selector outside height).resourcePool path) = 0 := by
  apply Nat.le_zero.mp
  exact rowCircuit_gate_count_le physical sameWires measured parity temporary table
    target distinct selector
    outside height .toffoli 0
    (fun value => Nat.le_of_eq (wordPhase_toffoli_count physical target distinct selector outside
      value height)) path

/-- Every nonempty actual feedback mask retains at most its two original native H events. -/
lemma rowCircuit_singleQubit_count_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity temporary table target distinct selector outside height).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate .singleQubit) ((rowCircuit physical sameWires measured parity temporary table target
        distinct
        selector outside height).resourcePool path) ≤ 2 := by
  apply rowCircuit_gate_count_le physical sameWires measured parity temporary table
    target distinct selector
    outside height .singleQubit 2
  intro value
  have actual := maskedParityPhaseProgram_singleQubit_count physical oracles
    (constantMaskTarget target value) (constantMaskTarget_distinct target distinct value) selector
    (fun index => outside ((Word.constantOneIndices value).get index)) height
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
    (wordMaskParityPhaseProgram physical oracles target distinct selector outside value
      height).eventCost = _ at actual
  rw [actual]
  split <;> omega

/-- Actual fan-in and inverse pay at most twice the original low unary range minus one CNOT. -/
lemma rowCircuit_cnot_count_le (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (target : Word encoding columns)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire) (height : Nat)
    (covered : columns ≤ 2 ^ height)
    (path : (rowCircuit (oracles := oracles) (services := services) physical sameWires
      measured parity temporary table target distinct selector outside height).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles BitWord.model services)
      (.gate .cnot) ((rowCircuit physical sameWires measured parity temporary table target
        distinct selector
        outside height).resourcePool path) ≤ 2 * columns - 1 := by
  apply rowCircuit_gate_count_le physical sameWires measured parity temporary table
    target distinct selector
    outside height .cnot (2 * columns - 1)
  intro value
  have selected := Word.constantOneIndices_length_le value
  have actual := maskedParityPhaseProgram_cnot_count physical oracles
    (constantMaskTarget target value) (constantMaskTarget_distinct target distinct value) selector
    (fun index => outside ((Word.constantOneIndices value).get index)) height
    (selected.trans covered)
  change ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
    (wordMaskParityPhaseProgram physical oracles target distinct selector outside value
      height).eventCost = _ at actual
  rw [actual]
  split <;> omega

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

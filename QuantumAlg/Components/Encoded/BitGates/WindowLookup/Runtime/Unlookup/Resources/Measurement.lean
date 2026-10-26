/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Resources.Restoration
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Resources

/-!
# Exact measurements and supplied-system reuse of actual unlookup

Every real MZ occurs in the original result-word reset. All subsequent
classical parity computations and native unary/feedback/inverse programs add
no measurement or allocation. Unary targets are certified positions of those
same original result systems; the complete caller context is the exact peak.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma weightedIndicator {model : ExecutionModel} (focus : Resource.Event model)
    (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun event => if event = focus then 1 else 0) pool =
      ResourcePool.count focus pool := by
  classical
  induction pool using Multiset.induction_on with
  | empty => rfl
  | cons event rest ih =>
      simp only [ResourcePool.weightedCount, Multiset.map_cons, Multiset.sum_cons,
        ResourcePool.count, Multiset.count_cons]
      rw [show (rest.map (fun event => if event = focus then 1 else 0)).sum =
        Multiset.count focus rest from ih]
      by_cases same : event = focus
      · simp [same, Nat.add_comm]
      · simp [same, Ne.symm same]

private lemma parityFold_measurement_count (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (RuntimeParity.foldProgram (oracles := .empty) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((RuntimeParity.foldProgram parity temporary pairs).resourcePool
        path) = 0 := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) (ResourcePool.ofList
          ([.classicalOperation (.bit .and), .classicalOperation (.bit .xor)] ++
            (RuntimeParity.foldProgram parity temporary rest).eventTrace path.2)) = 0
      rw [ResourcePool.ofList_append, ResourcePool.count_add]
      change 0 + ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        ((RuntimeParity.foldProgram parity temporary rest).resourcePool path.2) = 0
      rw [ih]

private lemma parityProgram_measurement_count (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (path : (RuntimeParity.program (oracles := .empty) (services := services)
      parity temporary pairs).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((RuntimeParity.program parity temporary pairs).resourcePool path) =
        0 := by
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) (ResourcePool.ofList
      ([.classicalOperation (.bit .xor)] ++
        (RuntimeParity.foldProgram parity temporary pairs).eventTrace path.2)) = 0
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change 0 + ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+))
    ((RuntimeParity.foldProgram parity temporary pairs).resourcePool path.2) = 0
  rw [parityFold_measurement_count]

private lemma rowProgram_measurement_count {wordWidth columns : Nat}
    (measured : CInputRef ctx (.bits wordWidth)) (parity : Fin columns → CWriteRef ctx .bit)
    (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (indices : List (Fin columns))
    (path : (RuntimeRow.rowProgram (oracles := .empty) (services := services)
      measured parity temporary table indices).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((RuntimeRow.rowProgram measured parity temporary table indices).resourcePool path) = 0 := by
  induction indices with
  | nil =>
      dsimp only [RuntimeRow.rowProgram, Circuit.Path] at path
      cases path
      simp [RuntimeRow.rowProgram, Circuit.resourcePool, Circuit.eventTrace]
  | cons index rest ih =>
      dsimp only [RuntimeRow.rowProgram, Circuit.Path] at path
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        (((RuntimeParity.program (oracles := .empty) (services := services)
          (parity index) temporary (RuntimeParity.inputs (table index) measured)).seq
            (RuntimeRow.rowProgram measured parity temporary table rest)).resourcePool path) = 0
      rw [Circuit.resourcePool_count_seq, parityProgram_measurement_count, ih, Nat.zero_add]


variable {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (measured : CInputRef ctx (.bits resultWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
  (temporary : CWriteRef ctx .bit)

private lemma halfCallback_measurement_count
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (label : Fin (2 ^ highRemaining))
    (path : (halfCallback frame (services := services)
      physical sameWires measured parity temporary table label).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((halfCallback frame physical sameWires measured parity temporary
        table label).resourcePool path) =
        0 := by
  dsimp only [halfCallback, RuntimeRow.rowCircuit, SelectorFrame.placedCircuit,
    Circuit.Path] at path
  have first := rowProgram_measurement_count measured parity temporary (table label)
    (List.ofFn fun index : Fin (2 ^ lowWidth) => index) path.1
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
    (ResourcePool.ofList
      ((RuntimeRow.rowProgram (oracles := .empty) (services := services) measured parity temporary
        (table label) (List.ofFn fun index : Fin (2 ^ lowWidth) => index)).eventTrace path.1 ++
      (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (wordMaskParityPhaseProgram physical .empty frame.lowWord frame.low.targetDistinct
          (frame.high.stack ⟨highRemaining, by omega⟩) (frame.highStack_lowWord _)
          (MaskParity.storedConstant path.2.1) lowWidth)).eventTrace BitWord.model services)) = 0
  dsimp only [UnlookupFrame.lowWord] at first ⊢
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+))
    ((RuntimeRow.rowProgram (oracles := .empty) (services := services)
      measured parity temporary (table label)
      (List.ofFn fun index : Fin (2 ^ lowWidth) => index)).resourcePool
        path.1) + _ = 0
  rw [first, Nat.zero_add,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ BitWord.model services,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]

private lemma halfCircuit_measurement_count
    (table : Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
      CInputRef ctx (.unsignedWord resultWidth))
    (path : (halfCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((halfCircuit frame physical sameWires measured parity temporary
        table).resourcePool path) = 0 := by
  classical
  have actual := frame.high.circuitAt_weight_le physical sameWires
    (halfCallback frame (services := services) physical sameWires measured parity temporary table)
    (fun event => if event = .measurement (2 : ℕ+) then 1 else 0) 0
    (fun label current => by
      rw [weightedIndicator, halfCallback_measurement_count frame])
    (SelectorTrie.full highRemaining) 0 (by omega) 0 (by omega) path
  simp only [weightedIndicator, SelectorFrame.hybridForkWeight, reduceCtorEq,
    ↓reduceIte, Nat.mul_zero, Nat.add_zero] at actual
  simpa only [halfCircuit, SelectorFrame.circuit] using Nat.le_zero.mp actual

variable (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) →
  CInputRef ctx (.unsignedWord resultWidth))

private lemma phaseCircuit_measurement_count
    (path : (phaseCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((phaseCircuit frame physical sameWires measured parity temporary
        table).resourcePool path) = 0 := by
  have arithmetic
      (left right : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services))
      (leftZero : ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) left = 0)
      (rightZero : ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) right = 0) :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        (ResourcePool.ofList
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          [.gate .singleQubit] +
          (left + (ResourcePool.ofList
            (model := .quantum AlgorithmGate.model .empty BitWord.model services)
            [.gate .singleQubit] + right))) = 0 := by
    rw [ResourcePool.count_add, ResourcePool.count_add, ResourcePool.count_add,
      leftZero, rightZero]
    rfl
  exact (congrArg (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+)))
    (phaseCircuit_resourcePool frame physical sameWires measured parity temporary table path)).trans
      (arithmetic _ _
        (halfCircuit_measurement_count frame physical sameWires measured parity
          temporary (table false)
          path.2.1)
        (halfCircuit_measurement_count frame physical sameWires measured parity
          temporary (table true)
          path.2.2.2))

/-- The original unary preparation, every paid row and native inverse add no measurement. -/
lemma restorationCircuit_measurement_count
    (path : (restorationCircuit frame (services := services)
      physical sameWires measured parity temporary table).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((restorationCircuit frame physical sameWires measured parity temporary
        table).resourcePool path) =
        0 := by
  have arithmetic
      (middle : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services))
      (zero : ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) middle = 0) :
      ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        ((frame.low.program physical .empty).eventCost BitWord.model services +
          (middle + (frame.low.uncomputeProgram physical).eventCost BitWord.model services)) =
        0 := by
    rw [ResourcePool.count_add, ResourcePool.count_add,
      UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (frame.low.program physical .empty) BitWord.model services (.measurement (2 : ℕ+)),
      UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (frame.low.uncomputeProgram physical) BitWord.model services (.measurement (2 : ℕ+))]
    change 0 + (ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) middle + 0) = 0
    rw [zero]
  exact (congrArg (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.measurement (2 : ℕ+)))
    (restorationCircuit_resourcePool frame physical sameWires measured parity temporary
      table path)).trans
      (arithmetic _ (phaseCircuit_measurement_count frame physical sameWires measured parity
        temporary table
        path.2.1))

/-- Exactly one actual MZ per original result system occurs in the full unlookup circuit. -/
lemma circuit_measurement_count (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (path : (circuit frame (services := services)
      physical sameWires output mask parity temporary table).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((circuit frame physical sameWires output mask parity temporary table).resourcePool path) =
        resultWidth := by
  have actual := Circuit.resourcePool_count_seq
    (measuredResetWordCircuit (oracles := .empty) (services := services)
      physical sameWires frame.result frame.resultDistinct output mask)
    (restorationCircuit frame (services := services) physical sameWires
      (.storage mask.toCStorageRef) parity temporary table) (.measurement (2 : ℕ+)) path
  have first := measuredResetWordCircuit_measurement_count (oracles := .empty)
    (services := services) physical sameWires frame.result frame.resultDistinct output mask path.1
  have last := restorationCircuit_measurement_count frame physical sameWires
    (.storage mask.toCStorageRef) parity temporary table path.2
  exact actual.trans ((congrArg₂ (fun left right : Nat => left + right) first last).trans
    (Nat.add_zero _))

/-- Every unary target is the same original physical result system, after ordered-wire placement. -/
lemma reused_resultWire (index : Fin (2 ^ lowWidth)) :
    resultWire physical sameWires (frame.low.target index) =
      resultWire physical sameWires (frame.result.bit (frame.lowResult index)) :=
  congrArg (positionsOfEqualWires physical.toQuantum ctx.quantumLayout sameWires)
    (frame.lowResultWire index)

/-- The allocation-free actual circuit has exactly the caller's existing resident/auxiliary peak. -/
lemma circuit_spaces (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (path : (circuit frame (services := services)
      physical sameWires output mask parity temporary table).Path) :
    (circuit frame physical sameWires output mask parity temporary table).peakResidentSpace path =
      ctx.residentSpace ∧
    (circuit frame physical sameWires output mask parity temporary table).peakAuxiliarySpace path =
      ctx.auxiliarySpace :=
  ⟨Circuit.fixed_peakResidentSpace _ _, Circuit.fixed_peakAuxiliarySpace _ _⟩


end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeUnlookup

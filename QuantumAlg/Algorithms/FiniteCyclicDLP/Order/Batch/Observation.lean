/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Actual terminal observations of the fresh-bank sampler

The retained finite cells are distinct across both sample and exponent
coordinates. Reading one sample after the terminal measurement pass therefore
returns exactly the native Born readout of its corresponding physical bank.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Store produced by the actual terminal-measurement path for this execution
model. Naming it fixes all four model components that the path alone cannot
infer from a store. -/
@[expose] public def terminalStore (P : KnownOrderProblem G) (count : Nat)
    (store : Store (post P count)) (basis : (post P count).register.Index) :
    Store (post P count) :=
  Circuit.writeMeasurementPath (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    (allReadouts P count) store
    (Circuit.measurementBasisPath (allowAllocation := true)
      (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
      (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (allReadouts P count) basis)

/-- Decode every retained sample in chronological bank order. -/
public def observedVector (P : KnownOrderProblem G) (count : Nat)
    (value : (CShape.fixedVector count
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))).Value) :
    List.Vector (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count :=
  List.Vector.ofFn fun slot => OrderExecution.observedOutcome P (value.get slot)

/-- Read every exponent pair directly from a complete physical family basis. -/
public def observedBasisVector (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P count).Basis) :
    List.Vector (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count :=
  List.Vector.ofFn fun slot => OrderBornBridge.readout P (bankBasis P slot basis)

/-- Every pair of sample and exponent coordinates names a distinct retained cell. -/
public lemma cell_keys_injective (P : KnownOrderProblem G) (count : Nat) :
    Function.Injective (fun pair : Fin count × Fin (OrderExecution.sampleWidth P) =>
      (cell P pair.1 pair.2).key) := by
  intro left right same
  change (MeasurementCells.reference (bankContext P count) 2
      (count * OrderExecution.sampleWidth P) (finProdFinEquiv left)).key =
    (MeasurementCells.reference (bankContext P count) 2
      (count * OrderExecution.sampleWidth P) (finProdFinEquiv right)).key at same
  have flat := MeasurementCells.reference_key_injective
    (bankContext P count) 2 (count * OrderExecution.sampleWidth P) same
  exact finProdFinEquiv.injective flat

/-- No terminal readout writes a cell used by another bank or exponent position. -/
public lemma allReadouts_nodup (P : KnownOrderProblem G) (count : Nat) :
    ((allReadouts P count).map fun item => item.output.key).Nodup := by
  rw [allReadouts, List.map_flatten, List.map_ofFn]
  let keys : Fin (count * OrderExecution.sampleWidth P) → StorageKey := fun flat =>
    (cell P (finProdFinEquiv.symm flat).1 (finProdFinEquiv.symm flat).2).key
  have listed :
      List.ofFn keys =
        (List.ofFn fun slot : Fin count =>
          List.ofFn fun index : Fin (OrderExecution.sampleWidth P) =>
            (cell P slot index).key).flatten := by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext slot
    apply List.ofFn_inj.mpr
    funext index
    have flatEq :
        (⟨slot.val * OrderExecution.sampleWidth P + index.val, by
          calc
            slot.val * OrderExecution.sampleWidth P + index.val <
                (slot.val + 1) * OrderExecution.sampleWidth P :=
              (Nat.add_lt_add_left index.isLt _).trans_eq (by
                rw [Nat.add_mul, Nat.one_mul])
            _ ≤ count * OrderExecution.sampleWidth P :=
              Nat.mul_le_mul_right _ slot.isLt⟩ :
            Fin (count * OrderExecution.sampleWidth P)) =
          finProdFinEquiv (slot, index) := by
      apply Fin.ext
      change slot.val * OrderExecution.sampleWidth P + index.val =
        index.val + OrderExecution.sampleWidth P * slot.val
      rw [Nat.mul_comm slot.val, Nat.add_comm]
    change keys
      (⟨slot.val * OrderExecution.sampleWidth P + index.val, by
        calc
          slot.val * OrderExecution.sampleWidth P + index.val <
              (slot.val + 1) * OrderExecution.sampleWidth P :=
            (Nat.add_lt_add_left index.isLt _).trans_eq (by
              rw [Nat.add_mul, Nat.one_mul])
          _ ≤ count * OrderExecution.sampleWidth P :=
            Nat.mul_le_mul_right _ slot.isLt⟩ :
        Fin (count * OrderExecution.sampleWidth P)) = _
    rw [flatEq]
    unfold keys
    rw [Equiv.symm_apply_apply]
  have rows :
      List.ofFn
          ((List.map (fun item : ZReadout (post P count) => item.output.key)) ∘
            readouts (count := count) P) =
        List.ofFn (fun slot : Fin count =>
          List.ofFn fun index : Fin (OrderExecution.sampleWidth P) =>
            (cell P slot index).key) := by
    apply List.ofFn_inj.mpr
    funext slot
    unfold readouts
    change List.map (fun item : ZReadout (post P count) => item.output.key)
        (List.ofFn (readout P slot)) = _
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext index
    simpa only [Function.comp_apply, readout] using
      QubitReadouts.readout_key
        (bankPosition P slot (exponentPosition P index))
        (exponent_dimension P slot index) (cell P slot index)
  rw [rows]
  rw [← listed]
  apply List.nodup_ofFn.mpr
  intro left right same
  have pairSame : finProdFinEquiv.symm left = finProdFinEquiv.symm right := by
    apply cell_keys_injective P count
    exact same
  exact finProdFinEquiv.symm.injective pairSame

/-- A terminal cell contains the actual measured value of its physical bank wire. -/
public lemma measured_cell (P : KnownOrderProblem G) (count : Nat)
    (store : Store (post P count)) (basis : (post P count).register.Index)
    (slot : Fin count) (index : Fin (OrderExecution.sampleWidth P)) :
    ((terminalStore P count store basis).read
        (.storage (cell P slot index).toCStorageRef)).toFin.val =
      (basis (readout P slot index).wire).val := by
  have present : readout P slot index ∈ allReadouts P count := by
    rw [allReadouts, List.mem_flatten]
    exact ⟨readouts P slot, List.mem_ofFn.mpr ⟨slot, rfl⟩,
      List.mem_ofFn.mpr ⟨index, rfl⟩⟩
  have actual := Circuit.writeMeasurementBasis_read (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
    (operations := BitWord.model) (services := ClassicalFiniteGroupOracle.model G)
    (allReadouts P count)
    (allReadouts_nodup P count) (readout P slot index) present store basis
  have values := congrArg (fun value => value.toFin.val) actual
  unfold terminalStore
  exact (QubitReadouts.outputAt_read _ (exponent_dimension P slot index)
    (cell P slot index) _).symm.trans values

/-- One retained sample is exactly the source readout of its actual bank basis. -/
public lemma observedOutcome_after_measurement (P : KnownOrderProblem G) (count : Nat)
    (store : Store (post P count)) (basis : (post P count).register.Index)
    (slot : Fin count) :
    OrderExecution.observedOutcome P
        ((terminalStore P count store basis).read (sampleInput P slot)) =
      OrderBornBridge.readout P (outputBankBasis P slot basis) := by
  funext index
  change decide
      ((((terminalStore P count store basis).read
          (.storage (cell P slot index).toCStorageRef)).toFin.val) = 1) = _
  rw [measured_cell, OrderBornBridge.readout_apply]
  change decide ((basis (bankPosition P slot (exponentPosition P index))).val = 1) =
    decide (((outputBankBasis P slot basis)
      (Fin.castAdd 1 index)).val = 1)
  have position : Fin.castAdd 1 index = exponentPosition P index := by
    apply Fin.ext
    change index.val = index.val
    rfl
  rw [position, outputBankBasis_value]

/-- Reading the complete retained vector after the terminal measurement pass
is the bankwise Born readout of the same physical family basis. -/
public lemma observedVector_after_measurement (P : KnownOrderProblem G) (count : Nat)
    (store : Store (post P count)) (basis : (post P count).register.Index) :
    observedVector P count
        ((terminalStore P count store basis).read (samplesInput P count)) =
      observedBasisVector P count (basisEquiv P count basis) := by
  apply List.Vector.ext
  intro slot
  simpa only [observedVector, observedBasisVector, List.Vector.get_ofFn,
    samplesInput, CShape.Value.get, Store.read, outputBankBasis] using
      observedOutcome_after_measurement P count store basis slot

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Sequence

/-!
# Executed readout law of the known-order sampler

The retained finite cells expose the same ordered exponent outcome as the
native-dimensional Born construction. The comparison follows corresponding
physical wire values and the exact source circuit matrix.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Interpret the two-valued retained cells as their ordered terminal bits. -/
public def observedOutcome (P : KnownOrderProblem G)
    (value : (CShape.fixedVector (sampleWidth P) (.finite 2)).Value) :
    TerminalZMeasure.Outcome (sampleWidth P) :=
  fun index => decide ((value.get index).toFin.val = 1)

/-- Every exponent position writes a distinct retained cell. -/
public lemma readouts_nodup (P : KnownOrderProblem G) :
    ((readouts P).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  dsimp only [Function.comp_apply] at same
  rw [readout_output_key, readout_output_key] at same
  exact MeasurementCells.reference_key_injective
    (bankContext P) 2 (sampleWidth P) same

/-- Each retained cell contains the actual finite value measured at its named
physical exponent wire. -/
public lemma measured_cell (P : KnownOrderProblem G)
    (store : Store (post P)) (basis : (post P).register.Index)
    (index : Fin (sampleWidth P)) :
    ((Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
      (oracles := OrderOracle.model P) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G) (readouts P) store
      (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := OrderOracle.model P) (operations := BitWord.model)
        (classicalOracles := ClassicalFiniteGroupOracle.model G) (readouts P) basis)).read
        (.storage (cell P index).toCStorageRef)).toFin.val =
      (basis (readout P index).wire).val := by
  have actual := Circuit.writeMeasurementBasis_read (allowAllocation := true)
    (gates := AlgorithmGate.model)
    (oracles := OrderOracle.model P) (operations := BitWord.model)
    (services := ClassicalFiniteGroupOracle.model G) (readouts P) (readouts_nodup P)
    (readout P index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  simp only [readout, Execution.QubitReadouts.readout] at numeric
  rw [Execution.QubitReadouts.outputAt_read] at numeric
  exact numeric

/-- Reading all retained cells yields exactly the source Born readout for the
corresponding complete physical basis label. -/
public lemma observedOutcome_after_measurement (P : KnownOrderProblem G)
    (store : Store (post P)) (basis : (post P).register.Index) :
    observedOutcome P
        ((Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
          (oracles := OrderOracle.model P) (operations := BitWord.model)
          (classicalOracles := ClassicalFiniteGroupOracle.model G) (readouts P) store
          (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
            (oracles := OrderOracle.model P) (operations := BitWord.model)
            (classicalOracles := ClassicalFiniteGroupOracle.model G)
            (readouts P) basis)).read (sampleInput P)) =
      OrderBornBridge.readout P (basisEquiv P basis) := by
  funext index
  change decide
      ((((Circuit.writeMeasurementPath (allowAllocation := true) (gates := AlgorithmGate.model)
        (oracles := OrderOracle.model P) (operations := BitWord.model)
        (classicalOracles := ClassicalFiniteGroupOracle.model G) (readouts P) store
        (Circuit.measurementBasisPath (allowAllocation := true) (gates := AlgorithmGate.model)
          (oracles := OrderOracle.model P) (operations := BitWord.model)
          (classicalOracles := ClassicalFiniteGroupOracle.model G)
          (readouts P) basis)).read
          (.storage (cell P index).toCStorageRef)).toFin.val) = 1) = _
  rw [measured_cell, OrderBornBridge.readout_apply]
  let sourceIndex : Fin
      (OrderPreparation.width P + OrderPreparation.width P + 1) :=
    ⟨index.val, by
      have bound := index.isLt
      unfold sampleWidth at bound
      omega⟩
  change decide ((basis (wireEquiv P sourceIndex)).val = 1) =
    decide ((basisEquiv P basis (Fin.castAdd 1 index)).val = 1)
  have sameIndex : sourceIndex = Fin.castAdd 1 index := Fin.ext rfl
  have sameValue := (basisEquiv_wire_value P basis sourceIndex).trans
    (congrArg (fun selected => (basisEquiv P basis selected).val) sameIndex)
  exact congrArg (fun value : Nat => decide (value = 1)) sameValue

/-- Equal-wire placement preserves each source-circuit matrix entry. -/
public lemma nativeProgram_matrix_entry (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (row column : (post P).register.Index) :
    ((nativeProgram P expansion).matrix (OrderOracle.interpretation P)) row column =
      ((OrderCircuit.circuit P expansion).matrix (OrderOracle.interpretation P))
        (basisEquiv P row) (basisEquiv P column) := by
  unfold nativeProgram basisEquiv
  rw [Execution.unitaryOfEqualWires_matrix]
  rfl

/-- The actual runtime zero column is the normalized Born vector of the same
source circuit. -/
public lemma nativeProgram_zero_amplitude (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (row : (post P).register.Index) :
    ((nativeProgram P expansion).matrix
      (OrderOracle.interpretation P)) row (post P).quantumLayout.zeroLabel =
      OrderBornBridge.evolvedState P expansion (basisEquiv P row) := by
  rw [nativeProgram_matrix_entry, basisEquiv_zero]
  unfold OrderBornBridge.evolvedState UnitaryCircuit.applyNormalized
  rw [UnitaryOperator.apply_coe]
  exact (HilbertOperator.applyVec_ket
    (((OrderCircuit.circuit P expansion).matrix (OrderOracle.interpretation P)) :
      HilbertOperator (OrderOracle.layout P).register)
    (OrderOracle.layout P).zeroLabel (basisEquiv P row)).symm

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution

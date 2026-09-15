/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual qubit measurements into separate finite result cells

Each existing dimension-two wire writes its own finite classical cell.
The structural vector reads precisely those cells; it allocates no packed
word or computed value. A later classical branch may inspect these finite
values directly. Distinct result keys ensure that the complete sequence
retains every measured bit, including when a physical wire is measured
more than once [dW19, qcnotes.tex:5409,5420].
-/

namespace QuantumAlg.Execution.QubitReadouts

noncomputable section

variable {ctx : RuntimeCtx .quantum} {width : Nat}

private def outputAt (dimension : ℕ+) (equal : dimension = 2)
    (cell : CWriteRef ctx (.finite 2)) : CWriteRef ctx (.finite dimension) :=
  equal.symm ▸ cell

private theorem outputAt_key (dimension : ℕ+) (equal : dimension = 2)
    (cell : CWriteRef ctx (.finite 2)) : (outputAt dimension equal cell).key = cell.key := by
  cases equal
  rfl

private theorem outputAt_read (dimension : ℕ+) (equal : dimension = 2)
    (cell : CWriteRef ctx (.finite 2)) (store : Store ctx) :
    (store.read (.storage (outputAt dimension equal cell).toCStorageRef)).toFin.val =
      (store.read (.storage cell.toCStorageRef)).toFin.val := by
  cases equal
  rfl

/-- One existing qubit writes the supplied actual finite cell. -/
def readout (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (cell : CWriteRef ctx (.finite 2)) : ZReadout ctx :=
  ⟨wire, outputAt _ qubit cell⟩

/-- The indexed order determines the actual sequential measurement order. -/
def readouts (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) : List (ZReadout ctx) :=
  List.ofFn fun index => readout (wires index) (qubits index) (cells index)

/-- The closed structural vector reads the existing finite result cells without packing. -/
def input (cells : Fin width → CWriteRef ctx (.finite 2)) :
    CInputRef ctx (.fixedVector width (.finite 2)) :=
  .fixedVector fun index => .storage (cells index).toCStorageRef

/-- A branch indexes its concrete gate family by each actual stored finite value. -/
def mask (value : CShape.Value (.fixedVector width (.finite 2))) (index : Fin width) : Bool :=
  decide ((value.get index).toFin.val = 1)

theorem readout_key (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (cell : CWriteRef ctx (.finite 2)) : (readout wire qubit cell).output.key = cell.key :=
  outputAt_key _ qubit cell

/-- Distinct real cells give the exact no-overwrite condition used by sequential Z writes. -/
theorem readouts_distinct (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key) :
    ((readouts wires qubits cells).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply distinct
  exact (readout_key (wires left) (qubits left) (cells left)).symm.trans
    (same.trans (readout_key (wires right) (qubits right) (cells right)))

/-- Each stored result is exactly the value of its named physical measured wire. -/
theorem written_value (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    (store : Store ctx) (basis : ctx.register.Index) (index : Fin width) :
    ((Circuit.writeMeasurementPath (readouts wires qubits cells) store
      (Circuit.measurementBasisPath (readouts wires qubits cells) basis)).read
        (.storage (cells index).toCStorageRef)).toFin.val = (basis (wires index)).val := by
  have stored := Circuit.writeMeasurementBasis_read (readouts wires qubits cells)
    (readouts_distinct wires qubits cells distinct)
    (readout (wires index) (qubits index) (cells index)) (List.mem_ofFn.mpr ⟨index, rfl⟩)
    store basis
  have values := congrArg (fun value => value.toFin.val) stored
  exact (outputAt_read _ (qubits index) (cells index) _).symm.trans values

/-- Direct branch selection reads the actual result, including the finite zero case. -/
theorem written_mask (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    (store : Store ctx) (basis : ctx.register.Index) (index : Fin width) :
    mask ((Circuit.writeMeasurementPath (readouts wires qubits cells) store
      (Circuit.measurementBasisPath (readouts wires qubits cells) basis)).read
        (input cells)) index = decide ((basis (wires index)).val = 1) := by
  exact congrArg (fun value : Nat => decide (value = 1))
    (written_value wires qubits cells distinct store basis index)

/-- The actual measurement pool counts each requested Z operation once. -/
theorem measurement_resources (wires : Fin width → Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (path : (Circuit.measurementSequence (readouts wires qubits cells)).Path) :
    (Circuit.measurementSequence (readouts wires qubits cells)).resourcePool path =
      width • ResourcePool.singleton (Circuit.zEvent 2) := by
  have measured := Circuit.measurementSequence_qubit_resourcePool (readouts wires qubits cells)
    (by
      intro item present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact qubits index) path
  simpa only [readouts, List.length_ofFn] using measured

end

end QuantumAlg.Execution.QubitReadouts

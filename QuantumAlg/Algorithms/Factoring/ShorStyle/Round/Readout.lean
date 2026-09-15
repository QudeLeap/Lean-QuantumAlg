/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual stored phase bits are the original Shor readout

The complete physical wire correspondence preserves the phase values. Each
actual Z write goes to its distinct retained cell, and the charged packing
opcode reads those same values in the original source's big-endian order.
The internal key distinctness is discharged by actual result allocation;
it does not constrain the quantum input or replace a measurement outcome.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
  (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))

/-- Dimension equality transport preserves the actual destination storage key. -/
theorem readout_key (index : Fin (phaseBits N)) :
    (readout N sameWires cells index).output.key = (cells index).key :=
  FiniteReadout.transported_key (phaseWire_dimension N sameWires index) (cells index)

/-- Dimension equality transport reads the actual value from the same finite cell. -/
theorem readout_read_value (index : Fin (phaseBits N)) (store : Store ctx) :
    (store.read (.storage (readout N sameWires cells index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value (phaseWire_dimension N sameWires index) (cells index) store

/-- Distinct retained phase cells give distinct actual Z-write keys. -/
theorem readouts_keys_nodup (distinct : Function.Injective (fun index => (cells index).key)) :
    ((readouts N sameWires cells).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right equal
  apply distinct
  exact (readout_key N sameWires cells left).symm.trans
    (equal.trans (readout_key N sameWires cells right))

/-- Reading the actual written cell obtains the measured finite value of its actual phase wire. -/
theorem measuredCell_value (distinct : Function.Injective (fun index => (cells index).key))
    (store : Store ctx) (basis : ctx.register.Index) (index : Fin (phaseBits N)) :
    ((Circuit.writeMeasurementPath (readouts N sameWires cells) store
      (Circuit.measurementBasisPath (readouts N sameWires cells) basis)).read
        (.storage (cells index).toCStorageRef)).toFin.val =
      (basis (phaseWire N sameWires index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts N sameWires cells)
    (readouts_keys_nodup N sameWires cells distinct)
    (readout N sameWires cells index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [readout_read_value] at numeric
  exact numeric

/-- The full physical/source coordinate correspondence keeps each wire's finite value. -/
theorem wire_value (basis : ctx.register.Index) (index : Fin (NativeQuantum.totalQubits N)) :
    (basis (NativePlacement.wireEquiv N sameWires index)).val =
      ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm
        (NativePlacement.basisEquiv N sameWires basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (NativeQuantum.runtimeLayout N)
    ctx.quantumLayout (NativePlacement.layoutWires N sameWires)
  have value := Execution.basisOfEqualWires_value (NativeQuantum.runtimeLayout N)
    ctx.quantumLayout (NativePlacement.layoutWires N sameWires) (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (NativePlacement.wireEquiv N sameWires index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply
    (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun sourceBasis : (NativeQuantum.runtimeLayout N).Basis => (sourceBasis index).val)
    inverse).symm

/-- A real binary Z outcome becomes precisely the source phase-readout bit. -/
theorem measuredWire_bit (basis : ctx.register.Index) (index : Fin (phaseBits N)) :
    decide ((basis (phaseWire N sameWires index)).val = 1) =
      (OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
        (NativePlacement.basisEquiv N sameWires basis) index := by
  let source :=
    (OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).logical_idx index
  let binary := NativePlacement.basisEquiv N sameWires basis
  have finiteValue := wire_value N sameWires basis source
  have bit :=
    (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv_bit
      ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm
        binary)
      source
  have inverse := congrArg
    (fun value : Fin (2 ^ (phaseBits N + (modulusBits N + modulusBits N))) =>
      value.val.testBit source.rev.val)
    (Equiv.apply_symm_apply
      (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv binary)
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv
        ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm
          binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm.trans inverse
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (NativeQuantum.totalQubits N - 1 - source.val)
      congr 1
      simp only [Fin.rev, NativeQuantum.totalQubits]
      omega

/-- The real packing operation computes the original source outcome from its actual Z writes. -/
theorem packing_measured_value (distinct : Function.Injective (fun index => (cells index).key))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    (store : Store ctx) (basis : ctx.register.Index) :
    (packing N cells result).eval
      ((Circuit.writeMeasurementPath (readouts N sameWires cells) store
        (Circuit.measurementBasisPath (readouts N sameWires cells) basis)).read
          (packing N cells result).inputRef) =
      CShape.Value.bits
        ((OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          (NativePlacement.basisEquiv N sameWires basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts N sameWires cells) store
      (Circuit.measurementBasisPath (readouts N sameWires cells) basis)).read
        (.storage (cells index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [measuredCell_value N sameWires cells distinct]
  exact measuredWire_bit N sameWires basis index

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

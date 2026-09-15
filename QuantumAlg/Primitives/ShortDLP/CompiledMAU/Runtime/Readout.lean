/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual short-DLP measured cells and the original source readout

The placed wires, typed finite writes and charged packing opcode preserve the
original source's big-endian two-exponent readout. Distinctness below is the
internal wiring fact supplied by the actual measurement-cell allocation. It
is independent of all stored values and imposes no quantum-state assumption.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))

/-- Dimension transport keeps the identity of the actual finite output cell. -/
theorem shortDLP_runtimeReadout_key (index : Fin (resultBits m ell width)) :
    (readout m ell width sameWires cells index).output.key = (cells index).key :=
  FiniteReadout.transported_key
    (shortDLP_runtimeMeasuredWire_dimension m ell width sameWires index) (cells index)

/-- Dimension transport reads precisely the value stored in the original finite cell. -/
theorem shortDLP_runtimeReadout_read_value (index : Fin (resultBits m ell width))
    (store : Store ctx) :
    (store.read (.storage
      (readout m ell width sameWires cells index).output.toCStorageRef)).toFin.val =
      (store.read (.storage (cells index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value
    (shortDLP_runtimeMeasuredWire_dimension m ell width sameWires index) (cells index) store

/-- Actual pairwise distinct measurement cells give distinct ordered write keys. -/
theorem shortDLP_runtimeReadouts_keys_nodup
    (distinct : Function.Injective (fun index => (cells index).key)) :
    ((readouts m ell width sameWires cells).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right equal
  apply distinct
  exact (shortDLP_runtimeReadout_key m ell width sameWires cells left).symm.trans
    (equal.trans (shortDLP_runtimeReadout_key m ell width sameWires cells right))

/-- Reading the actual measured cell obtains the value of its actual source wire. -/
theorem shortDLP_runtimeMeasuredCell_value
    (distinct : Function.Injective (fun index => (cells index).key))
    (store : Store ctx) (basis : ctx.register.Index) (index : Fin (resultBits m ell width)) :
    ((Circuit.writeMeasurementPath (readouts m ell width sameWires cells) store
      (Circuit.measurementBasisPath (readouts m ell width sameWires cells) basis)).read
        (.storage (cells index).toCStorageRef)).toFin.val =
      (basis (measuredWire m ell width sameWires index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (readouts m ell width sameWires cells)
    (shortDLP_runtimeReadouts_keys_nodup m ell width sameWires cells distinct)
    (readout m ell width sameWires cells index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [shortDLP_runtimeReadout_read_value] at numeric
  exact numeric

/-- The exact runtime/source correspondence preserves every finite wire value. -/
theorem shortDLP_runtimeWire_value (basis : ctx.register.Index)
    (index : Fin (totalQubits (registerParameters m ell width))) :
    (basis (RuntimePlacement.wireEquiv m ell width sameWires index)).val =
      ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm
        (RuntimePlacement.basisEquiv m ell width sameWires basis) index).val := by
  let correspondence := Execution.basisOfEqualWires (runtimeLayout m ell width)
    ctx.quantumLayout (RuntimePlacement.layoutWires m ell width sameWires)
  have value := Execution.basisOfEqualWires_value (runtimeLayout m ell width)
    ctx.quantumLayout (RuntimePlacement.layoutWires m ell width sameWires)
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (RuntimePlacement.wireEquiv m ell width sameWires index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply
    (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv (correspondence.symm basis)
  exact value.trans (congrArg
    (fun sourceBasis : (ShortDLP.layout (registerParameters m ell width)).toQuantumLayout.Basis =>
      (sourceBasis index).val) inverse).symm

/-- Boolean conversion of a real measured wire is exactly the original source readout bit. -/
theorem shortDLP_runtimeMeasuredWire_bit (basis : ctx.register.Index)
    (index : Fin (resultBits m ell width)) :
    decide ((basis (measuredWire m ell width sameWires index)).val = 1) =
      (ShortDLP.measurement (registerParameters m ell width)).readout
        (RuntimePlacement.basisEquiv m ell width sameWires basis) index := by
  let source := (ShortDLP.measurement (registerParameters m ell width)).logical_idx index
  let binary := RuntimePlacement.basisEquiv m ell width sameWires basis
  have finiteValue := shortDLP_runtimeWire_value m ell width sameWires basis source
  have bit := (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv_bit
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm binary) source
  rw [Equiv.apply_symm_apply] at bit
  have converted (value : Fin 2) : decide (value.val = 1) = finTwoEquiv value := by
    fin_cases value <;> rfl
  calc
    _ = finTwoEquiv
        ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm binary source) :=
      (congrArg (fun value => decide (value = 1)) finiteValue).trans (converted _)
    _ = binary.val.testBit source.rev.val := bit.symm
    _ = _ := by
      change binary.val.testBit source.rev.val =
        binary.val.testBit (totalQubits (registerParameters m ell width) - 1 - source.val)
      congr 1
      simp only [Fin.rev]
      omega

/-- The real pack operation computes exactly the original source outcome from its actual writes. -/
theorem shortDLP_runtimePacking_measured_value
    (distinct : Function.Injective (fun index => (cells index).key))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (store : Store ctx) (basis : ctx.register.Index) :
    (packing m ell width cells result).eval
      ((Circuit.writeMeasurementPath (readouts m ell width sameWires cells) store
        (Circuit.measurementBasisPath (readouts m ell width sameWires cells) basis)).read
          (packing m ell width cells result).inputRef) =
      CShape.Value.bits ((ShortDLP.measurement (registerParameters m ell width)).readout
        (RuntimePlacement.basisEquiv m ell width sameWires basis)) := by
  change CShape.Value.bits (fun index => decide
    (((Circuit.writeMeasurementPath (readouts m ell width sameWires cells) store
      (Circuit.measurementBasisPath (readouts m ell width sameWires cells) basis)).read
        (.storage (cells index).toCStorageRef)).toFin.val = 1)) = _
  apply congrArg CShape.Value.bits
  funext index
  rw [shortDLP_runtimeMeasuredCell_value m ell width sameWires cells distinct]
  exact shortDLP_runtimeMeasuredWire_bit m ell width sameWires basis index

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

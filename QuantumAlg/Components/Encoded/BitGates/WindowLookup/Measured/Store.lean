/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Semantics
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Algorithm.ClassicalOp.Finite.Bits

/-!
# Actual measured finite cells and paid packed-mask readback

Distinct destination keys retain every named measurement outcome. The only
cast changes the certified finite shape of the same existing cell. Packing
those actual readings recovers each measured physical bit, independently of
the incoming Store and without adding quantum systems.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- Casting the finite dimension changes no actual storage identity. -/
lemma finiteOutput_key {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) : (finiteOutput qubit output).key = output.key := by
  cases qubit
  rfl

private lemma finiteOutput_read {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) (store : Store ctx) (value : Fin dimension)
    (observed : store.read (.storage (finiteOutput qubit output).toCStorageRef) = .finite value) :
    (store.read (.storage output.toCStorageRef)).toFin.val = value.val := by
  cases qubit
  exact congrArg (fun reading => reading.toFin.val) observed

/-- Distinct supplied finite cells remain distinct after the physical dimension casts. -/
lemma resultReadouts_output_nodup (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective (fun index => (output index).key)) :
    ((resultReadouts physical sameWires target output).map
      (fun item => item.output.key)).Nodup := by
  simp only [resultReadouts, List.map_ofFn, Function.comp_def, resultReadout]
  apply List.nodup_ofFn_ofInjective
  intro first second same
  apply distinct
  exact (finiteOutput_key _ (output first)).symm.trans
    (same.trans (finiteOutput_key _ (output second)))

/-- Reading a real measured cell obtains its named physical wire's exact finite outcome. -/
lemma resultReadout_read_basis (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective (fun index => (output index).key))
    (store : Store ctx) (basis : ctx.register.Index) (index : Fin width) :
    ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output) store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output) basis)).read
          (.storage (output index).toCStorageRef)).toFin.val =
      (basis (resultWire physical sameWires (target.bit index))).val := by
  exact finiteOutput_read (resultWire_qubit physical sameWires (target.bit index)) (output index)
    _ _ (Circuit.writeMeasurementBasis_read _
      (resultReadouts_output_nodup physical sameWires target output distinct)
      (resultReadout physical sameWires (target.bit index) (output index))
      (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis)

/-- Each paid packed-mask bit is exactly its actual corresponding physical measurement value. -/
lemma measuredWordFinalStore_bit_basis (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective (fun index => (output index).key))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (basis : ctx.register.Index)
    (index : Fin width) :
    (((measuredWordFinalStore (oracles := oracles) (services := services)
      physical sameWires target output mask store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output) basis)).read
          (.storage mask.toCStorageRef)).bitGet index).toBool.toNat =
      (basis (resultWire physical sameWires (target.bit index))).val := by
  let measured := Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires target output) store
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output) basis)
  have packed : (measured.applyOp (resultPackOp output mask)).read
      (.storage mask.toCStorageRef) =
      (resultPackOp output mask).eval (measured.read (resultInput output)) :=
    Store.read_applyOp_output measured (resultPackOp output mask)
  change (((measured.applyOp (resultPackOp output mask)).read
    (.storage mask.toCStorageRef)).bitGet index).toBool.toNat = _
  rw [packed]
  exact (ClassicalOp.eval_packFiniteBits_recovers width ctx (resultInput output) mask
    (measured.read (resultInput output)) index).trans
      (resultReadout_read_basis physical sameWires target output distinct store basis index)

end

end QuantumAlg.EncodedBit.WindowLookup

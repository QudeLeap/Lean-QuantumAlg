/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Correction
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Measurement.Sequence

/-!
# Actual X-basis measurement and reset of the original result word

One physical parallel H layer precedes all actual Z measurements into their
supplied finite outcome cells. A paid native pack instruction copies those
real readings into the supplied mask cell. Its actual stored-bit branch then
selects the parallel X corrections on those same measured physical systems.
No quantum system or classical cell is allocated by this child circuit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The corresponding actual result-wire position in the full live runtime context. -/
def resultWire (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit encoding) : Fin ctx.systemCount :=
  positionsOfEqualWires physical.toQuantum ctx.quantumLayout sameWires target.wire

/-- The same ordered physical wire record retains its original qubit dimension. -/
lemma resultWire_qubit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit encoding) :
    (ctx.quantumLayout.wire (resultWire physical sameWires target)).dimension = 2 :=
  congrArg QuantumWire.dimension
    (wireAtCorrespondingPosition physical.toQuantum ctx.quantumLayout sameWires target.wire)

/-- Cast only the certified finite shape of one existing classical measurement cell. -/
def finiteOutput {dimension : ℕ+} (qubit : dimension = 2)
    (output : CWriteRef ctx (.finite 2)) : CWriteRef ctx (.finite dimension) :=
  Eq.mpr (congrArg (fun size : ℕ+ => CWriteRef ctx (.finite size)) qubit) output

/-- The original finite outcome cells, in the original physical result-word order. -/
def resultInput (output : Fin width → CWriteRef ctx (.finite 2)) :
    CInputRef ctx (.fixedVector width (.finite 2)) :=
  .fixedVector fun index => .storage (output index).toCStorageRef

/-- One actual result wire writes its measured finite value into its supplied existing cell. -/
def resultReadout (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : EncodedBit encoding) (output : CWriteRef ctx (.finite 2)) : ZReadout ctx where
  wire := resultWire physical sameWires target
  output := finiteOutput (resultWire_qubit physical sameWires target) output

/-- The actual sequence names every original result wire and its real writable outcome cell. -/
def resultReadouts (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2)) :
    List (ZReadout ctx) :=
  List.ofFn fun index => resultReadout physical sameWires (target.bit index) (output index)

/-- The actual nominal instruction materializes the measured finite readings as mask bits. -/
def resultPackOp (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width)) :
    ClassicalOp (.fixedVector width (.finite 2)) (.bits width) ctx ctx :=
  .packFiniteBits width ctx (resultInput output) mask

/-- Interpret only the actual stored mask bits, in result-word least-significant-first order. -/
def resultConstant : CShape.Value (.bits width) → Fin (2 ^ width)
  | .bits bits => ⟨Nat.ofBits bits, Nat.ofBits_lt_two_pow _⟩

/-- Each selected reset X is controlled by exactly its corresponding actual stored mask bit. -/
lemma resultConstant_testBit (value : CShape.Value (.bits width)) (index : Fin width) :
    (resultConstant value).val.testBit index.val = (value.bitGet index).toBool := by
  cases value with
  | bits bits => exact Nat.testBit_ofBits_lt _ index.val index.isLt

/-- Actual H, MZ, paid packing and stored-outcome parallel X on existing result systems. -/
def measuredResetWordCircuit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width)) :
    Circuit (.quantum AlgorithmGate.model oracles BitWord.model services) ctx ctx false :=
  (Circuit.unitary (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (wordHadamardProgram physical oracles target distinct))).seq
    ((Circuit.measurementSequence (resultReadouts physical sameWires target output)).seq
      ((MaskParity.instruction (resultPackOp output mask)).seq
        (.branch (.storage mask.toCStorageRef) fun value => .unitary
          (unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
            (wordXProgram physical oracles target distinct (resultConstant value))))))

end

end QuantumAlg.EncodedBit.WindowLookup

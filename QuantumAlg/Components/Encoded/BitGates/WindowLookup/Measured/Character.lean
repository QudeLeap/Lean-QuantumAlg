/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Character
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# Common branch coefficient from the actual measured mask

The original packed mask is read from the real measurement/reset Store.
Its bit values give precisely the actual physical Hadamard row. On a named
input table word, the exact retained coefficient is the positive common
amplitude times the same parity character computed by paid feedback rows.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution NormalizedVector

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The original encoded bit is exactly the original physical basis value's Boolean reading. -/
lemma encodedPhysicalBit_decide (physical : QubitLayout encoding.width)
    (bit : EncodedBit encoding) (state : Data) :
    decide ((physical.basisEquiv.symm (encoding.encode state) bit.wire).val = 1) =
      bit.get state := by
  rw [encodedPhysicalBit]
  cases bit.get state <;> rfl

/-- Read the actual paid packed mask of the original ordered measurement fiber. -/
def measuredMask (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (state : Data) :
    CShape.Value (.bits width) :=
  (measuredWordFinalStore (oracles := oracles) (services := services)
    physical sameWires target output mask store
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)
      (measuredEncodedBasis physical sameWires state))).read (.storage mask.toCStorageRef)

/-- Every bit of the real packed mask is the same original measured result value. -/
lemma measuredMask_bit (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (state : Data) (index : Fin width) :
    ((measuredMask (oracles := oracles) (services := services)
      physical sameWires target output mask store state).bitGet index).toBool =
        (target.bit index).get state :=
  measuredWordFinalStore_bit_encoded physical sameWires target output outputDistinct
    mask store state index

/-- The actual retained H coefficient is its common amplitude times the real measured character. -/
lemma wordHadamardAmplitude_measuredMask (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (input result : Data)
    (constant : Fin (2 ^ width))
    (inputWord : ∀ index, (target.bit index).get input = constant.val.testBit index.val) :
    wordHadamardAmplitude physical target
      (physical.basisEquiv.symm (encoding.encode result))
      (physical.basisEquiv.symm (encoding.encode input)) = invSqrt2 ^ width *
        (if MaskParity.maskValue
          (measuredMask (oracles := oracles) (services := services)
            physical sameWires target output mask store result) constant then (-1 : ℂ) else 1) := by
  have rowBits (index : Fin width) := (measuredMask_bit (oracles := oracles) (services := services)
    physical sameWires target output outputDistinct mask store result index).trans
      (encodedPhysicalBit_decide physical (target.bit index) result).symm
  have columnBits (index : Fin width) := (inputWord index).symm.trans
    (encodedPhysicalBit_decide physical (target.bit index) input).symm
  rw [wordHadamardAmplitude_character,
    wordHadamardCharacter_mask physical target _ _ _ constant rowBits columnBits]

end

end QuantumAlg.EncodedBit.WindowLookup

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Store
import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Coordinates
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# The stored physical correction clears every actual measured result bit

The reset uses the paid packed readings of the same physical measurement
path. Its exact native action clears every measured bit and retains all
other wires. The supplied result systems can subsequently serve as clean
unary workspace; no additional quantum system is introduced here.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The encoded full physical basis label expressed on the same complete live wire record. -/
def measuredEncodedBasis (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (state : Data) : ctx.register.Index :=
  basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (physical.basisEquiv.symm (encoding.encode state))

/-- Actual paid mask readback agrees with each measured encoded physical bit. -/
lemma measuredWordFinalStore_bit_encoded (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective (fun index => (output index).key))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (state : Data) (index : Fin width) :
    (((measuredWordFinalStore (oracles := oracles) (services := services)
      physical sameWires target output mask store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires state))).read
          (.storage mask.toCStorageRef)).bitGet index).toBool = (target.bit index).get state := by
  have reading := measuredWordFinalStore_bit_basis (oracles := oracles) (services := services)
    physical sameWires target output distinct mask store
    (measuredEncodedBasis physical sameWires state) index
  have wireRead := basisOfEqualWires_value physical.toQuantum ctx.quantumLayout sameWires
    (physical.basisEquiv.symm (encoding.encode state)) (target.bit index).wire
  have bitRead := congrArg Fin.val ((target.bit index).targetBasisEquiv_first state)
  change ((physical.basisEquiv.symm (encoding.encode state)) (target.bit index).wire).val =
    (finTwoEquiv.symm ((target.bit index).get state)).val at bitRead
  change _ = (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (physical.basisEquiv.symm (encoding.encode state))
    (positionsOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (target.bit index).wire)).val at reading
  rw [wireRead, bitRead] at reading
  cases observed : (((measuredWordFinalStore (oracles := oracles) (services := services)
    physical sameWires target output mask store
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)
      (measuredEncodedBasis physical sameWires state))).read
        (.storage mask.toCStorageRef)).bitGet index).toBool <;>
    cases value : (target.bit index).get state <;>
      simp_all [finTwoEquiv]

/-- The actual stored-outcome X program's semantic action on its measured basis fiber. -/
def measuredWordResetStep (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (state : Data) : Data :=
  Word.xorConstantStep target (resultConstant
    ((measuredWordFinalStore (oracles := oracles) (services := services)
      physical sameWires target output mask store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires state))).read (.storage mask.toCStorageRef))) state

/-- Every original measured result system is physically zero after its actual stored correction. -/
lemma measuredWordResetStep_zero (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (targetDistinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective (fun index => (output index).key))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx) (state : Data) (index : Fin width) :
    (target.bit index).get (measuredWordResetStep (oracles := oracles) (services := services)
      physical sameWires target output mask store state) = false := by
  unfold measuredWordResetStep
  rw [Word.xorConstantStep_get_target _ _ _
    (fun other different same => different (targetDistinct same)), resultConstant_testBit,
    measuredWordFinalStore_bit_encoded physical sameWires target output outputDistinct,
    Bool.xor_self]

/-- The actual equal-wire native X operator has exactly the stated cleared physical basis image. -/
lemma measuredWordCorrection_applyVec (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx) (state : Data) (environment : oracles.Interpretation) :
    ((measuredWordCorrection (services := services) physical sameWires target distinct output mask
      store (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires state))).matrix environment).applyVec
      (NormalizedVector.ket (R := ctx.register)
        (measuredEncodedBasis physical sameWires state)).vec =
      (NormalizedVector.ket (R := ctx.register) (measuredEncodedBasis physical sameWires
        (measuredWordResetStep (oracles := oracles) (services := services)
          physical sameWires target output mask store state))).vec := by
  unfold measuredWordCorrection
  rw [unitaryOfEqualWires_matrix]
  let constant := resultConstant
    ((measuredWordFinalStore (oracles := oracles) (services := services)
      physical sameWires target output mask store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires state))).read (.storage mask.toCStorageRef))
  have vector := congrArg NormalizedVector.vec
    ((wordXProgram_realizes physical oracles target distinct constant environment).apply_encoded_ket
      state)
  change UnitaryOperator.applyVec _
    (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode state))).vec = _ at vector
  have transported := congrArg
    (HilbertVector.reindex (R := physical.toQuantum.register) (S := ctx.register)
      (basisOfEqualWires physical.toQuantum ctx.quantumLayout sameWires)) vector
  rw [← UnitaryOperator.reindex_applyVec, HilbertVector.reindex_ket,
    HilbertVector.reindex_ket] at transported
  exact transported

end

end QuantumAlg.EncodedBit.WindowLookup

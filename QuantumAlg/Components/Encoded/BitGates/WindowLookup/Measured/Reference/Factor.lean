/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Matrix
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Untouched-reference factors of actual measured word branches

The actual H layer, same-wire joint MZ projector and stored-mask correction
have one local Kraus matrix beside identity on the arbitrary reference.
The width and original measurement path remain symbolic. This identity
requires no arithmetic admission, clean word or good-prefix hypothesis.
-/

namespace QuantumAlg

noncomputable section

open scoped Kronecker
open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

namespace Circuit

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- The local matrix of the actual joint readout on its same original physical systems. -/
def measurementLocalProjector (readouts : List (ZReadout ctx))
    (path : (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (allowAllocation := allowAllocation) readouts).Path) : HilbertOperator ctx.register :=
  ZMeasurement.projector
    (fun basis : ctx.register.Index =>
      measurementBasisPath (gates := gates) (oracles := oracles) (operations := operations)
        (classicalOracles := services) (allowAllocation := allowAllocation) readouts basis) path

/-- The complete actual measurement projector is local beside the same reference identity. -/
lemma measurementPathProjector_tensor_reference (readouts : List (ZReadout ctx))
    (Reference : Register)
    (path : (measurementSequence (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (allowAllocation := allowAllocation) readouts).Path) :
    measurementPathProjector readouts Reference path =
      measurementLocalProjector readouts path ⊗ₖ (1 : HilbertOperator Reference) := by
  ext row column
  simp only [measurementPathProjector, measurementLocalProjector, ZMeasurement.projector,
    Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases physical : row.1 = column.1
  · by_cases reference : row.2 = column.2
    · have same : row = column := Prod.ext physical reference
      simp only [if_pos same, if_pos physical, if_pos reference, mul_one]
    · have different : row ≠ column := fun same => reference (congrArg Prod.snd same)
      simp only [if_neg different, if_pos physical, if_neg reference, mul_zero]
  · have different : row ≠ column := fun same => physical (congrArg Prod.fst same)
    simp only [if_neg different, if_neg physical, zero_mul]

end Circuit

namespace EncodedBit.WindowLookup

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The original actual correction, MZ projector and H matrices, without a reference factor. -/
def measuredWordLocalKraus (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path)
    (environment : oracles.Interpretation) : HilbertOperator ctx.register :=
  ((measuredWordCorrection (services := services) physical sameWires target distinct
    output mask store path).matrix environment : HilbertOperator ctx.register) *
    Circuit.measurementLocalProjector (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (services := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output) path *
    ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
      (wordHadamardProgram physical oracles target distinct)).matrix environment :
        HilbertOperator ctx.register)

/-- All actual measured-word Kraus branches preserve the full arbitrary reference factor. -/
lemma measuredWordKraus_tensor_reference (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path)
    (environment : oracles.Interpretation) (Reference : Register) :
    measuredWordKraus physical sameWires target distinct output mask store path
        environment Reference =
      measuredWordLocalKraus physical sameWires target distinct output mask store path environment
        ⊗ₖ (1 : HilbertOperator Reference) := by
  unfold measuredWordKraus measuredWordLocalKraus
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    Circuit.measurementPathProjector_tensor_reference,
    HilbertOperator.kronecker_identity_mul, HilbertOperator.kronecker_identity_mul]

end EncodedBit.WindowLookup

end

end QuantumAlg

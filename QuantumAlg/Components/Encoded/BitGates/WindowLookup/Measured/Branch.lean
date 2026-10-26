/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Transport
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard.Projection
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reference
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Matrix

/-!
# Exact actual word-reset branch on complete coherent basis columns

The operator is the same actual parallel H, ordered joint projector and
stored-mask physical X correction used by execution. A named result column
retains every original complement value and its arbitrary external reference.
Its coefficient is exactly the product of the original native H entries;
normalization and character cancellation are separate consequences.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

private lemma projector_prodTensor {Local Reference : Register} {Outcome : Type}
    [decision : DecidableEq Outcome] (readout : Local.Index → Outcome) (outcome : Outcome)
    (localVector : HilbertVector Local) (referenceVector : HilbertVector Reference) :
    (ZMeasurement.projector
      (fun basis : (Register.prod Local Reference).Index => readout basis.1) outcome).applyVec
        (HilbertVector.prodTensor localVector referenceVector) =
      HilbertVector.prodTensor ((ZMeasurement.projector readout outcome).applyVec localVector)
        referenceVector := by
  ext row
  rw [projector_applyVec_any, HilbertVector.prodTensor_apply,
    HilbertVector.prodTensor_apply, projector_applyVec_any]
  split_ifs <;> simp

private lemma product_smul {Local Reference : Register} (scalar : ℂ)
    (first : HilbertVector Local) (second : HilbertVector Reference) :
    HilbertVector.prodTensor (scalar • first) second =
      scalar • HilbertVector.prodTensor first second := by
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

/-- The actual joint path projector after native parallel H retains the exact complete column. -/
lemma measuredHadamard_projector_reference_ket (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (environment : oracles.Interpretation)
    (input result : Data)
    (complement : physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct))
          (physical.basisEquiv.symm (encoding.encode result)) =
      physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct))
          (physical.basisEquiv.symm (encoding.encode input)))
    {Reference : Register} (reference : Reference.Index) :
    (Circuit.measurementPathProjector (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (services := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output) Reference
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires result))).applyVec
      ((UnitaryOperator.prodTensor
        ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
          (wordHadamardProgram physical oracles target distinct)).matrix environment)
        (1 : UnitaryOperator Reference)).applyVec
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires input, reference)).vec) =
      wordHadamardAmplitude physical target
        (physical.basisEquiv.symm (encoding.encode result))
        (physical.basisEquiv.symm (encoding.encode input)) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires result, reference)).vec := by
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    UnitaryOperator.one_applyVec, Circuit.measurementPathProjector, projector_prodTensor]
  have actual := resultHadamard_projected_ket (services := services) physical sameWires target
    distinct output environment (physical.basisEquiv.symm (encoding.encode input))
    (physical.basisEquiv.symm (encoding.encode result)) complement
  change HilbertOperator.applyVec (R := ctx.register) _
    (UnitaryOperator.applyVec _
      (NormalizedVector.ket (R := ctx.register)
        (measuredEncodedBasis physical sameWires input)).vec) =
      wordHadamardAmplitude physical target
        (physical.basisEquiv.symm (encoding.encode result))
        (physical.basisEquiv.symm (encoding.encode input)) •
          (NormalizedVector.ket (R := ctx.register)
            (measuredEncodedBasis physical sameWires result)).vec at actual
  change HilbertVector.prodTensor
    ((resultPathValueProjector (oracles := oracles) (services := services)
      physical sameWires target output (physical.basisEquiv.symm (encoding.encode result))).applyVec
        _) _ = _
  rw [actual, product_smul, HilbertVector.prodTensor_ket]

/-- The same actual H/MZ/X branch has its exact H coefficient and physical zeroed result image. -/
lemma measuredWordKraus_encoded_ket (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (environment : oracles.Interpretation) (store : Store ctx) (input result : Data)
    (complement : physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct))
          (physical.basisEquiv.symm (encoding.encode result)) =
      physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct))
          (physical.basisEquiv.symm (encoding.encode input)))
    {Reference : Register} (reference : Reference.Index) :
    (measuredWordKraus physical sameWires target distinct output mask store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts physical sameWires target output)
        (measuredEncodedBasis physical sameWires result)) environment Reference).applyVec
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires input, reference)).vec =
      wordHadamardAmplitude physical target
        (physical.basisEquiv.symm (encoding.encode result))
        (physical.basisEquiv.symm (encoding.encode input)) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires
              (measuredWordResetStep (oracles := oracles) (services := services)
                physical sameWires target output mask store result), reference)).vec := by
  have projected := measuredHadamard_projector_reference_ket (services := services)
    physical sameWires target distinct output environment input result complement reference
  have corrected := measuredWordCorrection_reference_ket (services := services)
    physical sameWires target distinct output mask store result environment reference
  change HilbertOperator.applyVec (R := Register.prod ctx.register Reference) _
    (HilbertOperator.applyVec (R := Register.prod ctx.register Reference) _ _) = _ at projected
  change HilbertOperator.applyVec (R := Register.prod ctx.register Reference) _ _ = _ at corrected
  rw [measuredWordKraus, HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    projected, HilbertOperator.applyVec_smul]
  exact congrArg (fun vector => wordHadamardAmplitude physical target
    (physical.basisEquiv.symm (encoding.encode result))
    (physical.basisEquiv.symm (encoding.encode input)) • vector) corrected

end

end QuantumAlg.EncodedBit.WindowLookup

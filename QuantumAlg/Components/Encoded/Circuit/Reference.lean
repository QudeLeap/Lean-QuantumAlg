/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.Circuit.Placement
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Placed native basis actions beside arbitrary original references

An exact native basis action is transported through the same ordered
physical wires and tensor identity on an arbitrary reference. The carrier
and placement remain abstract, so clients do not normalize a large basis
merely to preserve original reference correlations.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

open Execution
open scoped BigOperators

variable {gates : GateModel} {oracles : OracleModel}
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    {physical : QubitLayout encoding.width} {count : Nat} (target : QuantumLayout count)
    (sameWires : physical.toQuantum.wires = target.wires)

/-- The same placed native action leaves every original reference basis label unchanged. -/
lemma equalWires_reference_ket_of_eq
    (program : UnitaryCircuit gates oracles physical.toQuantum)
    (environment : oracles.Interpretation) (initial final : Data)
    (actual : program.applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode initial))) =
        NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode final)))
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor
        ((unitaryOfEqualWires physical.toQuantum target sameWires program).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator (target.register.prod Reference))
      (NormalizedVector.ket (R := target.register.prod Reference)
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode initial)), reference)).vec =
      (NormalizedVector.ket (R := target.register.prod Reference)
        (basisOfEqualWires physical.toQuantum target sameWires
          (physical.basisEquiv.symm (encoding.encode final)), reference)).vec := by
  have placed := equalWires_apply_encoded_ket_of_eq target sameWires program environment
    initial final actual
  change (UnitaryOperator.prodTensor
    ((unitaryOfEqualWires physical.toQuantum target sameWires program).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket (R := target.register) (S := Reference)
      (basisOfEqualWires physical.toQuantum target sameWires
        (physical.basisEquiv.symm (encoding.encode initial))) reference,
    UnitaryOperator.prodTensor_applyVec_prodTensor, placed, UnitaryOperator.one_applyVec,
    HilbertVector.prodTensor_ket]

/-- Arbitrary finite coherent sums keep the same amplitudes and original reference labels. -/
lemma equalWires_reference_sum_of_eq
    (program : UnitaryCircuit gates oracles physical.toQuantum)
    (environment : oracles.Interpretation) {Index : Type} [Fintype Index]
    (initial final : Index → Data)
    (actual : ∀ index, program.applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode (initial index)))) =
        NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode (final index))))
    {Reference : Register} (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor
        ((unitaryOfEqualWires physical.toQuantum target sameWires program).matrix environment)
        (1 : UnitaryOperator Reference) : HilbertOperator (target.register.prod Reference))
      (∑ index, amplitude index •
        (NormalizedVector.ket (R := target.register.prod Reference)
          (basisOfEqualWires physical.toQuantum target sameWires
            (physical.basisEquiv.symm (encoding.encode (initial index))), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := target.register.prod Reference)
          (basisOfEqualWires physical.toQuantum target sameWires
            (physical.basisEquiv.symm (encoding.encode (final index))), reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  exact congrArg (fun vector => amplitude index • vector)
    (equalWires_reference_ket_of_eq target sameWires program environment _ _ (actual index)
      (reference index))

end

end QuantumAlg.UnitaryCircuit

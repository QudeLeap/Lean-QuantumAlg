/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Correctness
import all QuantumAlg.Core.Base.Tensor.Certified

/-! # Complete physical arithmetic beside arbitrary original correlations and Reference -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

open scoped BigOperators

private lemma reference_ket_of_actual {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) (initial final : layout.register.Index)
    (actual : body.applyNormalized environment (NormalizedVector.ket initial) =
      NormalizedVector.ket final) {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (layout.register.prod Reference))
        (NormalizedVector.ket (R := layout.register.prod Reference) (initial, reference)).vec =
      (NormalizedVector.ket (R := layout.register.prod Reference) (final, reference)).vec := by
  have pure := congrArg NormalizedVector.vec actual
  change (body.matrix environment).applyVec (NormalizedVector.ket initial).vec =
    (NormalizedVector.ket final).vec at pure
  change (UnitaryOperator.prodTensor (body.matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    pure, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

private lemma reference_sum_of_actual {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation) {Index : Type} [Fintype Index]
    (initial final : Index → layout.register.Index)
    (actual : ∀ index, body.applyNormalized environment (NormalizedVector.ket (initial index)) =
      NormalizedVector.ket (final index)) {Reference : Register}
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference) :
        HilbertOperator (layout.register.prod Reference))
        (∑ index, amplitude index • (NormalizedVector.ket
          (R := layout.register.prod Reference) (initial index, reference index)).vec) =
      ∑ index, amplitude index • (NormalizedVector.ket
        (R := layout.register.prod Reference) (final index, reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  exact congrArg (fun value => amplitude index • value)
    (reference_ket_of_actual body environment _ _ (actual index) (reference index))

def referenceOperator (body : Circuit) (environment : OracleModel.empty.Interpretation)
    (Reference : Register) : HilbertOperator
    ((QubitLayout.canonical Frame.encoding.width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor (body.matrix environment) (1 : UnitaryOperator Reference)

def referenceVector {Reference : Register} {Index : Type} [Fintype Index]
    (states : Index → Frame.Raw) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) : HilbertVector
    ((QubitLayout.canonical Frame.encoding.width).toQuantum.register.prod Reference) :=
  ∑ index, amplitude index • (NormalizedVector.ket
    (R := (QubitLayout.canonical Frame.encoding.width).toQuantum.register.prod Reference)
    ((QubitLayout.canonical _).basisEquiv.symm (Frame.encoding.encode (states index)),
      reference index)).vec

/-- Extend the same actual complete physical circuit, without adding an algorithm wire. -/
lemma coherent_of_basis (body : Circuit) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (initial final : Index → Frame.Raw)
    (actual : ∀ index, body.applyNormalized environment (ket (initial index)) = ket (final index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator body environment Reference)
        (referenceVector initial reference amplitude) = referenceVector final reference amplitude :=
  reference_sum_of_actual body environment _ _ actual reference amplitude

/-- All original word, work, selector, caller and external-Reference correlations are retained. -/
lemma cleanProgram_reference (ports : PortAssignment) (control : Control) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source multiplier : Index → Word)
    (canonical : ∀ index, Canonical (source index)) (retained : Index → Placement.Rest ports)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (cleanProgram ports control choice) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) Horner.zeroWord
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Horner.productWord (source index)
          ((quantumMultiplier ports choice).value (source index) (multiplier index, retained index))
          ((controlBit ports control).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => cleanProgram_canonical ports control choice
    environment (source index) (multiplier index) (canonical index) (retained index))
    reference amplitude

lemma macProgram_reference (ports : PortAssignment) (control : Control)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest ports) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (macProgram ports control) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.accumulatedWord (source index) (multiplier index) (target index)
          ((controlBit ports control).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => macProgram_canonical ports control environment
    (source index) (target index) (multiplier index) (sourceCanonical index) (targetCanonical index)
    (retained index)) reference amplitude

lemma inverseMacProgram_reference (ports : PortAssignment) (control : Control)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest ports) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (inverseMacProgram ports control) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index)
        (Accumulate.Inverse.differenceWord (source index) (multiplier index) (target index)
          ((controlBit ports control).get (retained index)))
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => inverseMacProgram_canonical ports control
    environment (source index) (target index) (multiplier index) (sourceCanonical index)
    (targetCanonical index) (retained index)) reference amplitude

/-- The actual original A copy word is cleared beside arbitrary accumulator and Ref correlations. -/
lemma subtractSquareProgram_reference (control : Control)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target : Index → Word)
    (sourceCanonical : ∀ index, Canonical (source index))
    (targetCanonical : ∀ index, Canonical (target index))
    (retained : Index → Placement.Rest squarePorts) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (referenceOperator (subtractSquareProgram control) environment Reference)
        (referenceVector (fun index => arithmeticState squarePorts (source index) (target index)
          Horner.zeroWord (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState squarePorts (source index)
        (Accumulate.Inverse.differenceWord (source index) (source index) (target index)
          ((controlBit squarePorts control).get (retained index)))
        Horner.zeroWord (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _ (fun index => subtractSquareProgram_canonical control
    environment (source index) (target index) (sourceCanonical index) (targetCanonical index)
    (retained index)) reference amplitude

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Multiplication

/-!
# The same actual call record on mixed coherent enable and normal sectors

One real outcome path, original Store and arbitrary external Reference
are retained. Arithmetic promises are pointwise implications from the
actual selectors, allowing coherent sums of selected and arbitrary
unselected labels. No probabilistic mixture of selector sectors is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open scoped BigOperators
open Execution EncodedBit.WindowLookup NormalizedVector

attribute [local irreducible] modulus Native.ket Window.ket inputState
  divisionOutput multiplicationOutput

private lemma coherent_of_common_basis {Physical : Register} {Index : Type} [Fintype Index]
    (operator : HilbertOperator Physical) (coefficient : ℂ)
    (first second : Index → HilbertVector Physical) (amplitude : Index → ℂ)
    (basis : ∀ index, operator.applyVec (first index) = coefficient • second index) :
    operator.applyVec (∑ index, amplitude index • first index) =
      ∑ index, (amplitude index * coefficient) • second index := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul, basis index, smul_smul]

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)

include distinct

private lemma multiplication_at_anchor (environment : OracleModel.empty.Interpretation)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (admitted : flags.2.1 = true → ActiveDomain input numerator) (address : Window.Address)
    {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        anchor) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (multiplicationOutput stream width widthBound input numerator flags address),
            reference)).vec := by
  have actual := multiplication_branchOperator_ket (services := services) sameWires output mask
    distinct stream width widthBound environment store input numerator flags admitted address
    outcome reference
  have same := Reset.outcomePath_eq (services := services) .numerator sameWires output outcome
    (afterSave .normal (inputState stream width widthBound input numerator flags address)) anchor
  have changed := congrArg (fun path =>
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store path environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (inputState stream width widthBound input numerator flags address), reference)).vec)
    same
  exact changed.symm.trans actual

lemma multiplication_coherent (environment : OracleModel.empty.Interpretation)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    {Reference : Register} {Index : Type} [Fintype Index]
    (input numerator : Index → Fin (2 ^ modulus.size)) (flags : Index → Frame.Controls)
    (address : Index → Window.Address)
    (admitted : ∀ index, (flags index).2.1 = true → ActiveDomain (input index) (numerator index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        anchor) environment Reference).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound (input index) (numerator index) (flags index)
            (address index)), reference index)).vec) =
      ∑ index, (amplitude index * invSqrt2 ^ 256) •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (multiplicationOutput stream width widthBound (input index) (numerator index)
              (flags index) (address index)), reference index)).vec := by
  refine coherent_of_common_basis _ _ _ _ _ ?_
  intro index
  exact multiplication_at_anchor (services := services) sameWires output mask distinct stream width
    widthBound environment store outcome anchor (input index) (numerator index) (flags index)
    (admitted index) (address index) (reference index)

private lemma division_at_anchor (environment : OracleModel.empty.Interpretation)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address)
    (admitted : divisionEnabled stream width widthBound input numerator flags address = true →
      ActiveDomain input numerator)
    {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome anchor)
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (divisionOutput stream width widthBound input numerator flags address admitted),
            reference)).vec := by
  have actual := division_branchOperator_ket (services := services) sameWires output mask distinct
    stream width widthBound environment store input numerator flags normalZero address admitted
    outcome reference
  have same := Reset.outcomePath_eq (services := services) .numerator sameWires output outcome
    (inputState stream width widthBound input numerator flags address) anchor
  have changed := congrArg (fun path =>
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store path environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (inputState stream width widthBound input numerator flags address), reference)).vec)
    same
  exact changed.symm.trans actual

lemma division_coherent (environment : OracleModel.empty.Interpretation)
    (store : Store ctx) (outcome : Word) (anchor : Window.Raw)
    {Reference : Register} {Index : Type} [Fintype Index]
    (input numerator : Index → Fin (2 ^ modulus.size)) (flags : Index → Frame.Controls)
    (normalZero : ∀ index, (flags index).2.1 = false) (address : Index → Window.Address)
    (admitted : ∀ index, divisionEnabled stream width widthBound (input index) (numerator index)
      (flags index) (address index) = true → ActiveDomain (input index) (numerator index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome anchor)
      environment Reference).applyVec
      (∑ index, amplitude index • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound (input index) (numerator index) (flags index)
            (address index)), reference index)).vec) =
      ∑ index, (amplitude index * invSqrt2 ^ 256) •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires
            (divisionOutput stream width widthBound (input index) (numerator index)
              (flags index) (address index) (admitted index)), reference index)).vec := by
  refine coherent_of_common_basis _ _ _ _ _ ?_
  intro index
  exact division_at_anchor (services := services) sameWires output mask distinct stream width
    widthBound environment store outcome anchor (input index) (numerator index) (flags index)
    (normalZero index) (address index) (admitted index) (reference index)

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

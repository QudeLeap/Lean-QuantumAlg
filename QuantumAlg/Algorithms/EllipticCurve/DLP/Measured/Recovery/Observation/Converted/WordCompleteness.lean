/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Converted.CommonBank
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.ControlledPointWords
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.FreeSourceGram
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Complete actual converted point words on the entire retained bank

Each coordinate conversion is the actual runtime unitary on the complete
Numerator register, tensored with identities on selector and Reference. The
pair certificate keeps the physical X-then-Y order on that same register.
Both forward and inverse-coefficient pairs are individually unitary on all
bank inputs, including dirty padding and width zero.

The complete real point-outcome words remain in chronological order between
the four literal conversions. Completeness holds separately at every source
and on arbitrary residual Reference. No identity between an inverse-coefficient
pair and an adjoint is assumed or needed. These proof certificates introduce
no runtime, allocation, resource allowance, actual legal-path identification,
Fourier Gram identity, contraction or success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ConvertedWordCompleteness

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- This is the existing full bank basis, with its original nested product coordinates. -/
def bankRegister (width : Nat) (Reference : Register) : Register :=
  (NumeratorMeasurement.context width).register.prod ((Qudit 2).prod Reference)

private lemma tensor_identity_entry {Arithmetic Reference : Register}
    (operator : UnitaryOperator Arithmetic)
    (row column : (Arithmetic.prod ((Qudit 2).prod Reference)).Index) :
    UnitaryOperator.prodTensor operator
        (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qudit 2))
          (1 : UnitaryOperator Reference)) row column =
      operator row.1 column.1 * (if row.2.1 = column.2.1 then 1 else 0) *
        (if row.2.2 = column.2.2 then 1 else 0) := by
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply,
    UnitaryOperator.unitaryOperator_prodTensor_apply]
  change operator row.1 column.1 *
    ((1 : HilbertOperator (Qudit 2)) row.2.1 column.2.1 *
      (1 : HilbertOperator Reference) row.2.2 column.2.2) = _
  simp only [Matrix.one_apply, mul_assoc]

/-- Certify the same actual coordinate conversion without restricting any bank input. -/
def bankCoordinateUnitary (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) : UnitaryOperator (bankRegister width Reference) :=
  UnitaryOperator.prodTensor
    ((Encoding.runtimeProgram width modulus coefficient coordinate).matrix environment.quantum)
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qudit 2))
      (1 : UnitaryOperator Reference))

/-- The certificate has exactly the literal full-bank conversion matrix. -/
lemma bankCoordinateUnitary_coe (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (Reference : Register) :
    (bankCoordinateUnitary (environment := environment) width modulus coefficient coordinate
      Reference :
      HilbertOperator (bankRegister width Reference)) =
      Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) width
        modulus coefficient coordinate
        Reference := by
  ext row column
  exact tensor_identity_entry
    ((Encoding.runtimeProgram width modulus coefficient coordinate).matrix environment.quantum)
      row column

/-- X is executed first and Y second on the same complete Numerator/selector/Reference bank. -/
def bankPairUnitary (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    UnitaryOperator (bankRegister width Reference) :=
  bankCoordinateUnitary (environment := environment) width modulus coefficient .y Reference *
    bankCoordinateUnitary (environment := environment) width modulus coefficient .x Reference

/-- The pair certificate is the actual product, with neither conversion reordered. -/
lemma bankPairUnitary_coe (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (bankPairUnitary (environment := environment) width modulus coefficient Reference :
      HilbertOperator (bankRegister width Reference)) =
      Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
        coefficient Reference := by
  change (bankCoordinateUnitary (environment := environment) width modulus coefficient .y
    Reference :
      HilbertOperator (bankRegister width Reference)) *
    (bankCoordinateUnitary (environment := environment) width modulus coefficient .x Reference :
      HilbertOperator (bankRegister width Reference)) = _
  rw [bankCoordinateUnitary_coe, bankCoordinateUnitary_coe]
  rfl

/-- Each actual pair preserves the full bank Gram matrix, independently of its coefficient. -/
lemma bankPairOperator_gram (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
      coefficient
      Reference).conjTranspose *
      Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
        coefficient Reference = 1 := by
  have complete := Matrix.mem_unitaryGroup_iff'.mp
    (bankPairUnitary (environment := environment) width modulus coefficient Reference).property
  rw [Matrix.star_eq_conjTranspose, bankPairUnitary_coe] at complete
  exact complete

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The literal four conversions surround one ordered complete point word. -/
def convertedWord {Source : Type} (coefficient : (ZMod p)ˣ)
    (Reference : Register) (stages : List (ControlledPointWords.Stage E Source))
    (path : Fin stages.length → ControlledPointWords.Outcome p.size) (source : Source) :
    Matrix (Recovery.Point.Instrument.FiberBank p.size Reference)
      (Recovery.Point.Instrument.FiberBank p.size Reference) ℂ :=
  Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
    (InPlaceTarget.modulusWord p) coefficient
    Reference *
    ControlledPointWords.bankWord (environment := environment) E Reference stages path source *
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference

/-- Every source keeps the complete converted family over all real full point outcomes. -/
lemma convertedWord_complete {Source : Type}
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (stages : List (ControlledPointWords.Stage E Source)) (source : Source) :
    ∑ path : Fin stages.length → ControlledPointWords.Outcome p.size,
      (convertedWord (environment := environment) E coefficient Reference stages path
        source).conjTranspose *
        convertedWord (environment := environment) E coefficient Reference stages path source = 1
          := by
  simpa only [convertedWord] using
    FreeSourceGram.selected_suffix_complete
    (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference)
    (fun path => ControlledPointWords.bankWord (environment := environment) E Reference stages
      path source)
    (fun _ => Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (InPlaceTarget.modulusWord p)
      coefficient Reference)
    (bankPairOperator_gram p.size (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference)
    (ControlledPointWords.bankWord_complete E Reference stages source)
    (fun _ => bankPairOperator_gram p.size (InPlaceTarget.modulusWord p) coefficient Reference)

/-- The second block is left of the first, with all four actual conversions kept outside. -/
def convertedPairWord {FirstSource SecondSource : Type}
    (coefficient : (ZMod p)ˣ)
    (Reference : Register) (first : List (ControlledPointWords.Stage E FirstSource))
    (second : List (ControlledPointWords.Stage E SecondSource))
    (firstPath : Fin first.length → ControlledPointWords.Outcome p.size)
    (secondPath : Fin second.length → ControlledPointWords.Outcome p.size)
    (firstSource : FirstSource) (secondSource : SecondSource) :
    Matrix (Recovery.Point.Instrument.FiberBank p.size Reference)
      (Recovery.Point.Instrument.FiberBank p.size Reference) ℂ :=
  Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
    (InPlaceTarget.modulusWord p) coefficient
    Reference *
    (ControlledPointWords.bankWord (environment := environment) E Reference second secondPath
      secondSource *
      ControlledPointWords.bankWord (environment := environment) E Reference first firstPath
        firstSource) *
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference

/-- Both sourcewise blocks are complete, including empty words and every dirty bank column. -/
lemma convertedPairWord_complete {FirstSource SecondSource : Type}
    (coefficient : (ZMod p)ˣ)
    (Reference : Register) (first : List (ControlledPointWords.Stage E FirstSource))
    (second : List (ControlledPointWords.Stage E SecondSource))
    (firstSource : FirstSource) (secondSource : SecondSource) :
    ∑ firstPath : Fin first.length → ControlledPointWords.Outcome p.size,
      ∑ secondPath : Fin second.length → ControlledPointWords.Outcome p.size,
        (convertedPairWord (environment := environment) E coefficient Reference first second
          firstPath secondPath
          firstSource secondSource).conjTranspose *
        convertedPairWord (environment := environment) E coefficient Reference first second
          firstPath secondPath
          firstSource secondSource = 1 := by
  let family := fun paths :
      (Fin first.length → ControlledPointWords.Outcome p.size) ×
        (Fin second.length → ControlledPointWords.Outcome p.size) =>
    ControlledPointWords.bankWord (environment := environment) E Reference second paths.2
      secondSource *
      ControlledPointWords.bankWord (environment := environment) E Reference first paths.1
        firstSource
  have complete : ∑ paths, (family paths).conjTranspose * family paths = 1 := by
    dsimp only [family]
    rw [Fintype.sum_prod_type]
    exact FreeSourceGram.composed_complete
      (fun path => ControlledPointWords.bankWord (environment := environment) E Reference first
        path firstSource)
      (fun path => ControlledPointWords.bankWord (environment := environment) E Reference second
        path secondSource)
      (ControlledPointWords.bankWord_complete E Reference first firstSource)
      (ControlledPointWords.bankWord_complete E Reference second secondSource)
  simpa only [Fintype.sum_prod_type, family, convertedPairWord] using
    FreeSourceGram.selected_suffix_complete
      (Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
        (InPlaceTarget.modulusWord p)
        coefficient⁻¹ Reference) family
      (fun _ => Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
        (InPlaceTarget.modulusWord p)
        coefficient Reference)
      (bankPairOperator_gram p.size (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference)
      complete
      (fun _ => bankPairOperator_gram p.size (InPlaceTarget.modulusWord p) coefficient Reference)

end

end ConvertedWordCompleteness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

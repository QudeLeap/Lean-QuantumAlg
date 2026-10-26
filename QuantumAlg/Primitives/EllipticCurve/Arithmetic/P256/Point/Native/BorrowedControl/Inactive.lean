/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inactive

/-!
# F560-disabled arithmetic retains arbitrary original point coordinates

The original source and accumulator can be any binary words. Real source
doublings and their full inverse are retained in the MAC; square copy and
uncopy also execute. The original three flags and square-copy A have their
stated initialized values, and the entire complement is identical at output.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

lemma macProgram_inactive (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (retained : Placement.Rest ports) (disabled : (controlBit ports).get retained = false) :
    (macProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source target multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.program_inactive (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports))
      environment ((((source, target), false), (false, false)), (multiplier, retained))
      disabled rfl)

lemma inverseMacProgram_inactive (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (retained : Placement.Rest ports) (disabled : (controlBit ports).get retained = false) :
    (inverseMacProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source target multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Inverse.program_inactive (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports))
      environment ((((source, target), false), (false, false)), (multiplier, retained))
      disabled rfl)

private lemma square_at_ports_inactive (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target : Word)
    (retained : Placement.Rest ports) (disabled : (controlBit ports).get retained = false) :
    ((Placement.layout ports).place
      (Accumulate.Square.program (Placement.restEncoding ports) (controlBit ports))).applyNormalized
        environment (ket (arithmeticState ports source target Horner.zeroWord retained)) =
      ket (arithmeticState ports source target Horner.zeroWord retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Square.program_inactive (Placement.restEncoding ports)
      (controlBit ports) environment source target retained disabled)

lemma subtractSquareProgram_inactive (environment : OracleModel.empty.Interpretation)
    (source target : Word) (retained : Placement.Rest squarePorts)
    (disabled : (controlBit squarePorts).get retained = false) :
    subtractSquareProgram.applyNormalized environment
        (ket (arithmeticState squarePorts source target Horner.zeroWord retained)) =
      ket (arithmeticState squarePorts source target Horner.zeroWord retained) :=
  square_at_ports_inactive squarePorts environment source target retained disabled

lemma macProgram_inactive_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (disabled : ∀ index, (controlBit ports).get (retained index) = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (macProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index) (target index)
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _
    (fun index => macProgram_inactive ports environment (source index) (target index)
      (multiplier index) (retained index) (disabled index)) reference amplitude

lemma inverseMacProgram_inactive_reference (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target multiplier : Index → Word)
    (retained : Index → Placement.Rest ports)
    (disabled : ∀ index, (controlBit ports).get (retained index) = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator (inverseMacProgram ports) environment Reference)
        (referenceVector (fun index => arithmeticState ports (source index) (target index)
          (multiplier index) (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState ports (source index) (target index)
        (multiplier index) (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _
    (fun index => inverseMacProgram_inactive ports environment (source index) (target index)
      (multiplier index) (retained index) (disabled index)) reference amplitude

lemma subtractSquareProgram_inactive_reference
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (source target : Index → Word)
    (retained : Index → Placement.Rest squarePorts)
    (disabled : ∀ index, (controlBit squarePorts).get (retained index) = false)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator subtractSquareProgram environment Reference)
        (referenceVector (fun index => arithmeticState squarePorts (source index) (target index)
          Horner.zeroWord (retained index)) reference amplitude) =
      referenceVector (fun index => arithmeticState squarePorts (source index) (target index)
        Horner.zeroWord (retained index)) reference amplitude :=
  coherent_of_basis _ environment _ _
    (fun index => subtractSquareProgram_inactive environment (source index) (target index)
      (retained index) (disabled index)) reference amplitude

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

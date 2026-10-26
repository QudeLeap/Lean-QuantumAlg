/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Exceptional
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Offset.Correctness

/-! # Exceptional table-word addition on the same original physical point systems -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

namespace Exceptional

noncomputable section

open EncodedBit Horner

private lemma raw_apply {Saved : Type} (saved : BinaryLabelEncoding Saved)
    (enable normal : EncodedBit saved) (distinct : enable.wire ≠ normal.wire)
    (environment : OracleModel.empty.Interpretation) (source target : Word) (retained : Saved)
    (sourceCanonical : (enable.get retained && Bool.not (normal.get retained)) = true →
      Canonical source)
    (targetCanonical : (enable.get retained && Bool.not (normal.get retained)) = true →
      Canonical target) :
    (program saved enable normal distinct).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode
            ((((source, target), false), (false, false)), retained)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode
          ((((source, if enable.get retained && Bool.not (normal.get retained) then
            ModularAddition.modularSumWord source target else target), false),
            (false, false)), retained))) :=
  ((program_realizes saved enable normal distinct environment).apply_encoded_ket _).trans
    (congrArg (fun state => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding saved).encode state)))
        (gates_admitted saved enable normal distinct source target retained
          sourceCanonical targetCanonical))

namespace Placed

def enable (ports : PortAssignment) : EncodedBit (Placement.savedEncoding ports) :=
  Offset.Placed.selector ports

def normal (ports : PortAssignment) : EncodedBit (Placement.savedEncoding ports) :=
  Native.outerBit ports .normal

/-- F560 and N837 remain separate original systems under the complete arithmetic placement. -/
lemma enable_normal_ne (ports : PortAssignment) : (enable ports).wire ≠ (normal ports).wire := by
  intro same
  have both : (operandSavedBit (Placement.savedEncoding ports) (enable ports)).wire =
      (operandSavedBit (Placement.savedEncoding ports) (normal ports)).wire := by
    apply Fin.ext
    have positions := congrArg Fin.val same
    change 515 + (enable ports).wire.val = 515 + (normal ports).wire.val
    omega
  have physical := congrArg (Placement.completeWires ports) both
  have first : Placement.completeWires ports
      (operandSavedBit (Placement.savedEncoding ports) (enable ports)).wire =
        Native.BorrowedControl.flag.wire :=
    Placement.completeWires_rest ports Native.BorrowedControl.flag
      (Native.BorrowedControl.outside ports)
  have second : Placement.completeWires ports
      (operandSavedBit (Placement.savedEncoding ports) (normal ports)).wire =
        Frame.normalBit.wire :=
    Placement.completeWires_rest ports Frame.normalBit
      (Placement.suffix_outside ports Frame.normalBit (by rw [Frame.normalBit_wire]; decide))
  rw [first, second] at physical
  have positions := congrArg Fin.val physical
  rw [Native.BorrowedControl.flag_wire, Frame.normalBit_wire] at positions
  omega

/-- Both real controls and the negative-control restoration are native instructions. -/
def program (ports : PortAssignment) : Native.Circuit :=
  (Placement.layout ports).place (Exceptional.program (Placement.savedEncoding ports)
    (enable ports) (normal ports) (enable_normal_ne ports))

/-- Complete raw basis action restores the actual two controls and original arithmetic flags. -/
lemma program_apply (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    (source target third : Word) (retained : Placement.Rest ports)
    (sourceCanonical : ((Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained)) = true → Canonical source)
    (targetCanonical : ((Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained)) = true → Canonical target) :
    (program ports).applyNormalized environment
        (Native.ket (Native.arithmeticState ports source target third retained)) =
      Native.ket (Native.arithmeticState ports source
        (if (Native.BorrowedControl.controlBit ports).get retained &&
          Bool.not ((Native.controlBit ports .normal).get retained) then
            ModularAddition.modularSumWord source target else target) third retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (raw_apply (Placement.savedEncoding ports) (enable ports) (normal ports)
      (enable_normal_ne ports) environment source target (third, retained)
      sourceCanonical targetCanonical)

/-- The same actual exception gate word retains mixed coherent controls and arbitrary Reference. -/
lemma program_reference (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (source target third : Index → Word)
    (retained : Index → Placement.Rest ports)
    (sourceCanonical : ∀ index, ((Native.BorrowedControl.controlBit ports).get (retained index) &&
      Bool.not ((Native.controlBit ports .normal).get (retained index))) = true →
        Canonical (source index))
    (targetCanonical : ∀ index, ((Native.BorrowedControl.controlBit ports).get (retained index) &&
      Bool.not ((Native.controlBit ports .normal).get (retained index))) = true →
        Canonical (target index)) (reference : Index → Reference.Index)
    (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (Native.referenceOperator (program ports) environment Reference)
        (Native.referenceVector (fun index => Native.arithmeticState ports (source index)
          (target index) (third index) (retained index)) reference amplitude) =
      Native.referenceVector (fun index => Native.arithmeticState ports (source index)
        (if (Native.BorrowedControl.controlBit ports).get (retained index) &&
          Bool.not ((Native.controlBit ports .normal).get (retained index)) then
            ModularAddition.modularSumWord (source index) (target index) else target index)
        (third index) (retained index)) reference amplitude :=
  Native.coherent_of_basis _ environment _ _ (fun index => program_apply ports environment
    (source index) (target index) (third index) (retained index)
    (sourceCanonical index) (targetCanonical index)) reference amplitude

end Placed

end

end Exceptional

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Offset

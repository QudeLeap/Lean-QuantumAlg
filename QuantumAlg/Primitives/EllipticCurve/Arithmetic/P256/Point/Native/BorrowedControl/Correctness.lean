/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Inactive

/-!
# Complete original-state equations for arithmetic selected by F560

The complement contains all original C/N/W, the other pool positions, padding
and source history. Its value is identical in each output label. F560 need
not be zero. The false clean-Horner branch admits arbitrary source and
multiplier words; its target and three real arithmetic flags are zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

lemma flag_arithmeticState (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) :
    flag.get (arithmeticState ports source target multiplier retained) =
      (controlBit ports).get retained :=
  arithmeticState_restBit ports flag (outside ports) source target multiplier retained

/-- Canonical active multiplication and complete restoration retain the original F560 value. -/
lemma cleanProgram_canonical (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (canonical : Canonical source) (retained : Placement.Rest ports) :
    (cleanProgram ports choice).applyNormalized environment
        (ket (arithmeticState ports source Horner.zeroWord multiplier retained)) =
      ket (arithmeticState ports source
        (Horner.productWord source
          ((quantumMultiplier ports choice).value source (multiplier, retained))
          ((controlBit ports).get retained)) multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Horner.cleanProgram_product (Placement.savedEncoding ports) (quantumMultiplier ports choice)
      (outerBit ports) (outer_multiplier_ne ports choice) environment source canonical
      (multiplier, retained))

/-- Arbitrary inactive original source and multiplier labels have exact unit-phase identity. -/
lemma cleanProgram_inactive (ports : PortAssignment) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (retained : Placement.Rest ports) (disabled : (controlBit ports).get retained = false) :
    (cleanProgram ports choice).applyNormalized environment
        (ket (arithmeticState ports source Horner.zeroWord multiplier retained)) =
      ket (arithmeticState ports source Horner.zeroWord multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Horner.cleanProgram_inactive (Placement.savedEncoding ports) (quantumMultiplier ports choice)
      (outerBit ports) (outer_multiplier_ne ports choice) environment source
      (multiplier, retained) disabled)

lemma macProgram_canonical (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    (macProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.accumulatedWord source multiplier target ((controlBit ports).get retained))
        multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.program_canonical (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports))
      environment source target sourceCanonical targetCanonical (multiplier, retained))

lemma inverseMacProgram_canonical (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    (inverseMacProgram ports).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.Inverse.differenceWord source multiplier target
          ((controlBit ports).get retained)) multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Inverse.program_canonical (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports)
      (Accumulate.Square.outer_multiplier_ne (Placement.restEncoding ports) (controlBit ports))
      environment source target sourceCanonical targetCanonical (multiplier, retained))

private lemma square_at_ports (ports : PortAssignment)
    (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    ((Placement.layout ports).place
      (Accumulate.Square.program (Placement.restEncoding ports) (controlBit ports))).applyNormalized
        environment (ket (arithmeticState ports source target Horner.zeroWord retained)) =
      ket (arithmeticState ports source
        (Accumulate.Inverse.differenceWord source source target
          ((controlBit ports).get retained)) Horner.zeroWord retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Square.program_canonical (Placement.restEncoding ports)
      (controlBit ports) environment source target sourceCanonical targetCanonical retained)

/-- The actual original A copy/uncopy is retained beside the arbitrary canonical X accumulator. -/
lemma subtractSquareProgram_canonical (environment : OracleModel.empty.Interpretation)
    (source target : Word) (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest squarePorts) :
    subtractSquareProgram.applyNormalized environment
        (ket (arithmeticState squarePorts source target Horner.zeroWord retained)) =
      ket (arithmeticState squarePorts source
        (Accumulate.Inverse.differenceWord source source target
          ((controlBit squarePorts).get retained)) Horner.zeroWord retained) :=
  square_at_ports squarePorts environment source target sourceCanonical targetCanonical retained

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

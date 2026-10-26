/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Product
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Correctness

/-!
# Complete physical multiplication and arbitrary-accumulator square subtraction

The actual complete wire grouping supplies these labels. The retained
component contains every other original wire, with arbitrary values.
Only the three real arithmetic flags are initially zero. The clean
Horner target is unconditionally zero; the MAC target is any canonical
residue; only the existing square-copy A word has its separate zero
premise. No inactive-EEA cleanliness is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

/-- Label of the original physical frame in its certified arithmetic coordinates. -/
def arithmeticState (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) : Frame.Raw :=
  (Placement.layout ports).grouping.symm
    ((((source, target), false), (false, false)), (multiplier, retained))

def ket (state : Frame.Raw) :
    NormalizedVector (QubitLayout.canonical Frame.encoding.width).toQuantum.register :=
  NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (Frame.encoding.encode state))

lemma arithmeticState_grouping (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) :
    (Placement.layout ports).grouping (arithmeticState ports source target multiplier retained) =
      ((((source, target), false), (false, false)), (multiplier, retained)) :=
  (Placement.layout ports).grouping.apply_symm_apply _

lemma quantumMultiplier_value (ports : PortAssignment) (choice : Multiplier)
    (source multiplier : Word) (retained : Placement.Rest ports) :
    (quantumMultiplier ports choice).value source (multiplier, retained) =
      (match choice with | .source => source | .retained => multiplier) := by
  cases choice <;> rfl

/-- All 839 original systems have the complete clean-Horner output under either C/N branch. -/
lemma cleanProgram_canonical (ports : PortAssignment) (control : Control) (choice : Multiplier)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (canonical : Canonical source) (retained : Placement.Rest ports) :
    (cleanProgram ports control choice).applyNormalized environment
        (ket (arithmeticState ports source Horner.zeroWord multiplier retained)) =
      ket (arithmeticState ports source
        (Horner.productWord source
          ((quantumMultiplier ports choice).value source (multiplier, retained))
          ((controlBit ports control).get retained)) multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Horner.cleanProgram_product (Placement.savedEncoding ports) (quantumMultiplier ports choice)
      (outerBit ports control) (outer_multiplier_ne ports control choice) environment source
      canonical (multiplier, retained))

/-- Arbitrary canonical target, complete source restoration, and every saved wire retained. -/
lemma macProgram_canonical (ports : PortAssignment) (control : Control)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    (macProgram ports control).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.accumulatedWord source multiplier target
          ((controlBit ports control).get retained))
          multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.program_canonical (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control))
      environment source target sourceCanonical targetCanonical (multiplier, retained))

/-- Every canonical original accumulator is admitted by the same actual native MAC adjoint. -/
lemma inverseMacProgram_canonical (ports : PortAssignment) (control : Control)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    (inverseMacProgram ports control).applyNormalized environment
        (ket (arithmeticState ports source target multiplier retained)) =
      ket (arithmeticState ports source
        (Accumulate.Inverse.differenceWord source multiplier target
          ((controlBit ports control).get retained)) multiplier retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Inverse.program_canonical (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control))
      environment source target sourceCanonical targetCanonical (multiplier, retained))

private lemma square_at_ports (ports : PortAssignment) (control : Control)
    (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) :
    UnitaryCircuit.applyNormalized ((Placement.layout ports).place
        (Accumulate.Square.program (Placement.restEncoding ports) (controlBit ports control)))
      environment
        (ket (arithmeticState ports source target Horner.zeroWord retained)) =
      ket (arithmeticState ports source
        (Accumulate.Inverse.differenceWord source source target
          ((controlBit ports control).get retained)) Horner.zeroWord retained) :=
  (Placement.layout ports).place_ket_of_eq _ _ _
    (Accumulate.Square.program_canonical (Placement.restEncoding ports)
      (controlBit ports control) environment source target sourceCanonical targetCanonical
      retained)

/-- Original Y is retained, arbitrary canonical X loses its selected square,
and the actually clean original A copy word returns to zero. -/
lemma subtractSquareProgram_canonical (control : Control)
    (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest squarePorts) :
    (subtractSquareProgram control).applyNormalized environment
        (ket (arithmeticState squarePorts source target Horner.zeroWord retained)) =
      ket (arithmeticState squarePorts source
        (Accumulate.Inverse.differenceWord source source target
          ((controlBit squarePorts control).get retained)) Horner.zeroWord retained) :=
  square_at_ports squarePorts control environment source target sourceCanonical targetCanonical
    retained

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

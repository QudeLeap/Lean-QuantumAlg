/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Reference

/-!
# Complete native arithmetic between the actual query directions

The real enable and its inverse surround the actual ordinary or exceptional
quantum-word addition. Source A, the other numerical word, every arithmetic
flag, the complete retained frame and the original address are included.
The input is written through the involutive enable coordinates, so the
same laws also cover its disabled sectors without an arithmetic promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

/-- Transport an actual native basis action through both paid whole-digit enable directions. -/
lemma selectedBody_apply (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (body : Native.Circuit) (environment : OracleModel.empty.Interpretation)
    (initial final : Frame.Raw) (address : Address)
    (actual : body.applyNormalized environment (Native.ket initial) = Native.ket final) :
    (selectedBody stream width bounded body).applyNormalized environment
      (ket (Enable.step stream width bounded (streamInput stream initial address))) =
      ket (Enable.step stream width bounded (streamInput stream final address)) := by
  have first := Enable.program_ket stream width bounded environment
    (Enable.step stream width bounded (streamInput stream initial address))
  rw [Enable.step_step] at first
  exact UnitaryCircuit.applyNormalized_seq_of_eq first
    (UnitaryCircuit.applyNormalized_seq_of_eq
      (program_ket_of_eq stream body environment initial final address actual)
      (Enable.inverseProgram_ket stream width bounded environment _))

/-- Ordinary paid table-word addition retains the entire native frame and original address. -/
lemma ordinaryBody_apply (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    (source target third : Word) (retained : Placement.Rest ports) (address : Address)
    (sourceCanonical : (Native.BorrowedControl.controlBit ports).get retained = true →
      Canonical source)
    (targetCanonical : (Native.BorrowedControl.controlBit ports).get retained = true →
      Canonical target) :
    (ordinaryBody stream width bounded ports).applyNormalized environment
      (ket (Enable.step stream width bounded
        (streamInput stream (Native.arithmeticState ports source target third retained) address))) =
      ket (Enable.step stream width bounded
        (streamInput stream (Native.arithmeticState ports source
          (if (Native.BorrowedControl.controlBit ports).get retained then
            ModularAddition.modularSumWord source target else target) third retained) address)) :=
  selectedBody_apply stream width bounded (Chain.Offset.Placed.program ports) environment _ _
    address (Chain.Offset.Placed.program_apply ports environment source target third retained
      sourceCanonical targetCanonical)

/-- The actual exceptional addition keeps both coherent controls and all original work flags. -/
lemma exceptionalBody_apply (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (environment : OracleModel.empty.Interpretation)
    (source target third : Word) (retained : Placement.Rest ports) (address : Address)
    (sourceCanonical : ((Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained)) = true → Canonical source)
    (targetCanonical : ((Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained)) = true → Canonical target) :
    (selectedBody stream width bounded
      (Chain.Offset.Exceptional.Placed.program ports)).applyNormalized environment
      (ket (Enable.step stream width bounded
        (streamInput stream (Native.arithmeticState ports source target third retained) address))) =
      ket (Enable.step stream width bounded
        (streamInput stream (Native.arithmeticState ports source
          (if (Native.BorrowedControl.controlBit ports).get retained &&
            Bool.not ((Native.controlBit ports .normal).get retained) then
            ModularAddition.modularSumWord source target else target) third retained) address)) :=
  selectedBody_apply stream width bounded (Chain.Offset.Exceptional.Placed.program ports)
    environment _ _ address (Chain.Offset.Exceptional.Placed.program_apply ports environment
      source target third retained sourceCanonical targetCanonical)

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

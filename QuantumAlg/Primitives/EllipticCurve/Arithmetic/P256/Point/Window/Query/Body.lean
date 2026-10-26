/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.State
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Pool

/-!
# Complete actual query-body action on the original initialized bank

The real enable, ordinary or exceptional addition, and literal inverse
enable act on the complete original label. Only enabled numerical words
need to be canonical; disabled words remain arbitrary. The original clean
pool supplies the exact three native flag premises internally, while the
actual computed enable itself may be nonzero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

/-- Exact complete-label endpoint of the actual ordinary query body. -/
def ordinaryStep (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) : Raw :=
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  let source := ports.source.value prepared
  let target := ports.target.value prepared
  arithmeticInput stream width bounded ports source
    (if (Native.BorrowedControl.controlBit ports).get retained then
      ModularAddition.modularSumWord source target else target)
    (ports.multiplier.value prepared) retained state.2

/-- Exact complete-label endpoint of the actual E-and-not-N exceptional body. -/
def exceptionalStep (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) : Raw :=
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  let source := ports.source.value prepared
  let target := ports.target.value prepared
  arithmeticInput stream width bounded ports source
    (if (Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained) then
      ModularAddition.modularSumWord source target else target)
    (ports.multiplier.value prepared) retained state.2

/-- The same real ordinary body has this complete basis action, with no caller action callback. -/
lemma ordinaryBody_apply_of_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (environment : OracleModel.empty.Interpretation) (state : Raw)
    (clean : Frame.CleanPool state.1)
    (admitted : let prepared := arithmeticSource stream width bounded state
      let retained := ((Placement.layout ports).grouping prepared).2.2
      (Native.BorrowedControl.controlBit ports).get retained = true →
        Canonical (ports.source.value prepared) ∧ Canonical (ports.target.value prepared)) :
    (ordinaryBody stream width bounded ports).applyNormalized environment (ket state) =
      ket (ordinaryStep stream width bounded ports state) := by
  have represented := state_eq_arithmeticInput stream width bounded ports state clean
  have actual := ordinaryBody_apply stream width bounded ports environment
    (ports.source.value (arithmeticSource stream width bounded state))
    (ports.target.value (arithmeticSource stream width bounded state))
    (ports.multiplier.value (arithmeticSource stream width bounded state))
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2
    state.2 (fun active => (admitted active).1) (fun active => (admitted active).2)
  exact (congrArg (fun initial =>
    (ordinaryBody stream width bounded ports).applyNormalized environment (ket initial))
      represented).trans actual

/-- The same separate N control supplies the exceptional body's actual admitted basis action. -/
lemma exceptionalBody_apply_of_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (environment : OracleModel.empty.Interpretation) (state : Raw)
    (clean : Frame.CleanPool state.1)
    (admitted : let prepared := arithmeticSource stream width bounded state
      let retained := ((Placement.layout ports).grouping prepared).2.2
      ((Native.BorrowedControl.controlBit ports).get retained &&
        Bool.not ((Native.controlBit ports .normal).get retained)) = true →
        Canonical (ports.source.value prepared) ∧ Canonical (ports.target.value prepared)) :
    (selectedBody stream width bounded
      (Chain.Offset.Exceptional.Placed.program ports)).applyNormalized environment (ket state) =
      ket (exceptionalStep stream width bounded ports state) := by
  have represented := state_eq_arithmeticInput stream width bounded ports state clean
  have actual := exceptionalBody_apply stream width bounded ports environment
    (ports.source.value (arithmeticSource stream width bounded state))
    (ports.target.value (arithmeticSource stream width bounded state))
    (ports.multiplier.value (arithmeticSource stream width bounded state))
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2
    state.2 (fun active => (admitted active).1) (fun active => (admitted active).2)
  exact (congrArg (fun initial =>
    (selectedBody stream width bounded
      (Chain.Offset.Exceptional.Placed.program ports)).applyNormalized environment (ket initial))
      represented).trans actual

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resident
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Resident.Reuse.Inactive
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# Actual inactive resident segments on arbitrary original source words

The cleared-pool premises are precisely those of the same accepted resident
program. No original input, saved A word, numerator or small history is
assumed canonical. Both paid enable directions remain in the real program.
These component laws do not identify the old Y with zero before measurement.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

lemma reusedForward_disabled (environment : OracleModel.empty.Interpretation)
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.2.1 = false) :
    Boundary.reusedForward.applyNormalized environment (Native.ket state) = Native.ket state := by
  unfold Boundary.reusedForward
  apply Inversion.Normal.transport_disabled_normal Inversion.modulus_size _ environment _
    state clean control disabled
  intro original pool originalControl originalDisabled
  have address := congrArg Prod.fst pool
  have prefixZero := congrArg (fun value => value.2.1) pool
  have borrow := congrArg (fun value => value.2.2) pool
  exact ControlledResidentReuse.forward_apply_disabled modulus Inversion.modulus_nontrivial
    environment original prefixZero address borrow originalControl originalDisabled

lemma reusedBackward_disabled (environment : OracleModel.empty.Interpretation)
    (state : Frame.Raw) (clean : Frame.CleanPool state)
    (control : state.1.1.1.control = false) (disabled : state.2.2.1 = false) :
    Boundary.reusedBackward.applyNormalized environment (Native.ket state) = Native.ket state := by
  unfold Boundary.reusedBackward
  apply Inversion.Normal.transport_disabled_normal Inversion.modulus_size _ environment _
    state clean control disabled
  intro original pool originalControl originalDisabled
  have address := congrArg Prod.fst pool
  have prefixZero := congrArg (fun value => value.2.1) pool
  have borrow := congrArg (fun value => value.2.2) pool
  exact ControlledResidentReuse.backward_apply_disabled modulus Inversion.modulus_nontrivial
    environment original prefixZero address borrow originalControl originalDisabled

/-- N may be zero even for an enabled nonzero window with exceptional second difference. -/
lemma residentWithNormal_forward_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1)
    (control : (Window.Enable.step stream width bounded state).1.1.1.1.control = false)
    (disabled : (Window.Enable.step stream width bounded state).1.2.2.1 = false) :
    (residentWithNormal stream width bounded Boundary.reusedForward).applyNormalized
      environment (Window.ket state) = Window.ket state := by
  have actual := residentWithNormal_apply stream width bounded Boundary.reusedForward environment
    state (Window.Enable.step stream width bounded state).1
    (reusedForward_disabled environment _ clean control disabled)
  exact actual.trans (congrArg Window.ket (Window.Enable.step_step stream width bounded state))

lemma residentWithNormal_backward_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1)
    (control : (Window.Enable.step stream width bounded state).1.1.1.1.control = false)
    (disabled : (Window.Enable.step stream width bounded state).1.2.2.1 = false) :
    (residentWithNormal stream width bounded Boundary.reusedBackward).applyNormalized
      environment (Window.ket state) = Window.ket state := by
  have actual := residentWithNormal_apply stream width bounded Boundary.reusedBackward environment
    state (Window.Enable.step stream width bounded state).1
    (reusedBackward_disabled environment _ clean control disabled)
  exact actual.trans (congrArg Window.ket (Window.Enable.step_step stream width bounded state))

/-- The first inactive forward retains arbitrary original words and reverses temporary N. -/
lemma firstResident_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (disabled : (Control.prepareStep stream width bounded state).1.2.2.1 = false) :
    (Control.firstResidentProgram stream width bounded).applyNormalized environment
      (Window.ket state) = Window.ket state := by
  have actual := residentWithTemporary_apply stream width bounded Inversion.Normal.program
    environment state (Control.prepareStep stream width bounded state).1
    (Inversion.Normal.program_apply_disabled environment _ clean control disabled)
  exact actual.trans (congrArg Window.ket (restore_prepare stream width bounded state))

lemma residentWithTemporary_backward_disabled (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (disabled : (Control.prepareStep stream width bounded state).1.2.2.1 = false) :
    (residentWithTemporary stream width bounded Boundary.reusedBackward).applyNormalized
      environment (Window.ket state) = Window.ket state := by
  have actual := residentWithTemporary_apply stream width bounded Boundary.reusedBackward
    environment state (Control.prepareStep stream width bounded state).1
    (reusedBackward_disabled environment _ clean control disabled)
  exact actual.trans (congrArg Window.ket (restore_prepare stream width bounded state))

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

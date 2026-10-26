/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Phase
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.State

/-!
# Actual inactive arithmetic tails retain the saved old numerator character

The input here is after physical Y reset. The saved A word is arbitrary,
as are original X and small history. Both actual resident directions fix
the complete cleared-pool inactive label. The paid phase then uses saved A,
and the unconditional numerical swap returns it to Y. No pre-H zero-Y
assumption or canonical inactive-word premise is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

lemma divisionTail_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw) (outcome : Word)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (normal : (Control.prepareStep stream width bounded state).1.2.2.1 = false)
    (reset : phasePorts.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout phasePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout phasePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout phasePorts).grouping state.1).1.2.2 = false)
    (disabled : (Phase.physicalSelector .enable).get state.1 = false) :
    (divisionTail stream width bounded outcome).applyVec environment (Window.ket state).vec =
      WalshHadamard.walshSign outcome (phasePorts.multiplier.value state.1) •
        (Window.ket (Swap.step state)).vec := by
  have resident := congrArg NormalizedVector.vec
    (residentWithTemporary_backward_disabled stream width bounded environment state clean
      control normal)
  change (residentWithTemporary stream width bounded Boundary.reusedBackward).applyVec
    environment (Window.ket state).vec = (Window.ket state).vec at resident
  have phase := phaseThenSwap_applyVec .enable environment state outcome reset flags (fun active =>
    False.elim (Bool.noConfusion (disabled.symm.trans active)))
  dsimp only [divisionTail]
  rw [UnitaryCircuit.applyVec_seq, resident]
  simpa only [disabled, Save.savedWord, Bool.false_eq_true, ↓reduceIte] using phase

lemma multiplicationTail_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw) (outcome : Word)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1)
    (control : (Window.Enable.step stream width bounded state).1.1.1.1.control = false)
    (normal : (Window.Enable.step stream width bounded state).1.2.2.1 = false)
    (reset : phasePorts.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout phasePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout phasePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout phasePorts).grouping state.1).1.2.2 = false)
    (disabled : (Phase.physicalSelector .normal).get state.1 = false) :
    (multiplicationTail stream width bounded outcome).applyVec environment (Window.ket state).vec =
      WalshHadamard.walshSign outcome (phasePorts.multiplier.value state.1) •
        (Window.ket (Swap.step state)).vec := by
  have forward := congrArg NormalizedVector.vec
    (residentWithNormal_forward_disabled stream width bounded environment state clean
      control normal)
  have backward := congrArg NormalizedVector.vec
    (residentWithNormal_backward_disabled stream width bounded environment state clean
      control normal)
  change (residentWithNormal stream width bounded Boundary.reusedForward).applyVec
    environment (Window.ket state).vec = (Window.ket state).vec at forward
  change (residentWithNormal stream width bounded Boundary.reusedBackward).applyVec
    environment (Window.ket state).vec = (Window.ket state).vec at backward
  have phase := suffixPhase_applyVec_of_flags .normal environment state outcome reset flags
    (fun active => False.elim (Bool.noConfusion (disabled.symm.trans active)))
  dsimp only [multiplicationTail]
  rw [UnitaryCircuit.applyVec_seq, forward, UnitaryCircuit.applyVec_seq,
    phase, UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_seq, backward]
  have corrected := phaseThenSwap_applyVec .normal environment state outcome reset flags
    (fun active => False.elim (Bool.noConfusion (disabled.symm.trans active)))
  rw [UnitaryCircuit.applyVec_seq, phase, UnitaryCircuit.applyVec_smul] at corrected
  simpa only [disabled, Save.savedWord, Bool.false_eq_true, ↓reduceIte] using corrected


/-- The actual inactive division prefix saves old Y after its inactive resident identity. -/
lemma divisionBeforeReset_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (normal : (Control.prepareStep stream width bounded state).1.2.2.1 = false)
    (disabled : (Phase.physicalSelector .enable).get state.1 = false) :
    (beforeReset .division stream width bounded).applyNormalized environment (Window.ket state) =
      Window.ket (afterSave .enable state) :=
  UnitaryCircuit.applyNormalized_seq_of_eq
    (firstResident_disabled stream width bounded environment state clean control normal)
    (save_apply .enable environment state zero flags (fun active =>
      False.elim (Bool.noConfusion (disabled.symm.trans
        ((Phase.selector_get Save.ports .enable state.1).trans active)))))

/-- The real inactive multiplication prefix saves an arbitrary old binary numerator. -/
lemma multiplicationBeforeReset_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw)
    (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (disabled : (Phase.physicalSelector .normal).get state.1 = false) :
    (beforeReset .multiplication stream width bounded).applyNormalized environment
        (Window.ket state) = Window.ket (afterSave .normal state) :=
  save_apply .normal environment state zero flags (fun active =>
    False.elim (Bool.noConfusion (disabled.symm.trans
      ((Phase.selector_get Save.ports .normal state.1).trans active))))

private lemma temporary_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Window.normalBit.get (Control.prepareStep stream width bounded state) =
      (Window.normalBit.get state ^^ Window.Enable.outputBit.get state) :=
  (Window.Enable.step_other stream width bounded Window.normalBit Control.flag_normal_ne
    (Control.copyStep state)).trans (Control.copyStep_normal state)

private lemma clear_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Window.normalBit.get (Window.Enable.step stream width bounded state) =
      Window.normalBit.get state :=
  Window.Enable.step_other stream width bounded Window.normalBit Control.flag_normal_ne state

/-- On the real inactive division record the phase sees the saved old Y, for every binary Y. -/
lemma divisionTail_afterReset_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (state : Window.Raw) (outcome : Word)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1)
    (control : (Control.prepareStep stream width bounded state).1.1.1.1.control = false)
    (normal : (Control.prepareStep stream width bounded state).1.2.2.1 = false)
    (disabled : (Phase.physicalSelector .enable).get state.1 = false) :
    (divisionTail stream width bounded outcome).applyVec environment
        (Window.ket (afterReset .enable state)).vec =
      WalshHadamard.walshSign outcome (Frame.numerator state.1) •
        (Window.ket (Swap.step (afterReset .enable state))).vec := by
  have afterControl :
      (Control.prepareStep stream width bounded (afterReset .enable state)).1.1.1.1.control =
        false :=
    (congrArg (fun original : MAU.Inversion.SharedEEA.Registers 256 => original.control)
      (prepare_source stream width bounded (afterReset .enable state))).trans
      ((afterReset_control .enable state flags).trans
        ((congrArg (fun original : MAU.Inversion.SharedEEA.Registers 256 => original.control)
          (prepare_source stream width bounded state)).symm.trans control))
  have afterNormal :
      (Control.prepareStep stream width bounded (afterReset .enable state)).1.2.2.1 = false :=
    (temporary_normal stream width bounded (afterReset .enable state)).trans
      ((congrArg₂ Bool.xor (afterReset_selector .enable .normal state flags)
        (afterReset_selector .enable .enable state flags)).trans
        ((temporary_normal stream width bounded state).symm.trans normal))
  have actual := divisionTail_disabled stream width bounded environment
    (afterReset .enable state) outcome
    (prepare_afterReset_cleanPool .enable stream width bounded state flags clean)
    afterControl afterNormal (afterReset_numerator .enable state)
    (afterReset_arithmeticFlags .enable phasePorts state)
    ((afterReset_selector .enable .enable state flags).trans disabled)
  have saved : phasePorts.multiplier.value (afterReset .enable state).1 =
      Frame.numerator state.1 := by
    change Frame.work1 (afterReset .enable state).1 = Frame.numerator state.1
    simpa only [disabled, Save.savedWord, Bool.false_eq_true, ↓reduceIte] using
      afterReset_work1_value .enable state
  rw [saved] at actual
  exact actual

/-- The actual inactive multiplication forward and own dagger retain the same saved-Y character. -/
lemma multiplicationTail_afterReset_disabled (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) (outcome : Word)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1)
    (control : (Window.Enable.step stream width bounded state).1.1.1.1.control = false)
    (normal : (Window.Enable.step stream width bounded state).1.2.2.1 = false) :
    (multiplicationTail stream width bounded outcome).applyVec environment
        (Window.ket (afterReset .normal state)).vec =
      WalshHadamard.walshSign outcome (Frame.numerator state.1) •
        (Window.ket (Swap.step (afterReset .normal state))).vec := by
  have disabled : (Phase.physicalSelector .normal).get state.1 = false :=
    (clear_normal stream width bounded state).symm.trans normal
  have afterControl :
      (Window.Enable.step stream width bounded (afterReset .normal state)).1.1.1.1.control =
        false :=
    (congrArg (fun original : MAU.Inversion.SharedEEA.Registers 256 => original.control)
      (enable_source stream width bounded (afterReset .normal state))).trans
      ((afterReset_control .normal state flags).trans
        ((congrArg (fun original : MAU.Inversion.SharedEEA.Registers 256 => original.control)
          (enable_source stream width bounded state)).symm.trans control))
  have afterNormal :
      (Window.Enable.step stream width bounded (afterReset .normal state)).1.2.2.1 = false :=
    (clear_normal stream width bounded (afterReset .normal state)).trans
      ((afterReset_selector .normal .normal state flags).trans disabled)
  have actual := multiplicationTail_disabled stream width bounded environment
    (afterReset .normal state) outcome
    (enable_afterReset_cleanPool .normal stream width bounded state flags clean)
    afterControl afterNormal (afterReset_numerator .normal state)
    (afterReset_arithmeticFlags .normal phasePorts state)
    ((afterReset_selector .normal .normal state flags).trans disabled)
  have saved : phasePorts.multiplier.value (afterReset .normal state).1 =
      Frame.numerator state.1 := by
    change Frame.work1 (afterReset .normal state).1 = Frame.numerator state.1
    simpa only [disabled, Save.savedWord, Bool.false_eq_true, ↓reduceIte] using
      afterReset_work1_value .normal state
  rw [saved] at actual
  exact actual

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Conjunction

/-!
# External selection of the actual full geometry and phase conjunction

Both full geometry-validity circuits still execute. Only the two small
source-phase words receive an external native control. Alternating the
actual calls restores arbitrary original Iter, all temporary geometry,
and both external coordinates. Inactive execution accepts zero input
and arbitrary original source fields.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticConjunction

noncomputable section

open EncodedBit

private def validityStep (width : Nat) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  (ArithmeticGuard.validityStep width state.1, state.2)

private lemma validityStep_pool (width : Nat) (state : ControlledFrame.Data width) :
    (validityStep width state).1.2 = state.1.2 :=
  ArithmeticGuard.validityStep_pool width state.1

private lemma phaseStep_pool (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    (ControlledArithmeticPhase.step width signed coefficient state).1.2 = state.1.2 := by
  rw [ControlledArithmeticPhase.step,
    ControlledFrame.selected_predicateFlip width (ArithmeticGuard.flag width 4)
      (fun source => ArithmeticGuard.condition width signed coefficient source &&
        (ArithmeticGuard.flag width 3).get source) state]
  split
  · exact ArithmeticGuard.step_pool width signed coefficient state.1
  · rfl

private lemma phaseStep_eq (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    ControlledArithmeticPhase.step width signed coefficient state =
      (if state.2.1 then ArithmeticGuard.step width signed coefficient state.1 else state.1,
        state.2) := by
  rw [ControlledArithmeticPhase.step,
    ControlledFrame.selected_predicateFlip width (ArithmeticGuard.flag width 4)
      (fun source => ArithmeticGuard.condition width signed coefficient source &&
        (ArithmeticGuard.flag width 3).get source) state]
  rfl

private lemma originalValidityStep_self (width : Nat) (state : Scanned.Data width) :
    ArithmeticGuard.validityStep width (ArithmeticGuard.validityStep width state) = state := by
  have stable : ArithmeticGuard.valid width ((ArithmeticGuard.flag width 3).flip state) =
      ArithmeticGuard.valid width state := rfl
  cases selected : ArithmeticGuard.valid width state <;>
    simp only [ArithmeticGuard.validityStep, predicateFlip, selected, stable,
      Bool.false_eq_true, if_false, if_true, EncodedBit.flip_flip]

/-- Independent selection changes only original Ctrl and restores arbitrary original Iter. -/
def step (width : Nat) (signed coefficient : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  (if state.2.1 then ArithmeticGuard.conjunctionStep width signed coefficient state.1
    else state.1, state.2)

private lemma conjunction_steps (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) :
    ControlledArithmeticPhase.step width signed coefficient
        (validityStep width (ControlledArithmeticPhase.step width signed coefficient
          (validityStep width state))) = step width signed coefficient state := by
  cases selected : state.2.1 <;>
    simp only [phaseStep_eq, validityStep, selected, if_true, step]
  · exact congrArg (fun source => (source, state.2)) (originalValidityStep_self width state.1)
  · exact congrArg (fun source => (source, state.2))
      (ArithmeticGuard.conjunction_steps width signed coefficient state.1)

/-- Four actual calls keep the full geometry tests and their true native dependency order. -/
def program (width : Nat) (signed coefficient : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  (ControlledFrame.liftProgram width (GeometryValidity.fullProgram width)).seq
    ((ControlledArithmeticPhase.program width signed coefficient).seq
      ((ControlledFrame.liftProgram width (GeometryValidity.fullProgram width)).seq
        (ControlledArithmeticPhase.program width signed coefficient)))

private lemma validityProgram_apply_encoded_ket (width : Nat)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (clean : state.1.2.2.1 = 0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width)) :
    (ControlledFrame.liftProgram width (GeometryValidity.fullProgram width)).applyNormalized
        environment (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (validityStep width state))) := by
  exact UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (Scanned.encoding width) ExternalWord.flags (GeometryValidity.fullProgram width)
    state.1 (ArithmeticGuard.validityStep width state.1) state.2
    (GeometryValidity.fullProgram_apply_encoded_ket width environment state.1 clean)

/-- Same source-prefix premise as the actual original validity, with no phase-domain restriction. -/
lemma program_apply_encoded_ket (width : Nat) (signed coefficient : Bool)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (clean : state.1.2.2.1 = 0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width)) :
    (program width signed coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width signed coefficient state))) := by
  let first := validityStep width state
  let second := ControlledArithmeticPhase.step width signed coefficient first
  let third := validityStep width second
  have firstClean : first.1.2.2.1 =
      0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width) :=
    (congrArg (fun pool : Pool width => pool.2.1) (validityStep_pool width state)).trans clean
  have secondClean : second.1.2.2.1 =
      0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width) :=
    (congrArg (fun pool : Pool width => pool.2.1)
      (phaseStep_pool width signed coefficient first)).trans firstClean
  have firstActual := validityProgram_apply_encoded_ket width environment state clean
  have phaseActual :=
    ControlledArithmeticPhase.program_realizes width signed coefficient environment
  have secondActual := phaseActual.apply_encoded_ket first
  have thirdActual := validityProgram_apply_encoded_ket width environment second secondClean
  have fourthActual := phaseActual.apply_encoded_ket third
  have tail := UnitaryCircuit.applyNormalized_seq_of_eq thirdActual fourthActual
  have body := UnitaryCircuit.applyNormalized_seq_of_eq secondActual tail
  have complete := UnitaryCircuit.applyNormalized_seq_of_eq firstActual body
  change (program width signed coefficient).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode state))) =
    NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((ControlledFrame.encoding width).encode
        (ControlledArithmeticPhase.step width signed coefficient
          (validityStep width (ControlledArithmeticPhase.step width signed coefficient
            (validityStep width state)))))) at complete
  rw [conjunction_steps] at complete
  exact complete

/-- Inactive selection restores every actual source, pool and external work coordinate. -/
lemma step_disabled (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) (disabled : state.2.1 = false) :
    step width signed coefficient state = state := by
  simp only [step, disabled, Bool.false_eq_true, if_false, Prod.eta]

/-- All actual temporary geometry and original prefixes return, including both high branches. -/
lemma step_pool (width : Nat) (signed coefficient : Bool) (state : ControlledFrame.Data width) :
    (step width signed coefficient state).1.2 = state.1.2 := by
  unfold step
  split
  · exact ArithmeticGuard.conjunctionStep_pool width signed coefficient state.1
  · rfl

lemma step_external (width : Nat) (signed coefficient : Bool)
    (state : ControlledFrame.Data width) : (step width signed coefficient state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticConjunction

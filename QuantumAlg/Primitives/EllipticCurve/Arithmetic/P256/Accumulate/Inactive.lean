/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Inactive

/-!
# Exact inactive cancellation of actual MAC source traversals

Every multiplier-bit selected addition is identity. The actual unconditional
source doublings are retained and canceled by their same literal complete
inverse. The original source, accumulator and multiplier need no canonical
premise. The square still performs its actual original-word copy and uncopy.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

noncomputable section

open QuantumAlg.EncodedBit GateSpec Horner ModularAddition

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

-- Keep the native raw maps opaque except at the explicit projection/inverse bridges.
attribute [local irreducible] sourceDoublingStep inverseSourceDoublingStep
  Doubling.doublingStep

private def flagsAndSaved (state : OperandRegisters Saved) : (Bool × Bool) × Saved :=
  (state.1.2, state.2)

private lemma saved_of_retained {initial final : OperandRegisters Saved}
    (retained : flagsAndSaved final = flagsAndSaved initial) : final.2 = initial.2 :=
  congrArg (fun value : (Bool × Bool) × Saved => value.2) retained

private lemma latch_of_retained {initial final : OperandRegisters Saved}
    (retained : flagsAndSaved final = flagsAndSaved initial) : final.1.2.1 = initial.1.2.1 :=
  congrArg (fun value : (Bool × Bool) × Saved => value.1.1) retained

private lemma swapped_action_retained (action : Registers → Registers)
    (state : OperandRegisters Saved) :
    flagsAndSaved
        (swapOperands ((action (swapOperands state).1.1, (swapOperands state).1.2),
          (swapOperands state).2)) = flagsAndSaved state := rfl

private lemma doubling_retained (state : OperandRegisters Saved) :
    flagsAndSaved (sourceDoublingStep saved state) = flagsAndSaved state := by
  unfold sourceDoublingStep
  exact (congrArg (fun current : OperandRegisters Saved => flagsAndSaved (swapOperands current))
    (operandDoublingGates_step saved (swapOperands state))).trans
      (swapped_action_retained Doubling.doublingStep state)

private lemma iterated_retained (count : Nat) (state : OperandRegisters Saved) :
    flagsAndSaved ((sourceDoublingStep saved)^[count] state) = flagsAndSaved state := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      exact (doubling_retained saved ((sourceDoublingStep saved)^[count] state)).trans ih

private lemma doubling_inverse :
    Function.LeftInverse (inverseSourceDoublingStep saved) (sourceDoublingStep saved) := by
  intro state
  have twice (original : OperandRegisters Saved) : swapOperands (swapOperands original) =
      original := rfl
  have inverse (original : OperandRegisters Saved) :
      stepList (operandInverseDoublingGates saved)
          (stepList (operandDoublingGates saved) original) = original := by
    simp only [operandInverseDoublingGates, Doubling.inverseDoublingGates, List.map_reverse]
    exact stepList_reverse_stepList (operandDoublingGates saved) original
  rw [inverseSourceDoublingStep, sourceDoublingStep, twice, inverse, twice]

private lemma stage_inactive_state (port : MultiplierPort saved)
    (separate : (operandSavedBit saved outer).wire ≠ (operandMultiplierBit saved port).wire)
    (state : OperandRegisters Saved) (disabled : outer.get state.2 = false)
    (latchZero : state.1.2.1 = false) :
    stepList (stageGates saved port outer separate) state = state := by
  obtain ⟨⟨⟨⟨source, target⟩, reduction⟩, ⟨latch, work⟩⟩, retained⟩ := state
  change latch = false at latchZero
  subst latch
  exact Horner.stage_inactive saved outer port separate source target reduction work retained
    disabled

private lemma forwardRound_inactive (state : OperandRegisters Saved)
    (disabled : outer.get state.2 = false) (latchZero : state.1.2.1 = false)
    (index : Fin width) :
    forwardRoundStep saved multiplier outer outerMultiplier index state =
      if index.val = 0 then state else sourceDoublingStep saved state := by
  have first := stage_inactive_state saved outer (.retained (multiplier.bits index))
    (outerMultiplier index) state disabled latchZero
  have retained := doubling_retained saved state
  have savedEqual := saved_of_retained retained
  have latchEqual := latch_of_retained retained
  have next := stage_inactive_state saved outer (.retained (multiplier.bits index))
    (outerMultiplier index) (sourceDoublingStep saved state)
    ((congrArg outer.get savedEqual).trans disabled) (latchEqual.trans latchZero)
  by_cases initial : index.val = 0
  · exact (if_pos initial).trans (first.trans (if_pos initial).symm)
  · exact (if_neg initial).trans (next.trans (if_neg initial).symm)

private lemma forwardPrefix_inactive (state : OperandRegisters Saved)
    (disabled : outer.get state.2 = false) (latchZero : state.1.2.1 = false)
    (count : Nat) (within : count ≤ width) :
    UnitaryCircuit.Realizes.stepList
        ((List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)).take count) state =
      (sourceDoublingStep saved)^[count - 1] state := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let steps := List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)
      have bounded : count < width := by omega
      have listBound : count < steps.length := by
        simpa only [steps, List.length_ofFn] using bounded
      have previous := ih (by omega)
      have selected : steps.get ⟨count, listBound⟩ =
          forwardRoundStep saved multiplier outer outerMultiplier ⟨count, bounded⟩ := by
        simp only [steps, List.get_ofFn, Fin.cast_mk]
      let current := (sourceDoublingStep saved)^[count - 1] state
      have preserved := iterated_retained saved (count - 1) state
      have off : outer.get current.2 = false :=
        (congrArg outer.get (saved_of_retained preserved)).trans disabled
      have clean : current.1.2.1 = false :=
        (latch_of_retained preserved).trans latchZero
      have round := forwardRound_inactive saved multiplier outer outerMultiplier current off clean
        ⟨count, bounded⟩
      have last : (if count = 0 then current else sourceDoublingStep saved current) =
          (sourceDoublingStep saved)^[count + 1 - 1] state := by
        by_cases initial : count = 0
        · subst count
          rfl
        · rw [if_neg initial]
          have next : count - 1 + 1 = count + 1 - 1 := by omega
          exact (Function.iterate_succ_apply' (sourceDoublingStep saved) (count - 1)
            state).symm.trans
            (congrArg (fun index => (sourceDoublingStep saved)^[index] state) next)
      have actual := UnitaryCircuit.Realizes.stepList_take_succ steps count listBound state
      exact actual.trans ((congrArg (steps.get ⟨count, listBound⟩) previous).trans
        ((congrFun selected _).trans (round.trans last)))

/-- Disabled MAC retains arbitrary words and work using the real complete inverse traversal. -/
lemma fullStep_inactive (state : OperandRegisters Saved) (disabled : outer.get state.2 = false)
    (latchZero : state.1.2.1 = false) :
    fullStep saved multiplier outer outerMultiplier state = state := by
  have prefixActual := forwardPrefix_inactive saved multiplier outer outerMultiplier state disabled
    latchZero width le_rfl
  have complete : (List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier)).take width =
      List.ofFn (forwardRoundStep saved multiplier outer outerMultiplier) :=
    List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  have forward : forwardStep saved multiplier outer outerMultiplier state =
      (sourceDoublingStep saved)^[width - 1] state :=
    (congrArg (fun steps => UnitaryCircuit.Realizes.stepList steps state) complete).symm.trans
      prefixActual
  exact (congrArg ((inverseSourceDoublingStep saved)^[width - 1]) forward).trans
    ((doubling_inverse saved).iterate (width - 1) state)

lemma program_inactive (environment : OracleModel.empty.Interpretation)
    (state : OperandRegisters Saved) (disabled : outer.get state.2 = false)
    (latchZero : state.1.2.1 = false) :
    (program saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode state)) :=
  ((realizes saved multiplier outer outerMultiplier environment).apply_encoded_ket state).trans
    (congrArg (fun label => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((operandEncoding saved).encode label)))
        (fullStep_inactive saved multiplier outer outerMultiplier state disabled latchZero))

namespace Inverse

lemma program_inactive (environment : OracleModel.empty.Interpretation)
    (state : OperandRegisters Saved) (disabled : outer.get state.2 = false)
    (latchZero : state.1.2.1 = false) :
    (program saved multiplier outer outerMultiplier).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding saved).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding saved).encode state)) := by
  let initial := NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((operandEncoding saved).encode state))
  have forward := Accumulate.program_inactive saved multiplier outer outerMultiplier environment
    state disabled latchZero
  have canceled := UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
    (Accumulate.program saved multiplier outer outerMultiplier)
    (program saved multiplier outer outerMultiplier)
    (matrix_inverse saved multiplier outer outerMultiplier environment) initial
  exact (congrArg ((program saved multiplier outer outerMultiplier).applyNormalized environment)
    forward).symm.trans canceled

end Inverse

namespace Square

variable {Rest : Type} (rest : BinaryLabelEncoding Rest) (selector : EncodedBit rest)

/-- Both actual copies execute and cancel around a disabled MAC on arbitrary original words. -/
lemma program_inactive (environment : OracleModel.empty.Interpretation) (source target : Word)
    (retained : Rest) (disabled : selector.get retained = false) :
    (program rest selector).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((operandEncoding (savedEncoding rest)).encode
            ((((source, target), false), (false, false)), (zeroWord, retained))))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((operandEncoding (savedEncoding rest)).encode
          ((((source, target), false), (false, false)), (zeroWord, retained)))) := by
  let ket := fun state => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
    ((operandEncoding (savedEncoding rest)).encode state))
  have copied : (copyProgram rest).applyNormalized environment
      (ket ((((source, target), false), (false, false)), (zeroWord, retained))) =
        ket ((((source, target), false), (false, false)), (source, retained)) :=
    ((copy_realizes rest environment).apply_encoded_ket _).trans
      (congrArg ket (copy_clean rest _ retained))
  have inactive := Inverse.program_inactive (savedEncoding rest) (Square.multiplier rest)
    (outerBit rest selector) (outer_multiplier_ne rest selector) environment
    ((((source, target), false), (false, false)), (source, retained)) disabled rfl
  have cleared : (uncopyProgram rest).applyNormalized environment
      (ket ((((source, target), false), (false, false)), (source, retained))) =
        ket ((((source, target), false), (false, false)), (zeroWord, retained)) :=
    ((uncopy_realizes rest environment).apply_encoded_ket _).trans
      (congrArg ket (uncopy_clean rest _ retained))
  exact UnitaryCircuit.applyNormalized_seq_of_eq copied
    (UnitaryCircuit.applyNormalized_seq_of_eq inactive cleared)

end Square

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate

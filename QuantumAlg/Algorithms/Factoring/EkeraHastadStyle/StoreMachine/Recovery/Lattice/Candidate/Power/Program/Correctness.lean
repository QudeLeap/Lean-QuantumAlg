/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Program

/-!
# Original modular-power predicate from actual candidate execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

open Execution
open ClassicalAlgorithms.Modular
open ClassicalRoutines.Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- The original modular result, target predicate, modulus and full caller frame. -/
structure Outcome (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth)
    (input : Pow.Input spec exponentWidth) (target : Residue spec)
    (before after : Store ctx) : Prop where
  modulus : (after.read refs.modulus).toNat = spec.modulus
  power : (after.read (writeInput refs.power)).toNat =
    input.base.val ^ input.exponent.val % spec.modulus
  accepted : (after.read (writeInput refs.accepted)).toBool =
    decide (input.base.val ^ input.exponent.val % spec.modulus = target.val)
  callerFrame : CallerFrame refs before after

/-- Only the original power and comparison destinations can change in the returned caller store. -/
theorem candidatePowerInto_callerFrame (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (store : Store ctx) :
    CallerFrame refs store (candidateStep spec refs store).1 := by
  intro shape other avoidsPower avoidsAccepted
  change ((powerStep spec refs store).1.applyOp (equalityOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsAccepted]
  exact nativePower_into_read_other spec refs.generator refs.exponent refs.power store
    other avoidsPower

omit [BitWord.Selected model] in
/-- Original canonical base representation supplies the shared actual power's exact input. -/
theorem power_inputRepresents (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth)
    (store : Store ctx) (input : Pow.Input spec exponentWidth) (target : Residue spec)
    (initial : InitialConditions spec store refs input target) :
    InputRepresents spec refs.generator refs.exponent store input := by
  refine ⟨?_, initial.exponentValue⟩
  have represented := initial.baseRepresents
  generalize store.read refs.generator = encoded at represented ⊢
  cases encoded with
  | canonicalResidue word =>
      apply congrArg CShape.Value.canonicalResidue
      exact Fin.ext represented

/-- Actual source exponentiation and actual target read determine the original acceptance bit. -/
theorem candidatePowerInto_correct (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (separation : Separation refs) (store : Store ctx)
    (input : Pow.Input spec exponentWidth) (target : Residue spec)
    (initial : InitialConditions spec store refs input target) :
    Outcome spec refs input target store (candidateStep spec refs store).1 := by
  have powered := nativePower_into_toNat spec refs.generator refs.exponent refs.power store input
    (power_inputRepresents spec refs store input target initial)
  have targetFrame := nativePower_into_read_other spec refs.generator refs.exponent refs.power
    store refs.targetPower separation.targetPowerAvoidsPower
  have callerFrame : CallerFrame refs store (candidateStep spec refs store).1 :=
    candidatePowerInto_callerFrame spec refs store
  refine ⟨?_, ?_, ?_, callerFrame⟩
  · rw [callerFrame refs.modulus separation.modulusAvoidsPower separation.modulusAvoidsAccepted]
    exact initial.modulusRepresents
  · change (((powerStep spec refs store).1.applyOp (equalityOp refs)).read
      (writeInput refs.power)).toNat = _
    rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ separation.powerAvoidsAccepted]
    exact powered
  · change (((powerStep spec refs store).1.applyOp (equalityOp refs)).read
      (.storage (equalityOp refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change decide (((intoStep spec refs.generator refs.exponent refs.power store).1.read
      (wordRead refs.power)).toNat =
      ((intoStep spec refs.generator refs.exponent refs.power store).1.read
        refs.targetPower).toNat) = _
    rw [powered, targetFrame, initial.targetRepresents]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

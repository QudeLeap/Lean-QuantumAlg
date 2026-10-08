/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure

/-!
# Checked-recovery contraction with a named candidate effect family

An algorithm may prove its source floor for a separately named actual event.
Pointwise equality with the checker's accepted-candidate event transports
that floor without elaborating the algorithm circuit inside the generic
failure-contraction proof.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

/-- A pointwise identified candidate effect family supplies the same actual
failure contraction as the checker's original accepted-candidate event. -/
theorem sampledAttempt_failure_weight_le_of_effects
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < (((underPersistent sampleCode supported width scalarWidth).execute
      Reference state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ)
    (effects : Circuit.EffectFamily (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState ×
        (H × (underPersistent sampleCode supported width scalarWidth).Path)))
    (agrees : ∀ entry, effects entry =
      if SampleAccepted curve modulus basePoint targetPoint
          (entry.1.read (persistentInput width scalarWidth sample)) then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
    (bound :
      let rejected := state.selectClassical (fun entry => (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool) false
      rejected.mass * lower ≤
        ((underPersistent sampleCode supported width scalarWidth).execute
          Reference rejected).effectWeight effects) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((sampledAttempt sampleCode supported curve modulus sample base target).execute
        Reference state) ≤ (1 - lower) *
          persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
            state := by
  apply sampledAttempt_failure_weight_le sampleCode supported curve modulus sample base target
    basePoint targetPoint state represents lower
  exact bound.trans_eq (by
    congr 1
    funext entry
    exact agrees entry)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

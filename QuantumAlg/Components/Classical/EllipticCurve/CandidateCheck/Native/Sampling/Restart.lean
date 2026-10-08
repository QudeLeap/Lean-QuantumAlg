/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Semantics
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Deterministic
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical cleanup includes the actual complete checked attempt

The physical sampler is lifted beside all seven existing recovery cells.
The same complete native recovery, curve check and first-success feedback
then runs on those real cells. Its proved deterministic full-state equation
preserves every record's fixed quantum seed. This certificate includes the
feedback and does not grant a sampling-only completed-cycle cut.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The original fixed seed survives the complete real checked attempt after physical sampling. -/
theorem sampledAttempt_reinitializedAt
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt sampleCode seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (sampledAttempt sampleCode supported curve modulus sample base target)
      seed := by
  obtain ⟨record, equation, _⟩ := attemptInto_actualRecord curve modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  exact Circuit.RestartCleanup.followedByMapAt
    (underPersistent sampleCode supported width scalarWidth)
    (persistentAttempt curve modulus sample base target) seed
    (underPersistent_reinitializedAt sampleCode supported width scalarWidth seed fixed noBorrowed)
    record equation

/-- Both physical reset and complete real recovery/feedback belong to the restartable section. -/
theorem sampledAttempt_restartCleanup
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (cleanup : Circuit.RestartCleanup sampleCode) (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup
      (sampledAttempt sampleCode supported curve modulus sample base target) := by
  obtain ⟨record, equation, _⟩ := attemptInto_actualRecord curve modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  apply Circuit.RestartCleanup.followedByMap
    (underPersistent sampleCode supported width scalarWidth)
    (persistentAttempt curve modulus sample base target)
    (underPersistent_restartCleanup sampleCode supported width scalarWidth cleanup noBorrowed)
    record equation
  intro Reference History _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (persistentAttempt curve modulus sample base target)
    ((persistentCtx_borrowedQuantumWires ctx width scalarWidth).trans noBorrowed) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

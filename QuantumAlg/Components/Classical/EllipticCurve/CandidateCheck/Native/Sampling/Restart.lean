/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Semantics
import all QuantumAlg.Core.Execution.Restart.Deterministic
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding.Restart

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

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The original fixed seed survives the complete real checked attempt after physical sampling. -/
lemma sampledAttempt_reinitializedAt
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt sampleCode environment seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (sampledAttempt sampleCode curve modulus sample base target) environment
      seed := by
  obtain ⟨record, equation, _⟩ := attemptInto_actualRecord (environment := environment) curve
    modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  exact Circuit.RestartCleanup.followedByMapAt (environment := environment)
    (sampleUnderPersistent sampleCode width scalarWidth)
    (persistentAttempt curve modulus sample base target) seed
    (candidateCheck_sampleUnderPersistent_reinitializedAt
      sampleCode width scalarWidth seed fixed noBorrowed)
    record equation

/-- Both physical reset and complete real recovery/feedback belong to the restartable section. -/
lemma sampledAttempt_restartCleanup
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (cleanup : Circuit.RestartCleanup sampleCode environment) (noBorrowed :
      ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup
      (sampledAttempt sampleCode curve modulus sample base target) environment := by
  obtain ⟨record, equation, _⟩ := attemptInto_actualRecord (environment := environment) curve
    modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  apply Circuit.RestartCleanup.followedByMap (environment := environment)
    (sampleUnderPersistent sampleCode width scalarWidth)
    (persistentAttempt curve modulus sample base target)
    (candidateCheck_sampleUnderPersistent_restartCleanup
      sampleCode width scalarWidth cleanup noBorrowed)
    record equation
  intro Reference History _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (persistentAttempt curve modulus sample base target)
    environment ((persistentCtx_borrowedQuantumWires ctx width scalarWidth).trans noBorrowed)
    Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model.Bounds

/-!
# Range preservation for the actual seven-port nearest checker

The selector either retains its previous bounded word or stores the actual
nearest decoder's bounded candidate. This statement is independent of point
representations, sampling probabilities and the context allocation strategy.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Every actual selector branch retains a word below the same subgroup modulus. -/
lemma attemptStore_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) (hidden : model.HiddenState)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key, accepted.key, selected.key].Nodup)
    (prior : (before.read (.storage selected.toCStorageRef)).toNat < modulus.modulus) :
    ((attemptStore (environment := environment) curve modulus sample base target inverseSuccess
      candidate reconstruction scalarResult targetAccepted accepted selected (before, hidden)).read
        (.storage selected.toCStorageRef)).toNat < modulus.modulus := by
  have latches := attempt_latches (environment := environment)
    curve modulus sample base target inverseSuccess candidate reconstruction scalarResult
    targetAccepted accepted selected before hidden distinct
  dsimp only at latches
  rw [latches.2]
  split
  · exact FiniteCyclicDLP.RawRecovery.Nearest.outputCells_candidate_lt modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
  · exact prior

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

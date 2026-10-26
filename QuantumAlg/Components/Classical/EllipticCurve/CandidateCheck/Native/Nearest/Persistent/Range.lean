/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model.Bounds

/-!
# Paid nearest recovery through actual candidate verification and first-success selection

The existing native verifier and selector consume the actual nearest decoder's
three exposed cells.  All chronological stores, path records, caller reads,
Reference matrices and prior History labels remain part of the same execution.
The generic truncated-range decoder and its existing consumers are unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- Every actual selector branch preserves the original modulus bound of the selected word. -/
lemma persistentAttemptStore_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (prior : (before.1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus) :
    ((persistentAttemptStore (environment := environment) curve modulus sample base target
      before).read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus := by
  have latches := attempt_latches (environment := environment)
    curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth) before.1 before.2
      (attemptKeys_distinct ctx width scalarWidth)
  dsimp only at latches
  rw [persistentAttemptStore_eq]
  rw [latches.2]
  split
  · exact FiniteCyclicDLP.RawRecovery.Nearest.outputCells_candidate_lt modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput
        (before.1.read (persistentInput width scalarWidth sample)))
  · exact prior

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

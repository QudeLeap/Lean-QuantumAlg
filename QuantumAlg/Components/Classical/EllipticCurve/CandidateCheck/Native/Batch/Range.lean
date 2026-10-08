/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model.Bounds

/-!
# Selected-word range through the actual recovery loop

The real Boolean selector either keeps the previous selected word or copies
the original raw candidate. The latter is below the original modulus on both
raw-recovery branches. Actual fresh allocation initializes the selected word
to zero, so its final range requires no caller range or initialization premise.
This argument is independent of point representations and candidate acceptance.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- Every actual selector branch preserves the original modulus bound of the selected word. -/
theorem persistentAttemptStore_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (prior : (before.1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus) :
    ((persistentAttemptStore curve modulus sample base target before).read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus := by
  have latches := attempt_latches curve modulus (persistentInput width scalarWidth sample)
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
  · exact FiniteCyclicDLP.RawRecovery.outputCells_candidate_lt modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput
        (before.1.read (persistentInput width scalarWidth sample)))
  · exact prior

private theorem fold_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : List (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (prior : (before.1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus) :
    ((samples.foldl (fun current sample =>
      persistentAttemptState curve modulus sample base target current) before).1.read
        (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
          modulus.modulus := by
  induction samples generalizing before with
  | nil => exact prior
  | cons sample rest ih =>
      exact ih (persistentAttemptState curve modulus sample base target before)
        (persistentAttemptStore_selected_lt curve modulus sample base target before prior)

/-- The actual chronological loop preserves the original selected-word modulus bound. -/
theorem repeatedAttemptsStore_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (prior : (before.1.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus) :
    ((repeatedAttemptsStore curve modulus samples base target before).read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus := by
  rw [repeatedAttemptsStore_fold]
  exact fold_selected_lt curve modulus (List.ofFn samples) base target before prior

/-- Actual fresh initialization supplies the selected-word bound without a caller promise. -/
theorem repeatedAttemptsStore_initial_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx)
    (hidden : model.HiddenState) :
    ((repeatedAttemptsStore curve modulus samples base target
      (persistentInitialStore width scalarWidth before, hidden)).read
        (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
          modulus.modulus := by
  apply repeatedAttemptsStore_selected_lt
  have initial : (persistentInitialStore width scalarWidth before).read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        CShape.initialValue (.unsignedWord scalarWidth) :=
    persistentInitialStore_selected width scalarWidth before
  rw [initial]
  change 0 % 2 ^ scalarWidth < modulus.modulus
  rw [Nat.zero_mod]
  exact lt_of_lt_of_le (by decide : 0 < 2) modulus.two_le

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

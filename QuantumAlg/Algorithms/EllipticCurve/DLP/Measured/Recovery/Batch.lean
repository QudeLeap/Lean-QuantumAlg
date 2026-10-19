/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Candidate
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Range
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing

/-!
# Original secret in the actual initialized recovery batch

The actual fresh allocation, chronological sample loop and final option-pack
store update retain the original candidate-check condition. Every accepted
selection is internally bounded by the subgroup order and satisfies the
original public point equation, so it is the unique original secret. The
secret is solely a proof witness; original public point values remain the
only mathematical input interpretation needed at this component boundary.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private lemma packOption_wordOfNat_iff (width value : Nat)
    (flag : CShape.Value .bit) (selected : CShape.Value (.unsignedWord width))
    (sound : flag.toBool = true → selected.toNat = value) :
    CShape.packOption (.product flag selected) =
        .optionSome (CShape.wordOfNat width value) ↔ flag.toBool = true := by
  cases flag with
  | bit flag =>
      cases flag
      · rw [CShape.packOption_false]
        constructor <;> intro impossible <;> cases impossible
      · have word : selected = CShape.wordOfNat width value := by
          cases selected with
          | unsignedWord selected =>
              apply congrArg CShape.Value.unsignedWord
              apply Fin.ext
              change selected.val = value % 2 ^ width
              have decoded : selected.val = value := sound rfl
              rw [← decoded, Nat.mod_eq_of_lt selected.isLt]
        rw [CShape.packOption_true, word]
        exact iff_of_true rfl rfl

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {count : Nat}

variable (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2)))
    (base target : CInputRef ctx (PointShape (Canonical.Layout.fieldWidth E)))
    (before : Store ctx) (hidden : model.HiddenState)
    (baseRep : PointRepresents (Canonical.Layout.curveSpec E)
      (before.read base) problem.generator.toMathlib)
    (targetRep : PointRepresents (Canonical.Layout.curveSpec E)
      (before.read target) problem.target.toMathlib)

include baseRep targetRep

/-- Actual accepted selection is the original secret, with its range derived inside the loop. -/
lemma repeatedRecovery_selected_secret
    (accepted : ((repeatedAttemptsStore (environment := environment)
      (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) samples base target
      (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem)
        before, hidden)).read
        (.storage (persistentAccepted ctx (Canonical.Layout.fieldWidth E)
          (orderWidth problem)).toCStorageRef)).toBool = true) :
    ((repeatedAttemptsStore (environment := environment)
      (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) samples base target
      (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem)
        before, hidden)).read
        (.storage (persistentSelected ctx (Canonical.Layout.fieldWidth E)
          (orderWidth problem)).toCStorageRef)).toNat = input.secret.val := by
  have bounded := repeatedAttemptsStore_initial_selected_lt (environment := environment)
      (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target before hidden
  apply (bounded_groupScalar_eq_target_iff problem input _ bounded).mp
  apply repeatedAttemptsStore_preserves_soundness (environment := environment)
      (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
    (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem) before, hidden)
    problem.generator.toMathlib problem.target.toMathlib
  · rw [persistentInitialStore_read]
    exact baseRep
  · rw [persistentInitialStore_read]
    exact targetRep
  · intro impossible
    have initialized := persistentInitialStore_accepted (Canonical.Layout.fieldWidth E)
      (orderWidth problem) before
    change (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem) before).read
      (.storage (persistentAccepted ctx (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).toCStorageRef) = CShape.Value.bit false at initialized
    rw [initialized] at impossible
    cases impossible
  · exact accepted

/-- The real final pack returns the secret exactly when an original sample passes checking. -/
lemma packedRecovery_secret_iff :
    let after := repeatedAttemptsStore (environment := environment)
      (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) samples base target
      (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem) before, hidden)
    (packBatchResultStep ctx (Canonical.Layout.fieldWidth E) (orderWidth problem) after).1.read
      (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
        .optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val) ↔
      ∃ index, SampleAccepted (Canonical.Layout.curveSpec E)
        (recoveryModulusSpec problem nontrivial) problem.generator.toMathlib
        problem.target.toMathlib (before.read (samples index)) := by
  let after := repeatedAttemptsStore (environment := environment)
      (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
    (persistentInitialStore (Canonical.Layout.fieldWidth E) (orderWidth problem) before, hidden)
  have eligible := repeatedAttemptsStore_initial_accepts_iff (environment := environment)
      (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target before hidden
    problem.generator.toMathlib problem.target.toMathlib baseRep targetRep
  change (packBatchResultStep ctx (Canonical.Layout.fieldWidth E) (orderWidth problem) after).1.read
    (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) = _ ↔ _
  rw [packBatchResultStep_output]
  apply (packOption_wordOfNat_iff (orderWidth problem) input.secret.val _ _ ?_).trans eligible
  intro accepted
  exact repeatedRecovery_selected_secret problem nontrivial input samples
    base target before hidden baseRep targetRep accepted

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

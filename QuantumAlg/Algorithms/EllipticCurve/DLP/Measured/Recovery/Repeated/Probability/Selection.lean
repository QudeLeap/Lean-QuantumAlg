/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Candidate
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Original selected measurements in the actual persistent sample input

The same structural finite-vector read passes through the original seven
persistent cells and the original raw-input reindexing. The selected mask
therefore implies the original complete candidate condition on those same
stored values. This event inclusion adds no inverse or point-value promise;
actual public-point interpretation is supplied separately by borrowed-input
preservation when applying the checked execution theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

private theorem indicator_weight_mono {R : Register} (density : DensityOperator R)
    (first second : Prop) [Decidable first] [Decidable second] (included : first → second) :
    (if first then Effect.one R else Effect.zero R).weight density ≤
      (if second then Effect.one R else Effect.zero R).weight density := by
  by_cases selected : first
  · simp only [selected, included selected, if_true, le_refl]
  · by_cases eligible : second
    · simp only [selected, eligible, if_false, if_true, Effect.weight_one, Effect.weight_zero]
      exact density.mass_nonneg
    · simp only [selected, eligible, if_false, le_refl]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
  {kind : ProblemKind} {ctx : RuntimeCtx kind}

omit [Fact p.Prime] in
private theorem rawRecoveryInput_persistentInput (problem : KnownOrderProblem E.GroupPoint)
    (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2))) :
    persistentInput width (orderWidth problem) (rawRecoveryInput problem measured) =
      rawRecoveryInput problem (persistentInput width (orderWidth problem) measured) := rfl

/-- The actual lifted sample has the original flags and natural-scalar equation on selection. -/
theorem selectedExponentEvent_persistentSampleAccepted (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem) (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (before : Store (persistentCtx ctx width (orderWidth problem)))
    (selected : selectedExponentEvent problem input (QubitReadouts.mask
      (before.read (persistentInput width (orderWidth problem) measured))) = true) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib
      (before.read (persistentInput width (orderWidth problem)
        (rawRecoveryInput problem measured))) := by
  rw [rawRecoveryInput_persistentInput]
  exact selectedExponentEvent_sampleAccepted problem nontrivial input
    (persistentInput width (orderWidth problem) measured) before selected

/-- Selected measurement mass is contained in the same original stored-candidate event. -/
theorem selectedPersistentSample_weight_le (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem) (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width (orderWidth problem)) Reference History) :
    state.effectWeight (fun record => if selectedExponentEvent problem input (QubitReadouts.mask
      (record.1.read (persistentInput width (orderWidth problem) measured))) = true then
        Effect.one ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)) ≤
      state.effectWeight (fun record =>
        if SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
            problem.generator.toMathlib problem.target.toMathlib
            (record.1.read (persistentInput width (orderWidth problem)
              (rawRecoveryInput problem measured))) then
          Effect.one ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)
        else Effect.zero
          ((persistentCtx ctx width (orderWidth problem)).register.prod Reference)) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro record _
  exact indicator_weight_mono (state.block record) _ _
    (selectedExponentEvent_persistentSampleAccepted problem nontrivial input width measured
      record.1)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

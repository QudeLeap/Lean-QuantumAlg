/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Execution
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Selected exponent mass reaches the actual checked batch result

The actual allocation, complete attempt loop and final option pack transfer
every original selected exponent event to the original secret output. The
public point interpretation is required only on positive-mass input blocks.
No condition is imposed on impossible classical records, and every quantum
reference block and previous history remains part of the actual execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}

/-- The original secret encoded in the actual final checked optional-word output. -/
def checkedSecretOutput (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem) :
    CShape.Value (.option (.unsignedWord (orderWidth problem))) :=
  .optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)

/-- Any original selected event contributes to the actual complete batch's secret result. -/
theorem recoveryTail_selected_weight_le (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : Fin count → CInputRef ctx
      (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (base target : CInputRef ctx (PointShape (Canonical.Layout.fieldWidth E)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read base) problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read target) problem.target.toMathlib) :
    state.effectWeight (fun entry =>
      if ∃ index, selectedExponentEvent problem input
          (QubitReadouts.mask (entry.1.read (measured index))) = true then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) ≤
      ((recoveryTail (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
        (fun index => rawRecoveryInput problem (measured index)) base target).execute
          Reference state).effectWeight (fun entry =>
        if entry.1.read (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
          Effect.one (Register.prod
            (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
            Reference)
        else Effect.zero (Register.prod
          (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
          Reference)) := by
  let samples := fun index => rawRecoveryInput problem (measured index)
  obtain ⟨record, equation, correct⟩ := recoveryTail_actualRecord (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
  rw [equation Reference state]
  unfold recoveryTailRecordState
  change _ ≤ (ExecutionState.mapClassical state
    (fun entry => ((record entry.1).1, entry.2, (record entry.1).2))).effectWeight
      (fun entry => if entry.1.read
          (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference))
  rw [ExecutionState.effectWeight_mapClassical_decision]
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro entry _present
  by_cases positive : 0 < (state.block entry).mass
  · by_cases selected : ∃ index, selectedExponentEvent problem input
        (QubitReadouts.mask (entry.1.read (measured index))) = true
    · obtain ⟨baseRep, targetRep⟩ := represents entry positive
      obtain ⟨index, event⟩ := selected
      have eligible := selectedExponentEvent_sampleAccepted problem nontrivial input
        (measured index) entry.1 event
      have written : (record entry.1).1.read
          (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input := by
        rw [correct entry.1]
        exact (packedRecovery_secret_iff problem nontrivial input samples base target
          entry.1 baseRep targetRep).mpr ⟨index, eligible⟩
      simp only [written, if_true]
      simp only [show (∃ index, selectedExponentEvent problem input
        (QubitReadouts.mask (entry.1.read (measured index))) = true) from ⟨index, event⟩,
        if_true, le_refl]
    · simp only [selected, if_false, Effect.weight_zero]
      split_ifs
      · simpa only [Effect.weight_one] using (state.block entry).mass_nonneg
      · simp only [Effect.weight_zero, le_refl]
  · have zeroMass := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    dsimp only
    split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero, zeroMass, le_refl]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

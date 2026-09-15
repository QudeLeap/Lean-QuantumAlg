/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Recovery.Execution
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Selected event weight survives actual raw recovery

The real deterministic classical suffix maps each complete state block to
its actual final store and path. Every original selected exponent outcome
produces the secret with a true reconstruction flag. Summing those same
nonnegative blocks transfers its event weight to the actual recovered output,
including arbitrary external reference, mixed input, old history and zero mass.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution FiniteCyclicDLP Canonical.Probability

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
    {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The original selected-event mass is retained in the actual recovered-secret output event. -/
theorem rawRecoveryIntoResult_selected_eventWeight_le
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (result : CWriteRef ctx
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape (orderWidth problem)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    state.effectWeight (fun entry =>
      if selectedExponentEvent problem input
          (QubitReadouts.mask (entry.1.read measured)) = true then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) ≤
      ((rawRecoveryIntoResult problem nontrivial measured result).execute
        Reference state).effectWeight
        (fun entry => if entry.1.read (.storage result.toCStorageRef) =
            .optionSome (.product (CShape.wordOfNat (orderWidth problem) input.secret.val)
              (.bit true)) then Effect.one (Register.prod ctx.register Reference)
          else Effect.zero (Register.prod ctx.register Reference)) := by
  obtain ⟨record, equation, correct⟩ :=
    rawRecoveryIntoResult_selected_actualRecord problem nontrivial input measured result
  rw [equation Reference state, ExecutionState.effectWeight_mapClassical_decision]
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro entry _present
  by_cases selected :
      selectedExponentEvent problem input (QubitReadouts.mask (entry.1.read measured)) = true
  · have written : (record entry.1).1.read (.storage result.toCStorageRef) =
        .optionSome (.product (CShape.wordOfNat (orderWidth problem) input.secret.val)
          (.bit true)) := by
      rw [correct entry.1 selected, Store.read_write_same]
    simp only [selected, written, if_true, le_refl]
  · simp only [selected, Bool.false_eq_true, if_false, Effect.weight_zero]
    split_ifs
    · simpa only [Effect.weight_one] using (state.block entry).mass_nonneg
    · simp only [Effect.weight_zero, le_refl]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

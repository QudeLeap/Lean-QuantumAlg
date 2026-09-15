/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Recovery
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Semantics

/-!
# Actual raw recovery from selected measured exponent values

The existing finite measurement vector is read in exactly its original
order. Its actual preparation and shared checked inverse compute the
original optional candidate. The selected event already proved for the
original exponent run therefore implies an actual stored secret and true
reconstruction flag. The executable circuit receives no semantic secret,
selected-event promise, supplied inverse or prepared scratch state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
    {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Structural reindexing preserves every actual finite measurement value and its bit order. -/
def rawRecoveryInput (problem : KnownOrderProblem E.GroupPoint)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2))) :
    CInputRef ctx (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2)) :=
  .fixedVector fun index => .vectorGet measured (Fin.cast (by omega) index)

/-- The actual decoder input is exactly the original raw exponent mask at every bit. -/
theorem preparationInput_rawRecoveryInput (problem : KnownOrderProblem E.GroupPoint)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (store : Store ctx) :
    preparationInput (store.read (rawRecoveryInput problem measured)) =
      rawExponentInput problem (QubitReadouts.mask (store.read measured)) := rfl

/-- Actual recovery reads measured values and writes the original optional shape. -/
def rawRecoveryIntoResult (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (result : CWriteRef ctx
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape (orderWidth problem))) :
    Circuit ctx ctx :=
  singleIntoResult (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) result

/-- The same complete execution record stores the secret on every original selected measurement. -/
theorem rawRecoveryIntoResult_selected_actualRecord (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (result : CWriteRef ctx
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape (orderWidth problem))) :
    ∃ record : Store ctx → Store ctx ×
        (rawRecoveryIntoResult problem nontrivial measured result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (rawRecoveryIntoResult problem nontrivial measured result).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        selectedExponentEvent problem input (QubitReadouts.mask (before.read measured)) = true →
          (record before).1 = before.write result
            (.optionSome (.product (CShape.wordOfNat (orderWidth problem) input.secret.val)
              (.bit true))) := by
  obtain ⟨record, equation, correct⟩ := singleIntoResult_actualRecord
    (recoveryModulusSpec problem nontrivial) (rawRecoveryInput problem measured) result
  refine ⟨record, equation, ?_⟩
  intro before selected
  obtain ⟨output, recovered, candidate, verified⟩ :=
    outputOf_selectedExponentEvent_recovers problem input
      (QubitReadouts.mask (before.read measured)) selected
      (recoveryModulusSpec problem nontrivial) rfl
  rw [correct before, preparationInput_rawRecoveryInput, recovered]
  change before.write result
    (.optionSome (.product (CShape.wordOfNat (orderWidth problem) output.candidate.val)
      (.bit output.verified))) = _
  rw [candidate, verified]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Sequence
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Selection.Mass
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure

/-!
# Reused ECC section reset preserves the checked failure mass

The trailing physical reset runs beside the seven retained classical cells.
It leaves the actual accepted bit untouched while changing the quantum bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ)
  (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)

/-- The actual trailing reset preserves exactly the subnormalized mass of
unaccepted records, with arbitrary prior history and external reference. -/
theorem persistentSamplingReset_failureWeight
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H)) :
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      ((persistentSamplingReset E fieldTail sameWidth fits problem seed).execute
        Reference state) =
    persistentFailureWeight (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := PublicInput.terminal E (orderWidth problem))
      (width := Canonical.Layout.fieldWidth E) (scalarWidth := orderWidth problem)
      state := by
  let raw := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selected := BitWord.selectForCircuit raw
  have localReset : selected.IsLocal := BitWord.selectForCircuit_isLocal raw
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  have retained := underPersistent_acceptance_mass selected localReset
    (Canonical.Layout.fieldWidth E) (orderWidth problem) state false
  have sameCode :
      persistentSamplingReset E fieldTail sameWidth fits problem seed =
        underPersistent selected localReset (Canonical.Layout.fieldWidth E)
          (orderWidth problem) := rfl
  rw [sameCode]
  unfold persistentFailureWeight
  exact retained

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

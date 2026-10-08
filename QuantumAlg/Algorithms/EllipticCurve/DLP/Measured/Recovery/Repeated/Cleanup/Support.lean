/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Sequence
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Physical reset facts at the actual persistent sampling boundary

The original reset runs inside the selected bit/word language and beside the
seven existing recovery cells. Its complete physical restart certificate
includes the fixed-seed law on every output block and complete history.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ)
  (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)

/-- The original sampling label, viewed on the unchanged quantum layout
beside all seven persistent classical recovery cells. -/
def persistentSamplingSeed :
    (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)).quantumLayout.SelectedBasis
        (persistentCtx (PublicInput.terminal E (orderWidth problem))
          (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedSelectionᶜ :=
  (PublicInput.terminal E (orderWidth problem)).quantumLayout.restrictSelectedBasis
    (PublicInput.terminal E (orderWidth problem)).borrowedSelectionᶜ
    (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed)

/-- The actual persistent reset retains the original complete sampling label
beside all seven checked-recovery cells, for every physical output record. -/
theorem persistentSamplingReset_reinitializedAt :
    Circuit.ReinitializedAt
      (persistentSamplingReset E fieldTail sameWidth fits problem seed)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) := by
  let code := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : code.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  exact underPersistent_reinitializedAt code supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem) _
    (samplingReset_selected_reinitializedAt E fieldTail (orderWidth problem)
      sameWidth fits seed)
    (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))

/-- The actual persistent sampling reset measures and restores the same fixed
owned quantum seed on every complete output record. -/
theorem persistentSamplingReset_restartCleanup :
    Circuit.RestartCleanup
      (persistentSamplingReset E fieldTail sameWidth fits problem seed) := by
  let code := BitWord.selectForCircuit
    (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed)
  have supported : code.IsLocal := BitWord.selectForCircuit_isLocal _
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  have original : Circuit.RestartCleanup code :=
    samplingReset_selected_restartCleanup E fieldTail (orderWidth problem)
      sameWidth fits seed
  exact underPersistent_restartCleanup code supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem) original
    (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))

/-- Every actual persistent reset path still contains the original physical measurement. -/
theorem persistentSamplingReset_measured :
    ContainsMeasurement
      (persistentSamplingReset E fieldTail sameWidth fits problem seed) := by
  exact (persistentSamplingReset_restartCleanup E fieldTail sameWidth fits
    problem seed).measured

/-- The same executed persistent reset restores every borrowed classical and
quantum observation jointly with an arbitrary external reference. -/
theorem persistentSamplingReset_restores (Reference : Register)
    {H : Type} [Fintype H]
    (state : State
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
      ((.quantum AlgorithmGate.model .empty BitWord.model : ExecutionModel).HiddenState × H)) :
    (persistentSamplingReset E fieldTail sameWidth fits problem seed).BorrowedRestored
      Reference state
      ((persistentSamplingReset E fieldTail sameWidth fits problem seed).execute
        Reference state) := by
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  change reset.BorrowedRestored Reference state (reset.execute Reference state)
  exact (persistentSamplingReset_restartCleanup E fieldTail sameWidth fits
    problem seed).restores Reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

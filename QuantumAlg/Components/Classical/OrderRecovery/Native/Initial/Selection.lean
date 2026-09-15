/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.FiniteSelection
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor.Representation

/-!
# Source selection from genuine initialized recovery storage

The complete fixed-fuel scan starts from its actual field allocations and
initialization. The physical layout proves separation, and the original
dyadic continued-fraction theorem supplies the fuel bound. Thus only the
original stored source input is required; no cursor, fitting, or initialization
certificate is delegated to an endpoint caller.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.OrderRecovery

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- Genuine initialization and the actual finite scan produce the source selection. -/
theorem nativeRecovery_scan_selection
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (baseValue : store.read base = .canonicalResidue input.base)
    (sampleValue : store.read sample = .bits input.terminalBits) :
    observedCandidate (recoveryCells ctx modulusWidth (phaseBits + 1))
      ((fun initial => (scanSlotStep spec.modulusSpec
        (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
        (recoveryCells ctx modulusWidth (phaseBits + 1)) initial).1)^[finiteCandidateFuel phaseBits]
          (initializeScanStep ctx modulusWidth phaseBits sample
            (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1) =
      selection spec input := by
  have actual := nativeScan_finite_source_selection spec input
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
    (nativeRecovery_scan_separated modulusWidth (phaseBits + 1))
    (nativeRecovery_scan_input_separate modulusWidth (phaseBits + 1) base)
    (finiteCandidateFuel phaseBits)
    (initializeScanStep ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1
    (.initial (decodedIndex input).val (2 ^ phaseBits))
    (nativeRecovery_initialized_cursor spec input sample store sampleValue)
    (nativeRecovery_initialized_source_reads spec input base sample store baseValue)
    (by
      rw [initialEuclideanContinuantCandidates_eq_finiteCandidates]
      exact List.Subset.refl _)
    (initialEuclideanContinuantCandidates_length_le_finiteCandidateFuel (decodedIndex input))
  rw [initialEuclideanContinuantCandidates_eq_finiteCandidates,
    ← candidateSchedule_eq_finiteCandidates spec input,
    ← selection_eq_scanSelection spec input] at actual
  exact actual

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

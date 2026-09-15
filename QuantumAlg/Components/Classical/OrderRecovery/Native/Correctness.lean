/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initial.Selection
import all QuantumAlg.Components.Classical.OrderRecovery.Native.ResultEncoding

/-!
# Complete native recovery agrees with the original source

The result theorem reads the actual final output cell after initialization,
the genuine activity-gated finite scan, the real option write, and every
matching workspace release. Its only input equalities identify the source
values in the existing base and measured-phase cells. It covers every source
input and does not assert that every accepted sample returns the least order.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.OrderRecovery

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The actual complete scoped routine writes exactly the original source's optional word. -/
theorem nativeRecovery_into_result
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (store : Store ctx)
    (baseValue : store.read base = .canonicalResidue input.base)
    (sampleValue : store.read sample = .bits input.terminalBits) :
    (intoStep spec base sample output store).1.read (cellRead output) =
      encodeOutput (recoverUnitOrder spec input) := by
  change (scopeRecoveryStep ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody spec base sample output) (recoveryBodyStep spec base sample output) store).1.read
      (cellRead output) = _
  rw [nativeRecovery_scope_store, nativeRecovery_leave_read]
  change (((fun initial => (scanSlotStep spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1)) initial).1)^[finiteCandidateFuel phaseBits]
      (initializeScanStep ctx modulusWidth phaseBits sample
        (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1).applyOp
          (packRecoveredOp output)).read
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields (cellRead output)) = _
  exact nativeRecovery_pack_source_result spec input output _
    (nativeRecovery_scan_selection spec input base sample store baseValue sampleValue)

/-- Decoding the actual final stored option returns the original recovery result. -/
theorem nativeRecovery_into_decoded_result
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) (store : Store ctx)
    (baseValue : store.read base = .canonicalResidue input.base)
    (sampleValue : store.read sample = .bits input.terminalBits) :
    decodeOutput ((intoStep spec base sample output store).1.read (cellRead output)) =
      recoverUnitOrder spec input :=
  (congrArg decodeOutput
    (nativeRecovery_into_result spec input base sample output store baseValue sampleValue)).trans
      (nativeRecovery_decode_encode _)

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

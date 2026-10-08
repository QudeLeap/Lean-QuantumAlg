/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Geometry
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Reads

/-!
# Actual native order recovery preserves every other original structural read

All genuine scan destinations are fresh internal fields. Actual preparation
of those fields, every finite scan slot and the matching releases preserve
the original frame. Only the final nominal output write can change an
original cell. The statement applies equally to borrowed, retained and
workspace operands; it does not infer their preservation from ownership.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.OrderRecovery

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth phaseBits : Nat}

/-- The actual complete routine changes no original structural read outside its output cell. -/
theorem nativeRecovery_into_read_other (spec : Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (intoStep (model := model) spec base sample output store).1.read other = store.read other := by
  have outputFree : (packRecoveredOp (modulusWidth := modulusWidth) output).outputRef.key ∉
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields other).storageKeys := by
    change (writeUnderRecoveryFields modulusWidth (phaseBits + 1) recoveryFields output).key ∉
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields other).storageKeys
    rw [nativeRecovery_writeUnderFields_key, nativeRecovery_underFields_keys]
    exact separate
  change (scopeRecoveryStep ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)
    (recoveryBodyStep (model := model) spec base sample output) store).1.read
      other = _
  rw [nativeRecovery_scope_store, nativeRecovery_leave_read]
  change (((fun initial => (scanSlotStep (model := model) spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1)) initial).1)^[finiteCandidateFuel phaseBits]
      (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
        (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1).applyOp
          (packRecoveredOp output)).read
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields other) = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ outputFree]
  exact (nativeScan_iterate_read_other spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1)) (finiteCandidateFuel phaseBits)
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields other)
    (nativeRecovery_scan_input_separate modulusWidth (phaseBits + 1) other)
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1).trans
      (nativeRecovery_initialize_read_original modulusWidth phaseBits sample store other)

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

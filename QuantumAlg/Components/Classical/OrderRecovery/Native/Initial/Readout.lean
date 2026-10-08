/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Keys
import all QuantumAlg.Util.Classical.TerminalDecode.Padding

/-!
# Original sampled index from the actual widened decoder

The leading reference reads the fresh false accepted cell, and all remaining
references read the original measured bit string under the real recovery
allocations. The existing decoder theorem and exact leading-zero identity
therefore recover the original source index in the widened numerator cell.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The actual numerator destination is separate from every actual input bit. -/
theorem nativeRecovery_initialBit_separate (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (index : Fin (phaseBits + 1)) :
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator.key ∉
      (initialPhaseBitRefs ctx modulusWidth phaseBits sample index).storageKeys := by
  refine Fin.cases ?_ (fun tail => ?_) index
  · change (recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields 2).key ∉
      [(recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields 9).key]
    intro present
    have same := nativeRecovery_field_injective modulusWidth (phaseBits + 1) recoveryFields
      (List.mem_singleton.mp present)
    exact (by decide : (2 : Fin recoveryFields.length) ≠ 9) same
  · exact nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 2 sample

/-- The actual fresh prefix bit and original sampled bits are read with their exact values. -/
theorem nativeRecovery_initialBit_read (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (index : Fin (phaseBits + 1)) :
    ((enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store).read
      (initialPhaseBitRefs ctx modulusWidth phaseBits sample index)).toBool =
        Fin.cons (α := fun _ => Bool) false
          (fun bit => ((store.read sample).bitGet bit).toBool) index := by
  refine Fin.cases ?_ (fun tail => ?_) index
  · have initial := nativeRecovery_enter_field modulusWidth (phaseBits + 1) recoveryFields
      (9 : Fin recoveryFields.length) store
    exact congrArg CShape.Value.toBool initial
  · change (((enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store).read
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields
        sample)).bitGet tail).toBool = _
    rw [nativeRecovery_enter_read]
    rfl

/-- The existing actual decoder writes exactly the original full-register sampled index. -/
theorem nativeRecovery_decoded_numerator {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    ((TerminalDecode.foldStep (model := model)
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator
      (List.ofFn (initialPhaseBitRefs ctx modulusWidth phaseBits sample))
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator)).toNat =
      (ClassicalAlgorithms.OrderRecovery.fullRegisterIndex
        (fun bit => ((store.read sample).bitGet bit).toBool)).val := by
  have actual := TerminalDecode.terminalDecode_intoFromBitRefs_read_output
    (model := model) .bigEndian
    (initialPhaseBitRefs ctx modulusWidth phaseBits sample)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator
    (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)
    (nativeRecovery_initialBit_separate modulusWidth phaseBits sample)
  have represented : TerminalDecode.decodeInputFromBitRefs .bigEndian
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)
      (initialPhaseBitRefs ctx modulusWidth phaseBits sample) =
      ({ order := .bigEndian,
          bits := Fin.cons false (fun bit => ((store.read sample).bitGet bit).toBool) } :
        ClassicalAlgorithms.TerminalDecode.Input (phaseBits + 1)) := by
    apply congrArg (ClassicalAlgorithms.TerminalDecode.Input.mk .bigEndian)
    funext index
    exact nativeRecovery_initialBit_read modulusWidth phaseBits sample store index
  rw [represented] at actual
  have padded :=
    ClassicalAlgorithms.TerminalDecode.terminalDecode_fullRegister_zero_prefix
      (fun bit => ((store.read sample).bitGet bit).toBool)
  exact actual.trans padded

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

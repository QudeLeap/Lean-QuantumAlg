/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization

/-!
# Complete native finite order-recovery circuit

The original stored modular base and measured phase bits enter the actual
initialization and finite activity-gated scan. One final closed option-packing
instruction reads the resulting accepted/selected latches into the supplied
output cell. Every recovery workspace is then released by its matching scope;
all original quantum systems and classical entries remain live.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

variable {modulusWidth phaseBits : Nat}

/-- The actual final option encoder reads the real accepted bit and selected candidate word. -/
def packRecoveredOp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (output : CWriteRef ctx (outputShape phaseBits)) :
    ClassicalOp (.product .bit (.unsignedWord (phaseBits + 1))) (outputShape phaseBits)
      (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .packOption _
    (.product (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
      (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).selected))
    (writeUnderRecoveryFields modulusWidth (phaseBits + 1) recoveryFields output)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Complete actual initialization, finite scan and final stored-result encoding. -/
noncomputable def recoveryBody
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) :
    Circuit model (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .seq (initializeScan (model := model) ctx modulusWidth phaseBits sample)
    (.seq (scan (model := model) spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits))
      (BitWord.instruction (execution := model) (packRecoveredOp output)))

/-- Native recovery from the original stored base and phase bits into an existing option cell. -/
noncomputable def into (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) : Circuit model ctx ctx :=
  scopeRecoveryFields (model := model) ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

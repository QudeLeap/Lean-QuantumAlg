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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The actual final option encoder reads the real accepted bit and selected candidate word. -/
def packRecoveredOp (output : CWriteRef ctx (outputShape phaseBits)) :
    ClassicalOp (.product .bit (.unsignedWord (phaseBits + 1))) (outputShape phaseBits)
      (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .packOption _
    (.product (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
      (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).selected))
    (writeUnderRecoveryFields modulusWidth (phaseBits + 1) recoveryFields output)

/-- Complete actual initialization, finite scan and final stored-result encoding. -/
def recoveryBody (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) :
    Circuit (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .seq (initializeScan ctx modulusWidth phaseBits sample)
    (.seq (scan spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits))
      (.classical (packRecoveredOp output)))

/-- Native recovery from the original stored base and phase bits into an existing option cell. -/
def into (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits))
    (output : CWriteRef ctx (outputShape phaseBits)) : Circuit ctx ctx :=
  scopeRecoveryFields ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody spec base sample output)

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native

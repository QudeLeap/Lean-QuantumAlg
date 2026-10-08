/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual decoded proposal equals the source sample slice

The native random instruction writes its proved MSB encoding, while the
proposal addresses and little-endian decoder recover the source's original
integer slice. The separation fact concerns the actual candidate and sample
cells; the enclosing fresh layout supplies it. Every initial candidate value
is admitted, including the unique zero-width word.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width count : Nat}

/-- The real decoder returns the exact source proposal carried by the stored random outcome. -/
theorem proposalDecoded_read_source
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (scratch : ScratchRefs ctx width) (store : Store ctx)
    (value : Fin (2 ^ (count * width)))
    (separate : scratch.candidate.key ∉ sample.storageKeys)
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    ((decodedStep (model := model) sample proposal scratch store).1.read
      (FirstAccepted.cellRead scratch.candidate)).toNat =
        (RSA.decodeFixedWidthWords width count value proposal).val := by
  have decoded := TerminalDecode.terminalDecode_intoFromBitRefs_read_output
    (model := model) .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate store (fun _ => separate)
  have sourceBits :
      (fun bit : Fin width => (store.read (PackedSample.proposalRefs sample proposal bit)).toBool) =
        fun bit : Fin width => value.val.testBit (proposal.val * width + bit.val) := by
    funext bit
    exact PackedSample.packedSample_proposalRefs_read store sample value sampled proposal bit
  calc
    ((decodedStep (model := model) sample proposal scratch store).1.read
        (FirstAccepted.cellRead scratch.candidate)).toNat =
        (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInputFromBitRefs .littleEndian store
            (PackedSample.proposalRefs sample proposal))).val := decoded
    _ = Nat.ofBits (fun bit : Fin width =>
        (store.read (PackedSample.proposalRefs sample proposal bit)).toBool) :=
      ClassicalAlgorithms.TerminalDecode.eval_littleEndian_val _
    _ = Nat.ofBits (fun bit : Fin width =>
        value.val.testBit (proposal.val * width + bit.val)) := congrArg Nat.ofBits sourceBits
    _ = (RSA.decodeFixedWidthWords width count value proposal).val :=
      (PackedSample.packedSample_proposalValue_eq_bits value proposal).symm

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

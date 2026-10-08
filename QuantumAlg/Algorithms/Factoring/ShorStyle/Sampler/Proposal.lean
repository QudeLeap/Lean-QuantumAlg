/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit

/-!
# Actual proposal decoding and first-eligible scanning

Each proposal uses the already established packed-sample addresses, the native
word decoder, a lossless resize, two actual interval tests and a Boolean
conjunction. The stored eligibility bit feeds the real first-accepted selector.
The ordered scan visits the supplied finite proposal list without a host
classification callback or a high-level proposal instruction.

The decoder's width-many shifts overwrite every original candidate bit, so no
extra clearing instruction or scratch initialization is required by that stage.
The public sampler instantiates the scan with the existing sixteen proposals.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open ClassicalRoutines

/-- Stored public interval endpoints and persistent selector latches. -/
structure SharedRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Lossless extended public modulus word. -/
  modulus : CInputRef ctx (.unsignedWord (width + 1))
  /-- The zero supplied by the enclosing actual allocation. -/
  zero : CInputRef ctx (.unsignedWord (width + 1))
  /-- Actual persistent selection state and its Boolean scratch. -/
  selector : FirstAccepted.Refs ctx width

/-- Actual reusable words and comparison bits written by every proposal slot. -/
structure ScratchRefs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- The intrinsically bounded decoded proposal. -/
  candidate : CWriteRef ctx (.unsignedWord width)
  /-- The same proposal widened for comparisons with the public modulus. -/
  extended : CWriteRef ctx (.unsignedWord (width + 1))
  /-- Stored result of the strict-positive test. -/
  positive : CWriteRef ctx .bit
  /-- Stored result of the strict upper interval test. -/
  belowModulus : CWriteRef ctx .bit
  /-- Actual conjunction consumed by the selector. -/
  eligible : CWriteRef ctx .bit

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- Widen the actual candidate word before comparing it with the public modulus. -/
def extendOp (scratch : ScratchRefs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx (FirstAccepted.cellRead scratch.candidate) scratch.extended

/-- Compare the initialized zero with the actual extended candidate. -/
def positiveOp (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
  .wordBinary .lessThan (width + 1) ctx
    (.product shared.zero (FirstAccepted.cellRead scratch.extended)) scratch.positive

/-- Compare the actual extended candidate with the stored public modulus. -/
def belowOp (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
  .wordBinary .lessThan (width + 1) ctx
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) scratch.belowModulus

/-- Conjoin the two actual comparison results. -/
def eligibleOp (scratch : ScratchRefs ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (FirstAccepted.cellRead scratch.positive)
    (FirstAccepted.cellRead scratch.belowModulus)) scratch.eligible

/-- The existing candidate and its actual stored eligibility are the selector's only inputs. -/
def selectorInputs (scratch : ScratchRefs ctx width) : FirstAccepted.Inputs ctx width where
  eligible := FirstAccepted.cellRead scratch.eligible
  candidate := FirstAccepted.cellRead scratch.candidate

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The literal four-instruction comparison suffix after decoding. -/
def comparisonBody (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (extendOp scratch))
    (.seq (BitWord.instruction (positiveOp shared scratch))
      (.seq (BitWord.instruction (belowOp shared scratch))
        (BitWord.instruction (eligibleOp scratch))))

/-- Decode the real addressed bits and compute their stored interval predicate. -/
def prefixBody (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : Circuit model ctx ctx :=
  .seq (TerminalDecode.intoFromBitRefs .littleEndian
    (PackedSample.proposalRefs sample proposal) scratch.candidate)
      (comparisonBody shared scratch)

/-- One real decoded proposal followed by stored-condition first-accepted selection. -/
def slot (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : Circuit model ctx ctx :=
  .seq (prefixBody sample proposal shared scratch)
    (FirstAccepted.circuit (selectorInputs scratch) shared.selector)

/-- Literal ordered composition retains the first success through all later proposal slots. -/
def foldSlots (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) :
    List (Fin count) → Circuit model ctx ctx
  | [] => .id ctx
  | proposal :: remaining =>
      .seq (slot sample proposal shared scratch) (foldSlots sample shared scratch remaining)

/-- Visit each source proposal in its original ascending finite order. -/
def scan (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : Circuit model ctx ctx :=
  foldSlots sample shared scratch (List.ofFn (fun proposal : Fin count => proposal))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

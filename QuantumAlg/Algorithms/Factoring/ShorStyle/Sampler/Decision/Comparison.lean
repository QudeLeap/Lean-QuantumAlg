/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Reduction

/-!
# The accepted arm's real equality test

The default unit is widened with a real resize and compared to the actual
GCD word by the native equality operation. Its stored Boolean is exactly the
ordinary natural equality. No comparison is computed by a structural read.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual store after widening the stored unit and writing the native GCD equality bit. -/
def comparisonStore (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) : Store ctx :=
  (store.applyOp (.wordResize width (width + 1) ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.extended)).applyOp
      (.wordBinary .equal (width + 1) ctx
        (.product (FirstAccepted.cellRead gcdResult) (FirstAccepted.cellRead scratch.extended))
        scratch.positive)

/-- The stored native equality bit compares the incoming GCD and unit values exactly. -/
theorem decisionComparison_bit (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (extendedGcd : scratch.extended.key ≠ gcdResult.key) (store : Store ctx) :
    ((comparisonStore shared scratch gcdResult store).read
      (FirstAccepted.cellRead scratch.positive)).toBool =
        decide ((store.read (FirstAccepted.cellRead gcdResult)).toNat =
          (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat) := by
  let resize : ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
    .wordResize width (width + 1) ctx
      (FirstAccepted.cellRead shared.selector.selected) scratch.extended
  let compare : ClassicalOp
      (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1))) .bit ctx ctx :=
    .wordBinary .equal (width + 1) ctx
      (.product (FirstAccepted.cellRead gcdResult) (FirstAccepted.cellRead scratch.extended))
      scratch.positive
  let widened := store.applyOp resize
  have gcdRead : widened.read (FirstAccepted.cellRead gcdResult) =
      store.read (FirstAccepted.cellRead gcdResult) :=
    Store.read_write_other store resize.outputRef gcdResult.toCStorageRef _ extendedGcd
  have unitValue : (widened.read (FirstAccepted.cellRead scratch.extended)).toNat =
      (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat :=
    decisionExtend_value { scratch with candidate := shared.selector.selected } store
  have actual := congrArg CShape.Value.toBool (Store.read_applyOp_output widened compare)
  change ((comparisonStore shared scratch gcdResult store).read
    (FirstAccepted.cellRead scratch.positive)).toBool =
      decide ((widened.read (FirstAccepted.cellRead gcdResult)).toNat =
        (widened.read (FirstAccepted.cellRead scratch.extended)).toNat) at actual
  rw [gcdRead, unitValue] at actual
  exact actual

/-- The comparison suffix preserves every complete read outside its two actual output keys. -/
theorem decisionComparison_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) {shape : CShape}
    (other : CInputRef ctx shape)
    (extendedFree : scratch.extended.key ∉ other.storageKeys)
    (positiveFree : scratch.positive.key ∉ other.storageKeys) (store : Store ctx) :
    (comparisonStore shared scratch gcdResult store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys _
    (.wordBinary .equal (width + 1) ctx
      (.product (FirstAccepted.cellRead gcdResult) (FirstAccepted.cellRead scratch.extended))
      scratch.positive) other positiveFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys store
          (.wordResize width (width + 1) ctx
            (FirstAccepted.cellRead shared.selector.selected) scratch.extended) other extendedFree)

/-- The accepted store composes actual reduction, comparison, and stored branching. -/
theorem decisionAccepted_store (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    (acceptedStep shared scratch gcdResult store).1 =
      (resultStep shared scratch gcdResult
        (comparisonStore shared scratch gcdResult
          (reducedStore shared scratch gcdResult store))).1 := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

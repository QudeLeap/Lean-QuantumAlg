/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.GCD
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Preservation

/-!
# Exact GCD value in the accepted residue arm

The native resize widens the candidate without truncation, then the real
Euclidean circuit produces its ordinary natural GCD. The zero-result premise
is an internal allocation fact. Preservation refers only to actual writes of
the extended candidate and GCD output, including their complete stored values.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Widening the actual candidate preserves its full natural value, including at width zero. -/
theorem decisionExtend_value (scratch : Proposal.ScratchRefs ctx width) (store : Store ctx) :
    ((store.applyOp (Proposal.extendOp scratch)).read
      (FirstAccepted.cellRead scratch.extended)).toNat =
        (store.read (FirstAccepted.cellRead scratch.candidate)).toNat := by
  have fits := CShape.Value.toNat_lt (store.read (FirstAccepted.cellRead scratch.candidate))
  have widened : (store.read (FirstAccepted.cellRead scratch.candidate)).toNat <
      CShape.wordModulus (width + 1) := by
    change _ < 2 ^ (width + 1)
    rw [pow_succ]
    omega
  exact (congrArg CShape.Value.toNat
    (Store.read_applyOp_output store (Proposal.extendOp scratch))).trans
      (ClassicalOp.eval_wordResize_exact width (width + 1) ctx
        (FirstAccepted.cellRead scratch.candidate) scratch.extended _ widened)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual store after the candidate resize and the expanded Euclidean circuit. -/
def reducedStore (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) : Store ctx :=
  (NumberTheory.GCD.lexicalStep (model := model)
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
    (store.applyOp (Proposal.extendOp scratch))).1

/-- The actually executed GCD stores the exact natural GCD of the original candidate and modulus. -/
theorem decisionReduction_value (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (extendedGcd : scratch.extended.key ≠ gcdResult.key)
    (extendedModulus : scratch.extended.key ∉ shared.modulus.storageKeys)
    (store : Store ctx)
    (resultZero : (store.read (FirstAccepted.cellRead gcdResult)).toNat = 0) :
    ((reducedStore (model := model) shared scratch gcdResult store).read
      (FirstAccepted.cellRead gcdResult)).toNat =
        Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
          (store.read shared.modulus).toNat := by
  let widened := store.applyOp (Proposal.extendOp scratch)
  have resultRead : widened.read (FirstAccepted.cellRead gcdResult) =
      store.read (FirstAccepted.cellRead gcdResult) :=
    Store.read_write_other store (Proposal.extendOp scratch).outputRef
      gcdResult.toCStorageRef _ extendedGcd
  have zeroValue : (widened.read (FirstAccepted.cellRead gcdResult)).toNat = 0 :=
    (congrArg CShape.Value.toNat resultRead).trans resultZero
  have modulusRead : widened.read shared.modulus = store.read shared.modulus :=
    Store.read_applyOp_of_not_mem_storageKeys store (Proposal.extendOp scratch)
      shared.modulus extendedModulus
  have actual := congrArg CShape.Value.toNat
    (NumberTheory.GCD.gcdLexical_read_result (model := model)
      (.product (FirstAccepted.cellRead scratch.extended) shared.modulus)
      gcdResult widened zeroValue)
  have arithmetic (left right : CShape.Word (width + 1)) :
      (encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
        (NumberTheory.GCD.decodeOperands (.product left right)))).toNat =
        Nat.gcd left.toNat right.toNat := by
    cases left
    cases right
    rfl
  exact actual.trans ((arithmetic
    (widened.read (FirstAccepted.cellRead scratch.extended))
    (widened.read shared.modulus)).trans
    (congrArg₂ Nat.gcd (decisionExtend_value scratch store)
      (congrArg CShape.Value.toNat modulusRead)))

/-- The reduction preserves every complete read outside its two actual written cells. -/
theorem decisionReduction_read_other (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    {shape : CShape} (other : CInputRef ctx shape)
    (extendedFree : scratch.extended.key ∉ other.storageKeys)
    (resultFree : gcdResult.key ∉ other.storageKeys) (store : Store ctx) :
    (reducedStore (model := model) shared scratch gcdResult store).read other = store.read other :=
  (NumberTheory.GCD.gcdLexical_read_other (model := model)
    (.product (FirstAccepted.cellRead scratch.extended) shared.modulus) gcdResult
    other resultFree _).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (Proposal.extendOp scratch)
        other extendedFree)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

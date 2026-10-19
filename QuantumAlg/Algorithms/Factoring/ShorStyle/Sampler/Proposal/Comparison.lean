/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact values of the native proposal comparisons

The actual resize preserves every candidate value, including at width zero.
The two stored tests and their actual conjunction recognize the open interval
between the supplied endpoints. No scratch value is assumed initialized.
Structural separation is discharged by the enclosing sampler's real layout;
the zero endpoint is kept arbitrary until that allocation is instantiated.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual cell identities needed to read the four-instruction suffix. -/
structure ComparisonSeparated (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) : Prop where
  /-- All four instructions preserve the decoded candidate. -/
  extendedCandidate : scratch.extended.key ≠ scratch.candidate.key
  positiveCandidate : scratch.positive.key ≠ scratch.candidate.key
  belowCandidate : scratch.belowModulus.key ≠ scratch.candidate.key
  eligibleCandidate : scratch.eligible.key ≠ scratch.candidate.key
  /-- The widened candidate survives the remaining writes. -/
  positiveExtended : scratch.positive.key ≠ scratch.extended.key
  belowExtended : scratch.belowModulus.key ≠ scratch.extended.key
  eligibleExtended : scratch.eligible.key ≠ scratch.extended.key
  /-- The upper test preserves the lower test until their conjunction. -/
  belowPositive : scratch.belowModulus.key ≠ scratch.positive.key
  /-- Earlier writes preserve the endpoint values when each is consumed. -/
  extendedZero : scratch.extended.key ∉ shared.zero.storageKeys
  extendedModulus : scratch.extended.key ∉ shared.modulus.storageKeys
  positiveModulus : scratch.positive.key ∉ shared.modulus.storageKeys

private lemma preserves_cell {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (FirstAccepted.cellRead other) =
      store.read (FirstAccepted.cellRead other) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

private lemma extended_read (scratch : ScratchRefs ctx width) (store : Store ctx) :
    ((store.applyOp (extendOp scratch)).read (FirstAccepted.cellRead scratch.extended)).toNat =
      (store.read (FirstAccepted.cellRead scratch.candidate)).toNat := by
  have fits := CShape.Value.toNat_lt (store.read (FirstAccepted.cellRead scratch.candidate))
  have widened : (store.read (FirstAccepted.cellRead scratch.candidate)).toNat <
      CShape.wordModulus (width + 1) := by
    change _ < 2 ^ (width + 1)
    rw [pow_succ]
    omega
  exact (congrArg CShape.Value.toNat
    (Store.read_applyOp_output store (extendOp scratch))).trans
      (ClassicalOp.eval_wordResize_exact width (width + 1) ctx
        (FirstAccepted.cellRead scratch.candidate) scratch.extended _ widened)

private lemma positive_read (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (store : Store ctx) :
    ((store.applyOp (positiveOp shared scratch)).read
      (FirstAccepted.cellRead scratch.positive)).toBool =
        decide ((store.read shared.zero).toNat <
          (store.read (FirstAccepted.cellRead scratch.extended)).toNat) :=
  congrArg CShape.Value.toBool (Store.read_applyOp_output store (positiveOp shared scratch))

private lemma below_read (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (store : Store ctx) :
    ((store.applyOp (belowOp shared scratch)).read
      (FirstAccepted.cellRead scratch.belowModulus)).toBool =
        decide ((store.read (FirstAccepted.cellRead scratch.extended)).toNat <
          (store.read shared.modulus).toNat) :=
  congrArg CShape.Value.toBool (Store.read_applyOp_output store (belowOp shared scratch))

private lemma eligible_read (scratch : ScratchRefs ctx width) (store : Store ctx) :
    ((store.applyOp (eligibleOp scratch)).read
      (FirstAccepted.cellRead scratch.eligible)).toBool =
        ((store.read (FirstAccepted.cellRead scratch.positive)).toBool &&
          (store.read (FirstAccepted.cellRead scratch.belowModulus)).toBool) := by
  have actual := congrArg CShape.Value.toBool
    (Store.read_applyOp_output store (eligibleOp scratch))
  change ((store.applyOp (eligibleOp scratch)).read
      (FirstAccepted.cellRead scratch.eligible)).toBool =
    ((eligibleOp scratch).eval (.product
      (store.read (FirstAccepted.cellRead scratch.positive))
      (store.read (FirstAccepted.cellRead scratch.belowModulus)))).toBool at actual
  cases left : store.read (FirstAccepted.cellRead scratch.positive) with
  | bit positive =>
      cases right : store.read (FirstAccepted.cellRead scratch.belowModulus) with
      | bit below =>
          rw [left, right] at actual
          exact actual

/-- Four actual comparison instructions preserve the complete candidate word. -/
lemma proposalComparison_candidate (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (separated : ComparisonSeparated shared scratch)
    (store : Store ctx) :
    (comparisonStore shared scratch store).read (FirstAccepted.cellRead scratch.candidate) =
      store.read (FirstAccepted.cellRead scratch.candidate) := by
  unfold comparisonStore
  exact (preserves_cell (eligibleOp scratch) scratch.candidate separated.eligibleCandidate _).trans
    ((preserves_cell (belowOp shared scratch) scratch.candidate separated.belowCandidate _).trans
      ((preserves_cell (positiveOp shared scratch) scratch.candidate
        separated.positiveCandidate _).trans
          (preserves_cell (extendOp scratch) scratch.candidate separated.extendedCandidate store)))

/-- The final widened word contains exactly the original candidate's natural value. -/
lemma proposalComparison_extended (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (separated : ComparisonSeparated shared scratch)
    (store : Store ctx) :
    ((comparisonStore shared scratch store).read
      (FirstAccepted.cellRead scratch.extended)).toNat =
        (store.read (FirstAccepted.cellRead scratch.candidate)).toNat := by
  unfold comparisonStore
  rw [preserves_cell (eligibleOp scratch) scratch.extended separated.eligibleExtended,
    preserves_cell (belowOp shared scratch) scratch.extended separated.belowExtended,
    preserves_cell (positiveOp shared scratch) scratch.extended separated.positiveExtended]
  exact extended_read scratch store

/-- The actual eligibility bit decides the strict interval between the original endpoints. -/
lemma proposalComparison_eligible (shared : SharedRefs ctx width)
    (scratch : ScratchRefs ctx width) (separated : ComparisonSeparated shared scratch)
    (store : Store ctx) :
    ((comparisonStore shared scratch store).read
      (FirstAccepted.cellRead scratch.eligible)).toBool =
        decide ((store.read shared.zero).toNat <
          (store.read (FirstAccepted.cellRead scratch.candidate)).toNat ∧
            (store.read (FirstAccepted.cellRead scratch.candidate)).toNat <
              (store.read shared.modulus).toNat) := by
  unfold comparisonStore
  rw [eligible_read,
    preserves_cell (belowOp shared scratch) scratch.positive separated.belowPositive,
    positive_read, below_read,
    preserves_cell (positiveOp shared scratch) scratch.extended separated.positiveExtended,
    Store.read_applyOp_of_not_mem_storageKeys _ (positiveOp shared scratch)
      shared.modulus separated.positiveModulus,
    Store.read_applyOp_of_not_mem_storageKeys _ (extendOp scratch)
      shared.zero separated.extendedZero,
    Store.read_applyOp_of_not_mem_storageKeys _ (extendOp scratch)
      shared.modulus separated.extendedModulus,
    extended_read, Bool.decide_and]

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

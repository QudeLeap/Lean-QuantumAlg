/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Selection
import Mathlib.Data.List.FinRange
import Batteries.Data.Fin.Fold

/-!
# The actual proposal scan selects the source's first eligible residue

The fold follows the real slot order and preserves the original packed sample
and stored interval endpoints between slots. Its observed latch is exactly
the source's first-success option. Initialization assumptions below refer to
the enclosing sampler's actual zero, modulus and acceptance cells; they do
not constrain scratch values or replace the real instructions with callbacks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- The selection option represented by the two actual persistent latch cells. -/
def selection (shared : SharedRefs ctx width) (store : Store ctx) : Option Nat :=
  if (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool then
    some (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat else none

/-- Actual key separation that preserves the fixed scan inputs between all slots. -/
structure ScanSeparated (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width) : Prop where
  /-- Each actual slot satisfies its already established local layout contracts. -/
  slot : SlotSeparated sample shared scratch
  /-- No slot writes the sample or either stored interval endpoint. -/
  sampleFree : ∀ key ∈ slotKeys shared scratch, key ∉ sample.storageKeys
  zeroFree : ∀ key ∈ slotKeys shared scratch, key ∉ shared.zero.storageKeys
  modulusFree : ∀ key ∈ slotKeys shared scratch, key ∉ shared.modulus.storageKeys

/-- One actual slot appends precisely the source's classified residue to the selection option. -/
theorem proposalSlot_selection
    (sample : CInputRef ctx (.bits (count * width))) (proposal : Fin count)
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (separated : SlotSeparated sample shared scratch) (store : Store ctx)
    (value : Fin (2 ^ (count * width))) (modulus : Nat)
    (sampled : store.read sample = .bits (PackedSample.storedBits value))
    (zero : (store.read shared.zero).toNat = 0)
    (modulusValue : (store.read shared.modulus).toNat = modulus) :
    selection shared (slotStep sample proposal shared scratch store).1 =
      (selection shared store).or
        (RSA.classifyResidueProposals modulus
          (RSA.decodeFixedWidthWords width count value) proposal) := by
  have actual := proposalSlot_latches sample proposal shared scratch separated store value sampled
  dsimp only at actual
  unfold selection
  rw [actual.1, actual.2, zero, modulusValue]
  by_cases eligible : RSA.ResidueEligible modulus
      (RSA.decodeFixedWidthWords width count value proposal).val
  · have classified : RSA.classifyResidueProposals modulus
        (RSA.decodeFixedWidthWords width count value) proposal =
          some (RSA.decodeFixedWidthWords width count value proposal).val := by
      unfold RSA.classifyResidueProposals
      exact dif_pos eligible
    rw [classified]
    have eligibleNat : 0 < (RSA.decodeFixedWidthWords width count value proposal).val ∧
        (RSA.decodeFixedWidthWords width count value proposal).val < modulus := eligible
    cases (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool <;>
      simp [eligibleNat, CShape.Value.toNat]
  · have classified : RSA.classifyResidueProposals modulus
        (RSA.decodeFixedWidthWords width count value) proposal = none := by
      unfold RSA.classifyResidueProposals
      exact dif_neg eligible
    rw [classified]
    have ineligibleNat : ¬ (0 < (RSA.decodeFixedWidthWords width count value proposal).val ∧
        (RSA.decodeFixedWidthWords width count value proposal).val < modulus) := eligible
    cases (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool with
    | false =>
        simp only [Fin.val_pos_iff, Bool.decide_and, Bool.false_or, Bool.and_eq_true,
          decide_eq_true_eq, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
          Option.or_self, ite_eq_right_iff, reduceCtorEq, imp_false, not_and, not_lt]
        intro positive
        exact Nat.le_of_not_gt (fun below => ineligibleNat ⟨Fin.val_pos_iff.mpr positive, below⟩)
    | true => simp [CShape.Value.toNat]

/-- The actual list of slots realizes the ordinary left-to-right first-success fold. -/
theorem proposalFold_selection
    (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (separated : ScanSeparated sample shared scratch) (proposals : List (Fin count))
    (store : Store ctx) (value : Fin (2 ^ (count * width))) (modulus : Nat)
    (sampled : store.read sample = .bits (PackedSample.storedBits value))
    (zero : (store.read shared.zero).toNat = 0)
    (modulusValue : (store.read shared.modulus).toNat = modulus) :
    selection shared (foldSteps sample shared scratch proposals store).1 =
      proposals.foldl (fun selected proposal => selected.or
        (RSA.classifyResidueProposals modulus
          (RSA.decodeFixedWidthWords width count value) proposal)) (selection shared store) := by
  induction proposals generalizing store with
  | nil => rfl
  | cons proposal remaining ih =>
      let next := (slotStep sample proposal shared scratch store).1
      have nextSample : next.read sample = .bits (PackedSample.storedBits value) :=
        (proposalSlot_read_other sample proposal shared scratch sample
          separated.sampleFree store).trans sampled
      have nextZero : (next.read shared.zero).toNat = 0 :=
        (congrArg CShape.Value.toNat (proposalSlot_read_other sample proposal shared scratch
          shared.zero separated.zeroFree store)).trans zero
      have nextModulus : (next.read shared.modulus).toNat = modulus :=
        (congrArg CShape.Value.toNat (proposalSlot_read_other sample proposal shared scratch
          shared.modulus separated.modulusFree store)).trans modulusValue
      change selection shared (foldSteps sample shared scratch remaining next).1 = _
      rw [ih next nextSample nextZero nextModulus, List.foldl_cons]
      rw [proposalSlot_selection sample proposal shared scratch separated.slot store value
        modulus sampled zero modulusValue]

/-- With the actual initially empty latch, ascending slots return the source's first residue. -/
theorem proposalScan_firstValidResidue
    (sample : CInputRef ctx (.bits (count * width)))
    (shared : SharedRefs ctx width) (scratch : ScratchRefs ctx width)
    (separated : ScanSeparated sample shared scratch) (store : Store ctx)
    (value : Fin (2 ^ (count * width))) (modulus : Nat)
    (sampled : store.read sample = .bits (PackedSample.storedBits value))
    (zero : (store.read shared.zero).toNat = 0)
    (modulusValue : (store.read shared.modulus).toNat = modulus)
    (unaccepted : (store.read (FirstAccepted.cellRead shared.selector.accepted)).toBool = false) :
    selection shared (foldSteps sample shared scratch
      (List.ofFn (fun proposal : Fin count => proposal)) store).1 =
        RSA.firstValidResidue (RSA.classifyResidueProposals modulus
          (RSA.decodeFixedWidthWords width count value)) := by
  rw [proposalFold_selection sample shared scratch separated _ store value
    modulus sampled zero modulusValue]
  have empty : selection shared store = none := by simp [selection, unaccepted]
  rw [empty]
  change (List.ofFn (id : Fin count → Fin count)).foldl _ none = _
  rw [List.ofFn_id]
  simp only [RSA.firstValidResidue, Fin.findSome?, Fin.foldl_eq_foldl_finRange,
    Option.orElse_eq_orElse, Option.orElse_eq_or]

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Proposal

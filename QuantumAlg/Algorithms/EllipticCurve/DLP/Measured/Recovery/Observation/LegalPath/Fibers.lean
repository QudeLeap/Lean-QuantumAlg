/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Terminal.StoreCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.BankWords
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Store.Ambient
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Cascade
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Execution.Store.WritePrefix

/-!
# Exact legal finite Store-path fibers with all real streaming outcome labels

Instantaneous coordinates retain the complete old ready Store and the entire
dirty result-cell history. Every reconstructed pre-readout Store uses those
coordinates, and every subsequent step performs its literal original output
write. The actual physical outcome is transported through its Fin.cast
bijection, while the original division Store is copied unchanged.

The equivalence below keeps all legal coarse labels, including branches whose
quantum CP matrix may be zero. It applies to zero length and repeated indices.
No canonical old terminal-write law, generated-history CP sum, positive sigma,
normalization, probability statement or complete instrument is asserted here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace LegalPathFibers

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage.PointCoordinates.StageWord.PathWord
open Recovery.Stage.PointCoordinates.ReadoutRows
open TerminalStoreCoordinates

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The existing physical measurement dimension is transported by exactly outcomeBit's cast. -/
def outcomeEquiv (modulus m : Nat) :
    Fin ((Recovery.Layout.terminal modulus.size m).quantumLayout.wire
      (Recovery.Layout.position modulus.size m 0)).dimension ≃ Fin 2 :=
  finCongr (congrArg PNat.val (Recovery.Layout.position_qubit modulus.size m 0))

lemma outcomeEquiv_apply (modulus m : Nat)
    (outcome : Fin ((Recovery.Layout.terminal modulus.size m).quantumLayout.wire
      (Recovery.Layout.position modulus.size m 0)).dimension) :
    outcomeEquiv modulus m outcome = outcomeBit modulus.size m outcome := rfl

lemma outcomeBit_inverse (modulus m : Nat) (bit : Fin 2) :
    outcomeBit modulus.size m ((outcomeEquiv modulus m).symm bit) = bit :=
  (outcomeEquiv modulus m).apply_symm_apply bit

/-- The instantaneous old coordinate is exactly the full old Store already used by BankWords. -/
lemma instantStore_oldReadyStore (modulus m : Nat)
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    (instantStore modulus m stored).1 = Recovery.Layout.BankWords.oldReadyStore modulus m
      stored := rfl

/-- Every actual chronological measurement label is retained as its original Fin 2 value. -/
def pathOutcomes (modulus m length : Nat)
    (path : Fin length → PathDensity.Branch modulus.size m) : Fin length → Fin 2 :=
  fun index => outcomeBit modulus.size m (path index).2.1

/-- The literal actual stage write; no new circuit, packing or result permutation is introduced. -/
def branchAfter (modulus m : Nat) (index : Fin (2 * m))
    (branch : PathDensity.Branch modulus.size m) : Store (Recovery.Layout.terminal modulus.size
      m) :=
  branch.1.write (Recovery.Stage.output modulus.size m index) (.finite branch.2.1)

/-- The complete history after the original ordered writes, starting at arbitrary dirty values. -/
def historyRun (modulus m : Nat) :
    (length : Nat) → (Fin length → Fin (2 * m)) → (Fin length → Fin 2) →
      Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m) →
      Circuit.measurementCellsHistory (Allocation.after modulus.size (2 * m)) 2 (2 * m)
  | 0, _, _, history => history
  | length + 1, indices, outcomes, history =>
      historyRun modulus m length (Fin.tail indices) (Fin.tail outcomes)
        (BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
          history (indices 0) (outcomes 0))

/-- This history recurrence is exactly the actual Store.writePrefix, including repeated writes. -/
lemma historyRun_actual_prefix (modulus m length : Nat)
    (indices : Fin length → Fin (2 * m)) (outcomes : Fin length → Fin 2)
    (original : Store (Recovery.Layout.terminal modulus.size m)) :
    historyRun modulus m length indices outcomes (instantStore modulus m original).2 =
      (instantStore modulus m
        (Store.writePrefix (fun index => Recovery.Stage.output modulus.size m (indices index))
          (fun index => CShape.Value.finite ((outcomeEquiv modulus m).symm (outcomes index)))
          original length le_rfl)).2 := by
  induction length generalizing original with
  | zero => rfl
  | succ length ih =>
      rw [Store.writePrefix_all_head_tail]
      have tail := ih (Fin.tail indices) (Fin.tail outcomes)
        (original.write (Recovery.Stage.output modulus.size m (indices 0))
          (.finite ((outcomeEquiv modulus m).symm (outcomes 0))))
      rw [instantStore_write_output, outcomeBit_inverse] at tail
      exact tail

/-- Reconstruct one complete pre-readout Store from the old Store and the current full history. -/
def rebuildBranch (modulus m : Nat) (original : Store (Recovery.Layout.terminal modulus.size m))
    (old : Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcome : Fin 2) :
    PathDensity.Branch modulus.size m :=
  ((instantStore modulus m).symm (old.1, (instantStore modulus m original).2),
    ((outcomeEquiv modulus m).symm outcome, old.2))

/-- The reconstructed point call retains precisely the entire prior dirty result history. -/
lemma rebuildBranch_retains (modulus m : Nat)
    (original : Store (Recovery.Layout.terminal modulus.size m))
    (old : Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcome : Fin 2) :
    Recovery.Stage.retains modulus.size m
      (rebuildBranch modulus m original old outcome).1 original := by
  rw [fixed_retains_iff_history]
  simp only [rebuildBranch, Equiv.apply_symm_apply]

/-- Reconstruction preserves the exact complete old Store and original division label. -/
lemma oldBranch_rebuild (modulus m : Nat)
    (original : Store (Recovery.Layout.terminal modulus.size m))
    (old : Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcome : Fin 2) :
    Recovery.Layout.BankWords.oldBranch modulus m (rebuildBranch modulus m original old outcome)
      = old := by
  change ((instantStore modulus m
    ((instantStore modulus m).symm (old.1, (instantStore modulus m original).2))).1, old.2) = old
  simp only [Equiv.apply_symm_apply, Prod.mk.eta]

/-- The actual physical outcome cast is inverted, with no labels removed or identified. -/
lemma outcome_rebuild (modulus m : Nat)
    (original : Store (Recovery.Layout.terminal modulus.size m))
    (old : Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcome : Fin 2) :
    outcomeBit modulus.size m (rebuildBranch modulus m original old outcome).2.1 = outcome :=
  outcomeBit_inverse modulus m outcome

/-- The actual output write preserves the old Store and updates precisely one history slot.
-/
lemma branchAfter_rebuild_coordinates (modulus m : Nat) (index : Fin (2 * m))
    (original : Store (Recovery.Layout.terminal modulus.size m))
    (old : Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcome : Fin 2) :
    instantStore modulus m
        (branchAfter modulus m index (rebuildBranch modulus m original old outcome)) =
      (old.1, BareStores.historyWrite (Allocation.after modulus.size (2 * m)) 2 (2 * m)
        (instantStore modulus m original).2 index outcome) := by
  rw [branchAfter, instantStore_write_output]
  simp only [rebuildBranch, Equiv.apply_symm_apply, outcomeBit_inverse]

/-- Every originally retained complete branch is reconstructed without losing any Store value. -/
lemma rebuildBranch_decode (modulus m : Nat)
    (original : Store (Recovery.Layout.terminal modulus.size m))
    (branch : PathDensity.Branch modulus.size m)
    (retained : Recovery.Stage.retains modulus.size m branch.1 original) :
    rebuildBranch modulus m original (Recovery.Layout.BankWords.oldBranch modulus m branch)
        (outcomeBit modulus.size m branch.2.1) = branch := by
  apply Prod.ext
  · apply (instantStore modulus m).injective
    change instantStore modulus m
      ((instantStore modulus m).symm
        ((instantStore modulus m branch.1).1, (instantStore modulus m original).2)) = _
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl ((fixed_retains_iff_history modulus m branch.1 original).mp retained)
  · apply Prod.ext
    · exact (outcomeEquiv modulus m).symm_apply_apply branch.2.1
    · rfl

/-- Reconstruct the full finite path, carrying the complete Store through each actual output write.
-/
def rebuildRun (modulus m : Nat) :
    (length : Nat) → (Fin length → Fin (2 * m)) →
      (Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m)) → (Fin length → Fin
        2) →
      Store (Recovery.Layout.terminal modulus.size m) →
      (Fin length → PathDensity.Branch modulus.size m) × Store (Recovery.Layout.terminal
        modulus.size m)
  | 0, _, _, _, original => (Fin.elim0, original)
  | length + 1, indices, old, outcomes, original =>
      let head := rebuildBranch modulus m original (old 0) (outcomes 0)
      let tail := rebuildRun modulus m length (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes)
        (branchAfter modulus m (indices 0) head)
      (Fin.cons head tail.1, tail.2)

/-- Every reconstructed run satisfies the actual new trace predicate at its actual final Store. -/
lemma rebuildRun_valid (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (old : Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcomes : Fin
      length → Fin 2)
    (original : Store (Recovery.Layout.terminal modulus.size m)) :
    PathDensity.traceValid modulus.size m length indices
      (rebuildRun modulus m length indices old outcomes original).1 original
      (rebuildRun modulus m length indices old outcomes original).2 := by
  induction length generalizing original with
  | zero => rfl
  | succ length ih =>
      simp only [rebuildRun, PathDensity.traceValid, Fin.cons_zero, Fin.tail_cons]
      exact ⟨rebuildBranch_retains modulus m original (old 0) (outcomes 0),
        ih (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes) _⟩

/-- Every old complete branch label is recovered at its original chronological index. -/
lemma oldPath_rebuildRun (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (old : Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcomes : Fin
      length → Fin 2)
    (original : Store (Recovery.Layout.terminal modulus.size m)) :
    Recovery.Layout.BankWords.oldPath modulus m length
      (rebuildRun modulus m length indices old outcomes original).1 = old := by
  induction length generalizing original with
  | zero => exact Subsingleton.elim _ _
  | succ length ih =>
      funext index
      refine Fin.cases ?_ (fun previous => ?_) index
      · simpa only [Recovery.Layout.BankWords.oldPath, rebuildRun, Fin.cons_zero] using
          oldBranch_rebuild modulus m original (old 0) (outcomes 0)
      · simpa only [Recovery.Layout.BankWords.oldPath, rebuildRun, Fin.cons_succ, Fin.tail] using
          congrFun (ih (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes)
          (branchAfter modulus m (indices 0)
            (rebuildBranch modulus m original (old 0) (outcomes 0)))) previous

/-- Every physical measurement outcome is recovered, even for repeated output destinations. -/
lemma outcomes_rebuildRun (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (old : Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcomes : Fin
      length → Fin 2)
    (original : Store (Recovery.Layout.terminal modulus.size m)) :
    pathOutcomes modulus m length
      (rebuildRun modulus m length indices old outcomes original).1 = outcomes := by
  induction length generalizing original with
  | zero => exact Subsingleton.elim _ _
  | succ length ih =>
      funext index
      refine Fin.cases ?_ (fun previous => ?_) index
      · simpa only [pathOutcomes, rebuildRun, Fin.cons_zero] using
          outcome_rebuild modulus m original (old 0) (outcomes 0)
      · simpa only [pathOutcomes, rebuildRun, Fin.cons_succ, Fin.tail] using
          congrFun (ih (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes)
          (branchAfter modulus m (indices 0)
            (rebuildBranch modulus m original (old 0) (outcomes 0)))) previous

/-- Final Store equality is precisely old legality together with the full actual history endpoint.

The zero-length implication uses injectivity of the full instantaneous Store
equivalence, rather than dropping the dirty history coordinate.
-/
lemma rebuildRun_final_eq_iff (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (old : Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m)) (outcomes : Fin
      length → Fin 2)
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :
    (rebuildRun modulus m length indices old outcomes original).2 = final ↔
      Recovery.Reference.Measured.traceValid modulus.size length indices old
          (instantStore modulus m original).1 (instantStore modulus m final).1 ∧
        historyRun modulus m length indices outcomes (instantStore modulus m original).2 =
          (instantStore modulus m final).2 := by
  induction length generalizing original final with
  | zero =>
      change original = final ↔
        (instantStore modulus m original).1 = (instantStore modulus m final).1 ∧
          (instantStore modulus m original).2 = (instantStore modulus m final).2
      constructor
      · intro same
        subst final
        exact ⟨rfl, rfl⟩
      · intro same
        exact (instantStore modulus m).injective (Prod.ext same.1 same.2)
  | succ length ih =>
      change (rebuildRun modulus m length (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes)
        (branchAfter modulus m (indices 0)
          (rebuildBranch modulus m original (old 0) (outcomes 0)))).2 = final ↔ _
      rw [ih (Fin.tail indices) (Fin.tail old) (Fin.tail outcomes) _ final,
        branchAfter_rebuild_coordinates]
      simp only [Recovery.Reference.Measured.traceValid, Recovery.Point.Store.old_retains_true,
        true_and, historyRun]

/-- Actual legality reconstructs the complete original path and its final Store exactly. -/
lemma rebuildRun_decode (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (path : Fin length → PathDensity.Branch modulus.size m)
    (original final : Store (Recovery.Layout.terminal modulus.size m))
    (valid : PathDensity.traceValid modulus.size m length indices path original final) :
    rebuildRun modulus m length indices (Recovery.Layout.BankWords.oldPath modulus m length path)
        (pathOutcomes modulus m length path) original = (path, final) := by
  induction length generalizing original final with
  | zero =>
      change original = final at valid
      subst final
      exact Prod.ext (Subsingleton.elim _ _) rfl
  | succ length ih =>
      change Recovery.Stage.retains modulus.size m (path 0).1 original ∧
        PathDensity.traceValid modulus.size m length (Fin.tail indices) (Fin.tail path)
          (branchAfter modulus m (indices 0) (path 0)) final at valid
      obtain ⟨retained, tailValid⟩ := valid
      have head := rebuildBranch_decode modulus m original (path 0) retained
      have tail := ih (Fin.tail indices) (Fin.tail path)
        (branchAfter modulus m (indices 0) (path 0)) final tailValid
      change (Fin.cons (α := fun _ : Fin (length + 1) => PathDensity.Branch modulus.size m)
        (rebuildBranch modulus m original (Recovery.Layout.BankWords.oldBranch modulus m (path 0))
          (outcomeBit modulus.size m (path 0).2.1))
        (rebuildRun modulus m length (Fin.tail indices)
          (Recovery.Layout.BankWords.oldPath modulus m length (Fin.tail path))
          (pathOutcomes modulus m length (Fin.tail path))
          (branchAfter modulus m (indices 0)
            (rebuildBranch modulus m original (Recovery.Layout.BankWords.oldBranch modulus m
              (path 0))
              (outcomeBit modulus.size m (path 0).2.1)))).1,
        (rebuildRun modulus m length (Fin.tail indices)
          (Recovery.Layout.BankWords.oldPath modulus m length (Fin.tail path))
          (pathOutcomes modulus m length (Fin.tail path))
          (branchAfter modulus m (indices 0)
            (rebuildBranch modulus m original (Recovery.Layout.BankWords.oldBranch modulus m
              (path 0))
              (outcomeBit modulus.size m (path 0).2.1)))).2) = _
      rw [head, tail, Fin.cons_self_tail]

/-- All actual new legal complete paths at fixed input and output Stores. -/
abbrev NewLegalPaths (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :=
  {path : Fin length → PathDensity.Branch modulus.size m //
    PathDensity.traceValid modulus.size m length indices path original final}

/-- All actual old legal complete paths at the matching instantaneous ready Stores. -/
abbrev ReferenceLegalPaths (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :=
  {path : Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m) //
    Recovery.Reference.Measured.traceValid modulus.size length indices path
      (instantStore modulus m original).1 (instantStore modulus m final).1}

/-- Every actual outcome word with exactly the prescribed complete dirty-history endpoint. -/
abbrev OutcomeFiber (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :=
  {outcomes : Fin length → Fin 2 //
    historyRun modulus m length indices outcomes (instantStore modulus m original).2 =
      (instantStore modulus m final).2}

/-- The exact finite legal fiber equivalence, with no CP support or probability pruning. -/
def legalPathEquiv (modulus m length : Nat) (indices : Fin length → Fin (2 * m))
    (original final : Store (Recovery.Layout.terminal modulus.size m)) :
    NewLegalPaths modulus m length indices original final ≃
      ReferenceLegalPaths modulus m length indices original final ×
        OutcomeFiber modulus m length indices original final where
  toFun path := by
    have endpoint := congrArg Prod.snd
      (rebuildRun_decode modulus m length indices path.val original final path.property)
    have components := (rebuildRun_final_eq_iff modulus m length indices
      (Recovery.Layout.BankWords.oldPath modulus m length path.val)
      (pathOutcomes modulus m length path.val) original final).mp endpoint
    exact (⟨Recovery.Layout.BankWords.oldPath modulus m length path.val, components.1⟩,
      ⟨pathOutcomes modulus m length path.val, components.2⟩)
  invFun choices := by
    have endpoint := (rebuildRun_final_eq_iff modulus m length indices
      choices.1.val choices.2.val original final).mpr ⟨choices.1.property, choices.2.property⟩
    exact ⟨(rebuildRun modulus m length indices choices.1.val choices.2.val original).1,
      Eq.mp (congrArg (fun stored : Store (Recovery.Layout.terminal modulus.size m) =>
        PathDensity.traceValid modulus.size m length indices
          (rebuildRun modulus m length indices choices.1.val choices.2.val original).1
          original stored) endpoint)
        (rebuildRun_valid modulus m length indices choices.1.val choices.2.val original)⟩
  left_inv path := Subtype.ext (congrArg Prod.fst
    (rebuildRun_decode modulus m length indices path.val original final path.property))
  right_inv choices := by
    apply Prod.ext
    · apply Subtype.ext
      exact oldPath_rebuildRun modulus m length indices choices.1.val choices.2.val original
    · apply Subtype.ext
      exact outcomes_rebuildRun modulus m length indices choices.1.val choices.2.val original

end

end LegalPathFibers
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

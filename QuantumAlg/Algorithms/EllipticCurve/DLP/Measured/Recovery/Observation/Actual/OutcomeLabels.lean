/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.PointOutcomeFibers
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Exact actual legal paths and independent measured outcome words

Fixing the complete original Store fixes each retained frame. The real point
outcome then reconstructs one complete pre-readout Store, and the physical bit
is transported by the existing measurement-dimension cast. Reconstruction
performs each literal output write before processing the next point outcome.

The resulting bijection counts every legal complete path once, including
zero quantum branches. It keeps the original Store as a parameter and covers
zero length, dirty histories and repeated output indices. It is a classical
label identity, not a runtime replacement, Gram identity or success claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualOutcomeLabels

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

/-- Actual point labels are final Store first, division Store second. -/
abbrev PointOutcome (width : Nat) :=
  Store (MeasuredPointAddition.context width) × Store (MeasuredPointAddition.context width)

/-- A real point outcome is independent of the subsequent physical readout bit. -/
abbrev StepOutcome (width : Nat) := PointOutcome width × Fin 2

/-- The physical readout label uses precisely its existing qubit-dimension cast. -/
def physicalOutcomeEquiv (width m : Nat) :
    Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension ≃ Fin 2 :=
  finCongr (congrArg PNat.val (Recovery.Layout.position_qubit width m 0))

lemma physicalOutcomeEquiv_apply (width m : Nat)
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension) :
    physicalOutcomeEquiv width m outcome =
      Recovery.Stage.PointCoordinates.ReadoutRows.outcomeBit width m outcome := rfl

/-- Projection retains both real point labels and the actual physical measurement bit. -/
def branchOutcome (width m : Nat) (branch : Branch width m) : StepOutcome width :=
  (((PointOutcomeFibers.storeCoordinates width m branch.1).1, branch.2.2),
    physicalOutcomeEquiv width m branch.2.1)

/-- The original full frame and one real outcome reconstruct exactly one branch Store. -/
def rebuildBranch (width m : Nat) (original : Store (Interface width m))
    (outcome : StepOutcome width) : Branch width m :=
  (((PointOutcomeFibers.retainedStoreEquiv width m original).symm outcome.1.1).val,
    ((physicalOutcomeEquiv width m).symm outcome.2, outcome.1.2))

lemma rebuildBranch_retains (width m : Nat) (original : Store (Interface width m))
    (outcome : StepOutcome width) :
    Recovery.Stage.retains width m (rebuildBranch width m original outcome).1 original :=
  ((PointOutcomeFibers.retainedStoreEquiv width m original).symm outcome.1.1).property

/-- No two real outcome triples are merged by reconstruction. -/
lemma branchOutcome_rebuild (width m : Nat) (original : Store (Interface width m))
    (outcome : StepOutcome width) :
    branchOutcome width m (rebuildBranch width m original outcome) = outcome := by
  change (((PointOutcomeFibers.retainedStoreEquiv width m original)
    ((PointOutcomeFibers.retainedStoreEquiv width m original).symm outcome.1.1), outcome.1.2),
    physicalOutcomeEquiv width m ((physicalOutcomeEquiv width m).symm outcome.2)) = outcome
  simp only [Equiv.apply_symm_apply]

/-- Every actually retained complete branch is reconstructed, with all frame data intact. -/
lemma rebuildBranch_outcome (width m : Nat) (original : Store (Interface width m))
    (branch : Branch width m) (retained : Recovery.Stage.retains width m branch.1 original) :
    rebuildBranch width m original (branchOutcome width m branch) = branch := by
  apply Prod.ext
  · exact congrArg Subtype.val
      ((PointOutcomeFibers.retainedStoreEquiv width m original).symm_apply_apply
        ⟨branch.1, retained⟩)
  · exact Prod.ext ((physicalOutcomeEquiv width m).symm_apply_apply branch.2.1) rfl

/-- This mathematical recurrence step is the original stage's literal output write. -/
def branchAfter (width m : Nat) (index : Fin (2 * m)) (branch : Branch width m) :
    Store (Interface width m) :=
  branch.1.write (Recovery.Stage.output width m index) (.finite branch.2.1)

/-- Decode the complete real outcome word, without discarding any intermediate point label. -/
def pathOutcomes (width m length : Nat) (path : Fin length → Branch width m) :
    Fin length → StepOutcome width :=
  fun current => branchOutcome width m (path current)

/-- Reconstruct every branch and final Store in the original chronological write order. -/
def rebuildRun (width m : Nat) :
    (length : Nat) → (Fin length → Fin (2 * m)) → (Fin length → StepOutcome width) →
      Store (Interface width m) → (Fin length → Branch width m) × Store (Interface width m)
  | 0, _, _, original => (Fin.elim0, original)
  | length + 1, indices, outcomes, original =>
      let head := rebuildBranch width m original (outcomes 0)
      let tail := rebuildRun width m length (Fin.tail indices) (Fin.tail outcomes)
        (branchAfter width m (indices 0) head)
      (Fin.cons head tail.1, tail.2)

/-- Every independent outcome word reconstructs an actually legal path. -/
lemma rebuildRun_valid (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (outcomes : Fin length → StepOutcome width) (original : Store (Interface width m)) :
    traceValid width m length indices (rebuildRun width m length indices outcomes original).1
      original (rebuildRun width m length indices outcomes original).2 := by
  induction length generalizing original with
  | zero => rfl
  | succ length ih =>
      simp only [rebuildRun, traceValid, Fin.cons_zero, Fin.tail_cons]
      exact ⟨rebuildBranch_retains width m original (outcomes 0),
        ih (Fin.tail indices) (Fin.tail outcomes) _⟩

/-- Decoding reconstruction recovers each point Store, division Store and physical bit. -/
lemma pathOutcomes_rebuildRun (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (outcomes : Fin length → StepOutcome width) (original : Store (Interface width m)) :
    pathOutcomes width m length (rebuildRun width m length indices outcomes original).1 =
      outcomes := by
  induction length generalizing original with
  | zero => exact Subsingleton.elim _ _
  | succ length ih =>
      funext current
      refine Fin.cases ?_ (fun previous => ?_) current
      · simpa only [pathOutcomes, rebuildRun, Fin.cons_zero] using
          branchOutcome_rebuild width m original (outcomes 0)
      · simpa only [pathOutcomes, rebuildRun, Fin.cons_succ, Fin.tail] using
          congrFun (ih (Fin.tail indices) (Fin.tail outcomes)
            (branchAfter width m (indices 0)
              (rebuildBranch width m original (outcomes 0)))) previous

/-- Actual legality recovers the entire complete path and its unique actual final Store. -/
lemma rebuildRun_outcomes (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (path : Fin length → Branch width m) (original final : Store (Interface width m))
    (valid : traceValid width m length indices path original final) :
    rebuildRun width m length indices (pathOutcomes width m length path) original =
      (path, final) := by
  induction length generalizing original final with
  | zero =>
      change original = final at valid
      subst final
      exact Prod.ext (Subsingleton.elim _ _) rfl
  | succ length ih =>
      change Recovery.Stage.retains width m (path 0).1 original ∧
        traceValid width m length (Fin.tail indices) (Fin.tail path)
          (branchAfter width m (indices 0) (path 0)) final at valid
      have head := rebuildBranch_outcome width m original (path 0) valid.1
      have tail := ih (Fin.tail indices) (Fin.tail path)
        (branchAfter width m (indices 0) (path 0)) final valid.2
      change (Fin.cons (α := fun _ : Fin (length + 1) => Branch width m)
        (rebuildBranch width m original (branchOutcome width m (path 0)))
        (rebuildRun width m length (Fin.tail indices)
          (pathOutcomes width m length (Fin.tail path))
          (branchAfter width m (indices 0)
            (rebuildBranch width m original (branchOutcome width m (path 0))))).1,
        (rebuildRun width m length (Fin.tail indices)
          (pathOutcomes width m length (Fin.tail path))
          (branchAfter width m (indices 0)
            (rebuildBranch width m original (branchOutcome width m (path 0))))).2) = _
      rw [head, tail, Fin.cons_self_tail]

/-- All complete actual legal paths, including their full final Store. -/
abbrev LegalRun (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (original : Store (Interface width m)) :=
  Σ final : Store (Interface width m),
    {path : Fin length → Branch width m // traceValid width m length indices path original final}

private lemma legal_pair_eq_of_prod_eq {Final Path : Type}
    (legal : Final → Path → Prop) (pair : Path × Final) (path : Path) (final : Final)
    (pair_valid : legal pair.2 pair.1) (path_valid : legal final path)
    (same : pair = (path, final)) :
    (⟨pair.2, ⟨pair.1, pair_valid⟩⟩ : Σ target, {row // legal target row}) =
      ⟨final, ⟨path, path_valid⟩⟩ := by
  cases same
  rfl

/-- The full actual legal-path labels are exactly the independent real step outcomes. -/
def runOutcomeEquiv (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (original : Store (Interface width m)) :
    LegalRun width m length indices original ≃ (Fin length → StepOutcome width) where
  toFun run := pathOutcomes width m length run.2.val
  invFun outcomes :=
    ⟨(rebuildRun width m length indices outcomes original).2,
      ⟨(rebuildRun width m length indices outcomes original).1,
        rebuildRun_valid width m length indices outcomes original⟩⟩
  left_inv run := by
    rcases run with ⟨final, path, valid⟩
    have rebuilt := rebuildRun_outcomes width m length indices path original final valid
    exact legal_pair_eq_of_prod_eq
      (fun target row => traceValid width m length indices row original target)
      (rebuildRun width m length indices (pathOutcomes width m length path) original)
      path final (rebuildRun_valid width m length indices
        (pathOutcomes width m length path) original) valid rebuilt
  right_inv outcomes := pathOutcomes_rebuildRun width m length indices outcomes original

/-- Point outcome words and physical bit words vary independently on this same legal fiber. -/
def pointAndReadoutEquiv (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (original : Store (Interface width m)) :
    LegalRun width m length indices original ≃
      (Fin length → PointOutcome width) × (Fin length → Fin 2) :=
  (runOutcomeEquiv width m length indices original).trans
    (Equiv.arrowProdEquivProdArrow (Fin length) (fun _ => PointOutcome width) (fun _ => Fin 2))

/-- The exact final/division point labels remain at their original chronological indices. -/
lemma pointAndReadoutEquiv_point (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (original : Store (Interface width m)) (run : LegalRun width m length indices original)
    (current : Fin length) :
    (pointAndReadoutEquiv width m length indices original run).1 current =
      ((PointOutcomeFibers.storeCoordinates width m (run.2.val current).1).1,
        (run.2.val current).2.2) := rfl

/-- The exact physical measurement cast remains at its original chronological index. -/
lemma pointAndReadoutEquiv_readout (width m length : Nat)
    (indices : Fin length → Fin (2 * m)) (original : Store (Interface width m))
    (run : LegalRun width m length indices original) (current : Fin length) :
    (pointAndReadoutEquiv width m length indices original run).2 current =
      physicalOutcomeEquiv width m (run.2.val current).2.1 := rfl

/-- Each reconstructed bank factor is precisely the original real point-outcome block. -/
lemma bankBlock_rebuildRun {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m length : Nat) (Reference : Register)
    (indices : Fin length → Fin (2 * m)) (outcomes : Fin length → StepOutcome p.size)
    (original : Store (Interface p.size m)) (current : Fin length) (control : Fin 2) :
    bankBlock (environment := environment) E Q m Reference
        ((rebuildRun p.size m length indices outcomes original).1 current).2.2
        ((rebuildRun p.size m length indices outcomes original).1 current).1 control =
      Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q (ResidualReference
        p.size m Reference)
        (outcomes current).1.2 (outcomes current).1.1 control := by
  have decoded := congrFun
    (pathOutcomes_rebuildRun p.size m length indices outcomes original) current
  dsimp only [pathOutcomes] at decoded
  have finalStore := congrArg (fun outcome : StepOutcome p.size => outcome.1.1) decoded
  have divisionStore := congrArg (fun outcome : StepOutcome p.size => outcome.1.2) decoded
  rw [PointOutcomeFibers.bankBlock_projection]
  change Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q
    (ResidualReference p.size m Reference)
    (branchOutcome p.size m
      ((rebuildRun p.size m length indices outcomes original).1 current)).1.2
    (branchOutcome p.size m
      ((rebuildRun p.size m length indices outcomes original).1 current)).1.1 control = _
  rw [divisionStore, finalStore]

private lemma conditional_sum_subtype {Label Value : Type}
    [Fintype Label] [AddCommMonoid Value]
    (predicate : Label → Prop) (term : Label → Value) :
    (∑ label, if predicate label then term label else 0) =
      ∑ label : Subtype predicate, term label.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) term

/-- Additive legal-path sums reindex without any CP support or probability pruning. -/
lemma legal_sum_point_readout {Value : Type} [AddCommMonoid Value]
    (width m length : Nat) (indices : Fin length → Fin (2 * m))
    (original : Store (Interface width m))
    (term : Store (Interface width m) → (Fin length → Branch width m) → Value) :
    (∑ final : Store (Interface width m), ∑ path : Fin length → Branch width m,
      if traceValid width m length indices path original final then term final path else 0) =
      ∑ points : Fin length → PointOutcome width, ∑ bits : Fin length → Fin 2,
        term (rebuildRun width m length indices (fun current => (points current, bits current))
          original).2
          (rebuildRun width m length indices (fun current => (points current, bits current))
            original).1 := by
  calc
    _ = ∑ run : LegalRun width m length indices original, term run.1 run.2.val := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro final _
      exact conditional_sum_subtype
        (fun path => traceValid width m length indices path original final) (term final)
    _ = ∑ choices : (Fin length → PointOutcome width) × (Fin length → Fin 2),
        term ((pointAndReadoutEquiv width m length indices original).symm choices).1
          ((pointAndReadoutEquiv width m length indices original).symm choices).2.val :=
      ((pointAndReadoutEquiv width m length indices original).symm.sum_comp
        (fun run => term run.1 run.2.val)).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

end

end ActualOutcomeLabels
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery

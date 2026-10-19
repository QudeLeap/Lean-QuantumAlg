/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Fold

/-!
# Terminal-pair alignment for batch recovery

This module aligns an indexed family of literal pair machines with the exact
unordered-pair enumeration of sixteen retained terminal cells.  The value
lemmas keep the early-factor priority of one shared prepared residue explicit.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairRecoveryBatch

open Execution
open ClassicalRoutines

noncomputable section

/-- The retained terminal cells in measurement order. -/
abbrev Terminals {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  Fin 16 → CInputRef ctx (.bits (measurementBits N))

/-- The exact unordered-pair vector of retained terminal cells. -/
def terminalPairs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (terminals : Terminals ctx N) :
    List.Vector
      (CInputRef ctx (.bits (measurementBits N)) ×
        CInputRef ctx (.bits (measurementBits N)))
      LatticePairRecoveryFold.PairCount :=
  (List.Vector.ofFn terminals).unorderedPairs

/-- The two terminal inputs of every literal pair slot are the corresponding
entry of the canonical unordered-pair vector. -/
structure Aligned {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : LatticePairRecoveryFold.Refs ctx N) (terminals : Terminals ctx N) : Prop where
  first : ∀ index, LatticePairReusableRecovery.firstTerminal (refs.pair index) =
    ((terminalPairs terminals).get index).1
  second : ∀ index, LatticePairReusableRecovery.secondTerminal (refs.pair index) =
    ((terminalPairs terminals).get index).2

/-- Decode one retained terminal cell in the pure batch convention. -/
def terminalSample {kind : ProblemKind} {ctx : RuntimeCtx kind} (N : Nat)
    (before : Store ctx)
    (terminal : CInputRef ctx (.bits (measurementBits N))) :
    RSA.ShortLogSample (shortLogBits N) (tradeoffBits N) :=
  BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
    (BatchMachine.sourceBits N before terminal)

/-- Pure factor option at one canonical unordered-pair index. -/
def terminalPairValue {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (generator : (ZMod N)ˣ) (terminals : Terminals ctx N)
    (before : Store ctx)
    (index : Fin LatticePairRecoveryFold.PairCount) : Option Nat :=
  let pair := (terminalPairs terminals).get index
  RSA.recoverFactorFromShortLogPair (shortLogBits N) (tradeoffBits N) generator
    (terminalSample N before pair.1, terminalSample N before pair.2)

/-- One aligned machine slot reads exactly its canonical terminal pair. -/
lemma pairValue_eq_terminalPairValue {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (generator : (ZMod N)ˣ)
    (refs : LatticePairRecoveryFold.Refs ctx N) (terminals : Terminals ctx N)
    (aligned : Aligned refs terminals) (before : Store ctx)
    (index : Fin LatticePairRecoveryFold.PairCount) :
    LatticePairRecoveryFold.pairValue generator refs before index =
      terminalPairValue generator terminals before index := by
  unfold LatticePairRecoveryFold.pairValue terminalPairValue
  dsimp only
  change RSA.recoverFactorFromShortLogPair (shortLogBits N) (tradeoffBits N)
      generator
        (terminalSample N before
            (LatticePairReusableRecovery.firstTerminal (refs.pair index)),
          terminalSample N before
            (LatticePairReusableRecovery.secondTerminal (refs.pair index))) =
    RSA.recoverFactorFromShortLogPair (shortLogBits N) (tradeoffBits N)
      generator
        (terminalSample N before ((terminalPairs terminals).get index).1,
          terminalSample N before ((terminalPairs terminals).get index).2)
  rw [aligned.first index, aligned.second index]

/-- The machine-indexed value list is the canonical terminal-pair value list. -/
lemma pairValues_eq_terminalPairValues {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (generator : (ZMod N)ˣ)
    (refs : LatticePairRecoveryFold.Refs ctx N) (terminals : Terminals ctx N)
    (aligned : Aligned refs terminals) (before : Store ctx) :
    List.ofFn (LatticePairRecoveryFold.pairValue generator refs before) =
      List.ofFn (terminalPairValue generator terminals before) := by
  rw [← List.Vector.toList_ofFn, ← List.Vector.toList_ofFn]
  apply congrArg List.Vector.toList
  apply List.Vector.ext
  intro index
  simp only [List.Vector.get_ofFn]
  exact pairValue_eq_terminalPairValue generator refs terminals aligned before index

/-- Seal the same prepared residue around all sixteen retained terminal cells. -/
def preparedSamples {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (prepared : RSA.PreparedResidue N) (terminals : Terminals ctx N)
    (before : Store ctx) :
    List.Vector
      (BatchRecovery.PreparedSample N (shortLogBits N) (tradeoffBits N)) 16 :=
  (List.Vector.ofFn terminals).map fun terminal =>
    { prepared := prepared
      terminalBits := BatchMachine.sourceBits N before terminal }

/-- One shared prepared residue keeps its early factor ahead of the indexed
short-log factor option. -/
def preparedPairValue {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (prepared : RSA.PreparedResidue N) (terminals : Terminals ctx N)
    (before : Store ctx)
    (index : Fin LatticePairRecoveryFold.PairCount) : Option Nat :=
  prepared.earlyFactor.orElse fun _ =>
    terminalPairValue prepared.unit terminals before index

/-- The pure batch list over a shared prepared residue has exactly the same
canonical pair order and early-factor priority. -/
lemma batchPairValues_preparedSamples {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (prepared : RSA.PreparedResidue N)
    (terminals : Terminals ctx N) (before : Store ctx) :
    BatchRecovery.batchPairValues N (shortLogBits N) (tradeoffBits N)
        (preparedSamples prepared terminals before) =
      List.ofFn (preparedPairValue prepared terminals before) := by
  unfold BatchRecovery.batchPairValues preparedSamples
  rw [List.Vector.toList_unorderedPairs_map]
  rw [List.map_map]
  rw [← List.Vector.toList_ofFn]
  rw [← List.Vector.toList_map]
  apply congrArg List.Vector.toList
  apply List.Vector.ext
  intro index
  unfold LatticePairRecoveryFold.PairCount at index ⊢
  rw [List.Vector.get_map, List.Vector.get_ofFn]
  simp only [Function.comp_apply]
  unfold preparedPairValue terminalPairValue terminalPairs
  rw [BatchRecovery.recoverPreparedPair_same_prepared]
  rfl

private lemma preparedPairValues_eq_map {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (prepared : RSA.PreparedResidue N)
    (terminals : Terminals ctx N) (before : Store ctx) :
    List.ofFn (preparedPairValue prepared terminals before) =
      (List.ofFn (terminalPairValue prepared.unit terminals before)).map
        (fun candidate => prepared.earlyFactor.orElse fun _ => candidate) := by
  change List.ofFn (fun index => prepared.earlyFactor.orElse fun _ =>
      terminalPairValue prepared.unit terminals before index) = _
  exact List.ofFn_comp' (terminalPairValue prepared.unit terminals before)
    (fun candidate => prepared.earlyFactor.orElse fun _ => candidate)

private lemma foldl_retainCandidate_some (values : List (Option Nat)) (value : Nat) :
    values.foldl FirstAccepted.retainFirst (some value) =
      some value := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons]
      change tail.foldl FirstAccepted.retainFirst
        (some value) = some value
      exact inductionHypothesis

private lemma foldl_retainSuccessful_some (values : List (Option Nat)) (value : Nat) :
    values.foldl BatchRecovery.retainFirstSuccessful (some value) = some value := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons]
      change tail.foldl BatchRecovery.retainFirstSuccessful (some value) = some value
      exact inductionHypothesis

private lemma fold_sharedEarly_eq_firstSuccessful
    (early : Option Nat) (values : List (Option Nat)) (nonempty : values ≠ []) :
    values.foldl FirstAccepted.retainFirst early =
      BatchRecovery.firstSuccessful
        (values.map fun candidate => early.orElse fun _ => candidate) := by
  cases early with
  | none =>
      have pointwise : (fun candidate : Option Nat =>
          none.orElse fun _ => candidate) = id := by
        funext candidate
        rfl
      have mapped : values.map (fun candidate => none.orElse fun _ => candidate) =
          values := by rw [pointwise, List.map_id]
      rw [mapped]
      unfold BatchRecovery.firstSuccessful
      congr 1
  | some value =>
      cases values with
      | nil => exact (nonempty rfl).elim
      | cons head tail =>
          rw [List.foldl_cons]
          change tail.foldl FirstAccepted.retainFirst
              (some value) =
            BatchRecovery.firstSuccessful
              (some value :: tail.map fun _candidate => some value)
          rw [foldl_retainCandidate_some]
          unfold BatchRecovery.firstSuccessful
          rw [List.foldl_cons]
          change some value =
            (tail.map fun _candidate => some value).foldl
              BatchRecovery.retainFirstSuccessful (some value)
          exact (foldl_retainSuccessful_some _ _).symm

/-- Starting from the shared prepared residue's early factor, the aligned
machine fold is exactly the pure fixed-batch value. -/
lemma selectedFold_eq_batchValue {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {N : Nat} (prepared : RSA.PreparedResidue N)
    (refs : LatticePairRecoveryFold.Refs ctx N) (terminals : Terminals ctx N)
    (aligned : Aligned refs terminals) (before : Store ctx) :
    (List.ofFn
        (LatticePairRecoveryFold.pairValue prepared.unit refs before)).foldl
        FirstAccepted.retainFirst prepared.earlyFactor =
      BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N)
        (preparedSamples prepared terminals before) := by
  rw [pairValues_eq_terminalPairValues prepared.unit refs terminals aligned before]
  unfold BatchRecovery.batchValue
  rw [batchPairValues_preparedSamples, preparedPairValues_eq_map]
  apply fold_sharedEarly_eq_firstSuccessful
  let zero : Fin LatticePairRecoveryFold.PairCount :=
    ⟨0, by norm_num [LatticePairRecoveryFold.PairCount, Nat.choose]⟩
  have member : terminalPairValue prepared.unit terminals before zero ∈
      List.ofFn (terminalPairValue prepared.unit terminals before) := by
    exact List.mem_ofFn.mpr ⟨zero, rfl⟩
  intro empty
  rw [empty] at member
  simp only [List.not_mem_nil] at member

end

end LatticePairRecoveryBatch
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

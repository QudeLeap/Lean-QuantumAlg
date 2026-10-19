/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Comparison
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Readout

/-!
# Exact parameter fields of the accepted native residue arm

The result follows the actual Euclidean value, stored comparison and chosen
instructions. The unit and tag may initially hold arbitrary values in this
local theorem; the enclosing initialization later supplies one and false.
Only the actual GCD result cell uses the internal zero-allocation fact.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Internal write/read separation of the accepted arm, supplied by the actual fresh layout. -/
structure AcceptedSeparated (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1))) : Prop where
  extendedGcd : scratch.extended.key ≠ gcdResult.key
  extendedCandidate : scratch.extended.key ≠ scratch.candidate.key
  extendedUnit : scratch.extended.key ≠ shared.selector.selected.key
  extendedFlag : scratch.extended.key ≠ scratch.eligible.key
  extendedModulus : scratch.extended.key ∉ shared.modulus.storageKeys
  gcdCandidate : gcdResult.key ≠ scratch.candidate.key
  gcdUnit : gcdResult.key ≠ shared.selector.selected.key
  gcdFlag : gcdResult.key ≠ scratch.eligible.key
  positiveGcd : scratch.positive.key ≠ gcdResult.key
  positiveCandidate : scratch.positive.key ≠ scratch.candidate.key
  positiveUnit : scratch.positive.key ≠ shared.selector.selected.key
  positiveFlag : scratch.positive.key ≠ scratch.eligible.key
  candidateUnit : scratch.candidate.key ≠ shared.selector.selected.key
  candidateFlag : scratch.candidate.key ≠ scratch.eligible.key
  unitFlag : shared.selector.selected.key ≠ scratch.eligible.key

private lemma cell_free {shape : CShape} (other : CWriteRef ctx shape)
    (key : StorageKey) (different : key ≠ other.key) :
    key ∉ (FirstAccepted.cellRead other).storageKeys := by
  simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using different

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private lemma preserved_cell (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    {shape : CShape} (other : CWriteRef ctx shape)
    (extendedOther : scratch.extended.key ≠ other.key)
    (gcdOther : gcdResult.key ≠ other.key)
    (positiveOther : scratch.positive.key ≠ other.key) (store : Store ctx) :
    (comparisonStore shared scratch gcdResult
      (reducedStore (model := model)
        shared scratch gcdResult store)).read (FirstAccepted.cellRead other) =
        store.read (FirstAccepted.cellRead other) :=
  (decisionComparison_read_other shared scratch gcdResult (FirstAccepted.cellRead other)
    (cell_free other _ extendedOther) (cell_free other _ positiveOther) _).trans
      (decisionReduction_read_other (model := model)
        shared scratch gcdResult (FirstAccepted.cellRead other)
        (cell_free other _ extendedOther) (cell_free other _ gcdOther) store)

/-- Exact complete fields obtained from the actual accepted GCD and stored result branch. -/
lemma decisionAccepted_fields (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (gcdResult : CWriteRef ctx (.unsignedWord (width + 1)))
    (separated : AcceptedSeparated shared scratch gcdResult) (store : Store ctx)
    (resultZero : (store.read (FirstAccepted.cellRead gcdResult)).toNat = 0) :
    fields shared scratch (acceptedStep (model := model) shared scratch gcdResult store).1 =
      if Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
          (store.read shared.modulus).toNat =
            (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat then
        .product (store.read (FirstAccepted.cellRead scratch.candidate))
          (.product (store.read (FirstAccepted.cellRead scratch.eligible))
            (CShape.wordOfNat width 0))
      else
        .product (store.read (FirstAccepted.cellRead shared.selector.selected))
          (.product (.bit (!(store.read (FirstAccepted.cellRead scratch.eligible)).toBool))
            (CShape.wordOfNat width
              (Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
                (store.read shared.modulus).toNat))) := by
  let reduced := reducedStore (model := model) shared scratch gcdResult store
  let compared := comparisonStore shared scratch gcdResult reduced
  have reducedGcd : (reduced.read (FirstAccepted.cellRead gcdResult)).toNat =
      Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
        (store.read shared.modulus).toNat :=
    decisionReduction_value (model := model) shared scratch gcdResult separated.extendedGcd
      separated.extendedModulus store resultZero
  have reducedUnit : reduced.read (FirstAccepted.cellRead shared.selector.selected) =
      store.read (FirstAccepted.cellRead shared.selector.selected) :=
    decisionReduction_read_other (model := model) shared scratch gcdResult
      (FirstAccepted.cellRead shared.selector.selected)
      (cell_free shared.selector.selected _ separated.extendedUnit)
      (cell_free shared.selector.selected _ separated.gcdUnit) store
  have choice : (compared.read (FirstAccepted.cellRead scratch.positive)).toBool =
      decide (Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
        (store.read shared.modulus).toNat =
          (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat) := by
    have actual := decisionComparison_bit shared scratch gcdResult separated.extendedGcd reduced
    rw [reducedGcd, reducedUnit] at actual
    exact actual
  have candidateRead : compared.read (FirstAccepted.cellRead scratch.candidate) =
      store.read (FirstAccepted.cellRead scratch.candidate) :=
    preserved_cell (model := model)
      shared scratch gcdResult scratch.candidate separated.extendedCandidate
      separated.gcdCandidate separated.positiveCandidate store
  have unitRead : compared.read (FirstAccepted.cellRead shared.selector.selected) =
      store.read (FirstAccepted.cellRead shared.selector.selected) :=
    preserved_cell (model := model)
      shared scratch gcdResult shared.selector.selected separated.extendedUnit
      separated.gcdUnit separated.positiveUnit store
  have flagRead : compared.read (FirstAccepted.cellRead scratch.eligible) =
      store.read (FirstAccepted.cellRead scratch.eligible) :=
    preserved_cell (model := model) shared scratch gcdResult scratch.eligible separated.extendedFlag
      separated.gcdFlag separated.positiveFlag store
  have gcdValue : (compared.read (FirstAccepted.cellRead gcdResult)).toNat =
      Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
        (store.read shared.modulus).toNat :=
    (congrArg CShape.Value.toNat
      (decisionComparison_read_other shared scratch gcdResult (FirstAccepted.cellRead gcdResult)
        (cell_free gcdResult _ separated.extendedGcd)
        (cell_free gcdResult _ separated.positiveGcd) reduced)).trans reducedGcd
  rw [decisionAccepted_store, decisionResult_store, choice]
  by_cases same : Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
      (store.read shared.modulus).toNat =
        (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat
  · have chosen : decide (Nat.gcd
        (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
        (store.read shared.modulus).toNat =
          (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat) = true := by
      simpa only [decide_eq_true_eq] using same
    rw [if_pos chosen]
    refine (decisionUnit_fields shared scratch separated.candidateUnit
      separated.candidateFlag separated.unitFlag compared).trans ?_
    calc
      _ = CShape.Value.product (store.read (FirstAccepted.cellRead scratch.candidate))
          (.product (store.read (FirstAccepted.cellRead scratch.eligible))
            (CShape.wordOfNat width 0)) := by rw [candidateRead, flagRead]
      _ = _ := (if_pos same).symm
  · have rejected : ¬ (decide (Nat.gcd
        (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
        (store.read shared.modulus).toNat =
          (store.read (FirstAccepted.cellRead shared.selector.selected)).toNat) = true) := by
      simpa only [decide_eq_true_eq] using same
    rw [if_neg rejected]
    refine (decisionFactor_fields shared scratch gcdResult separated.candidateUnit
      separated.unitFlag.symm separated.candidateFlag.symm compared).trans ?_
    calc
      _ = CShape.Value.product (store.read (FirstAccepted.cellRead shared.selector.selected))
          (.product (.bit (!(store.read (FirstAccepted.cellRead scratch.eligible)).toBool))
            (CShape.wordOfNat width
              (Nat.gcd (store.read (FirstAccepted.cellRead scratch.candidate)).toNat
                (store.read shared.modulus).toNat))) := by rw [unitRead, flagRead, gcdValue]
      _ = _ := (if_neg same).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

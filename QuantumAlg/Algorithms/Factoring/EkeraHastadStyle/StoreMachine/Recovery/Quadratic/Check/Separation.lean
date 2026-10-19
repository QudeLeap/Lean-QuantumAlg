/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Pair

/-!
# Physical separation for the two quadratic candidate checks

The checks execute in source order and reuse one compatible six-cell physical
footprint.  A compact external contract records that the caller's persistent
factor selector is disjoint from this later quadratic allocation.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticCheckSeparation

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory

noncomputable section

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := QuadraticScratchLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  QuadraticScratchLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  QuadraticScratchLayout.cellRef cells cell

end Layout

/-- The four mutable cells of the caller's persistent factor selector. -/
inductive FactorCell where
  | accepted | selected | available | take
deriving DecidableEq

/-- Exact shape of one factor-selector cell. -/
def factorShape (width : Nat) : FactorCell → CShape
  | .accepted => .bit
  | .selected => .unsignedWord width
  | .available => .bit
  | .take => .bit

/-- Read view of one persistent factor-selector cell. -/
def factorInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : FirstAccepted.Refs ctx width) :
    (cell : FactorCell) → CInputRef ctx (factorShape width cell)
  | .accepted => FirstAccepted.cellRead refs.accepted
  | .selected => FirstAccepted.cellRead refs.selected
  | .available => FirstAccepted.cellRead refs.available
  | .take => FirstAccepted.cellRead refs.take

/-- Physical key of one persistent factor-selector cell. -/
def factorKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : FirstAccepted.Refs ctx width) : FactorCell → StorageKey
  | .accepted => refs.accepted.toCStorageRef.key
  | .selected => refs.selected.toCStorageRef.key
  | .available => refs.available.toCStorageRef.key
  | .take => refs.take.toCStorageRef.key

/-- Cross-allocation and persistent-latch separation; the two scratch references may alias. -/
structure FactorSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (selection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N)) : Prop where
  availableAccepted : selection.available.key ≠ selection.accepted.key
  takeAccepted : selection.take.key ≠ selection.accepted.key
  availableSelected : selection.available.key ≠ selection.selected.key
  takeSelected : selection.take.key ≠ selection.selected.key
  acceptedSelected : selection.accepted.key ≠ selection.selected.key
  avoidsQuadratic : ∀ factor cell,
    ((Layout.cellRef cells cell).toCStorageRef.key ∉ (factorInput selection factor).storageKeys)

/-- Distinct named quadratic cells avoid each other's storage key. -/
private lemma cellAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (left right : Layout.Cell) (different : left ≠ right) :
    (Layout.cellRef cells right).toCStorageRef.key ∉
      (FirstAccepted.cellRead (Layout.cellRef cells left)).storageKeys := by
  intro present
  have equal := List.mem_singleton.mp present
  exact different
    (QuadraticScratchLayout.cellRef_key_injective cells distinct equal.symm)

/-- A quadratic cell avoids one external factor-selector key. -/
private lemma cellAvoidsFactor {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (selection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (separation : FactorSeparation cells selection)
    (cell : Layout.Cell) (factor : FactorCell) :
    factorKey selection factor ∉
      (FirstAccepted.cellRead (Layout.cellRef cells cell)).storageKeys := by
  have avoided := separation.avoidsQuadratic factor cell
  cases factor <;>
    simp only [factorInput, factorKey, FirstAccepted.cellRead, CInputRef.storageKeys,
      List.mem_singleton] at avoided ⊢ <;>
    exact Ne.symm avoided

/-- One candidate input supplies all six candidate-dependent avoidances. -/
private structure CandidateAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (candidate : CInputRef ctx
      (.unsignedWord (QuadraticScratchLayout.CandidateWidth N))) : Prop where
  greaterThanOne :
    ((Layout.cellRef cells .greaterThanOne).toCStorageRef.key ∉ candidate.storageKeys)
  candidateWide :
    ((Layout.cellRef cells .candidateWide).toCStorageRef.key ∉ candidate.storageKeys)
  belowModulus :
    ((Layout.cellRef cells .belowModulus).toCStorageRef.key ∉ candidate.storageKeys)
  division : ((Layout.cellRef cells .division).toCStorageRef.key ∉ candidate.storageKeys)
  modulusAccepted :
    ((Layout.cellRef cells .modulusAccepted).toCStorageRef.key ∉ candidate.storageKeys)
  eligible : ((Layout.cellRef cells .eligible).toCStorageRef.key ∉ candidate.storageKeys)

/-- Internal distinctness plus candidate avoidance supplies one total check. -/
private lemma totalCheckSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (candidate : CInputRef ctx
      (.unsignedWord (QuadraticScratchLayout.CandidateWidth N)))
    (candidateAvoids : CandidateAvoids cells candidate) :
    QuadraticCandidateCheck.TotalSeparation
      (QuadraticScratchViews.totalCheckRefs cells candidate) := by
  refine ⟨?_, cellAvoids cells distinct .one .greaterThanOne (by decide),
    candidateAvoids.greaterThanOne,
    cellAvoids cells distinct .modulus .greaterThanOne (by decide),
    cellAvoids cells distinct .zero .greaterThanOne (by decide), ?_, ?_, ?_⟩
  · refine ⟨candidateAvoids.candidateWide,
      cellAvoids cells distinct .modulus .candidateWide (by decide),
      cellAvoids cells distinct .zero .candidateWide (by decide),
      candidateAvoids.belowModulus,
      cellAvoids cells distinct .modulus .belowModulus (by decide),
      cellAvoids cells distinct .zero .belowModulus (by decide),
      cellAvoids cells distinct .candidateWide .belowModulus (by decide), ?_,
      cellAvoids cells distinct .belowModulus .division (by decide),
      cellAvoids cells distinct .belowModulus .modulusAccepted (by decide),
      cellAvoids cells distinct .belowModulus .eligible (by decide),
      cellAvoids cells distinct .modulusAccepted .eligible (by decide)⟩
    exact ⟨cellAvoids cells distinct .modulus .division (by decide),
      candidateAvoids.division,
      cellAvoids cells distinct .zero .division (by decide),
      cellAvoids cells distinct .division .modulusAccepted (by decide),
      cellAvoids cells distinct .zero .modulusAccepted (by decide)⟩
  · exact ⟨candidateAvoids.candidateWide, candidateAvoids.belowModulus,
      candidateAvoids.division, candidateAvoids.modulusAccepted,
      candidateAvoids.eligible⟩
  · exact ⟨cellAvoids cells distinct .modulus .candidateWide (by decide),
      cellAvoids cells distinct .modulus .belowModulus (by decide),
      cellAvoids cells distinct .modulus .division (by decide),
      cellAvoids cells distinct .modulus .modulusAccepted (by decide),
      cellAvoids cells distinct .modulus .eligible (by decide)⟩
  · exact ⟨cellAvoids cells distinct .zero .candidateWide (by decide),
      cellAvoids cells distinct .zero .belowModulus (by decide),
      cellAvoids cells distinct .zero .division (by decide),
      cellAvoids cells distinct .zero .modulusAccepted (by decide),
      cellAvoids cells distinct .zero .eligible (by decide)⟩

/-- First generated candidate avoids every shared check write. -/
private lemma firstCandidateAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N))) :
    CandidateAvoids cells (QuadraticCandidates.firstCandidate
      (QuadraticScratchViews.candidateRefs cells shortLog)) := by
  exact ⟨cellAvoids cells distinct .firstOutput .greaterThanOne (by decide),
    cellAvoids cells distinct .firstOutput .candidateWide (by decide),
    cellAvoids cells distinct .firstOutput .belowModulus (by decide),
    cellAvoids cells distinct .firstOutput .division (by decide),
    cellAvoids cells distinct .firstOutput .modulusAccepted (by decide),
    cellAvoids cells distinct .firstOutput .eligible (by decide)⟩

/-- Second generated candidate avoids every shared check write. -/
private lemma secondCandidateAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N))) :
    CandidateAvoids cells (QuadraticCandidates.secondCandidate
      (QuadraticScratchViews.candidateRefs cells shortLog)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cellAvoids cells distinct .secondCandidate .greaterThanOne (by decide)
  · exact cellAvoids cells distinct .secondCandidate .candidateWide (by decide)
  · exact cellAvoids cells distinct .secondCandidate .belowModulus (by decide)
  · exact cellAvoids cells distinct .secondCandidate .division (by decide)
  · exact cellAvoids cells distinct .secondCandidate .modulusAccepted (by decide)
  · exact cellAvoids cells distinct .secondCandidate .eligible (by decide)

/-- One arbitrary caller read avoids every write of one total check. -/
private lemma totalCallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (candidate : CInputRef ctx
      (.unsignedWord (QuadraticScratchLayout.CandidateWidth N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (decision :
      ((Layout.cellRef cells .greaterThanOne).toCStorageRef.key ∉ other.storageKeys))
    (wide : ((Layout.cellRef cells .candidateWide).toCStorageRef.key ∉ other.storageKeys))
    (below : ((Layout.cellRef cells .belowModulus).toCStorageRef.key ∉ other.storageKeys))
    (division : ((Layout.cellRef cells .division).toCStorageRef.key ∉ other.storageKeys))
    (accepted :
      ((Layout.cellRef cells .modulusAccepted).toCStorageRef.key ∉ other.storageKeys))
    (eligible : ((Layout.cellRef cells .eligible).toCStorageRef.key ∉ other.storageKeys)) :
    QuadraticCandidateCheck.TotalCallerFrameAvoids
      (QuadraticScratchViews.totalCheckRefs cells candidate) other :=
  ⟨decision, ⟨wide, below, division, accepted, eligible⟩⟩

/-- Cross-allocation avoidance supplies exactly the canonical selector's input obligations. -/
private lemma selectorSeparated {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (selection : FirstAccepted.Refs ctx (QuadraticScratchLayout.CandidateWidth N))
    (separation : FactorSeparation cells selection)
    (inputs : FirstAccepted.Inputs ctx (QuadraticScratchLayout.CandidateWidth N))
    (eligibleEq : inputs.eligible = FirstAccepted.cellRead (Layout.cellRef cells .eligible))
    (candidateAvoids : ∀ factor, factorKey selection factor ∉ inputs.candidate.storageKeys) :
    FirstAccepted.Separated inputs selection := by
  refine ⟨?_, candidateAvoids .available, candidateAvoids .take,
    separation.availableAccepted, separation.takeAccepted, separation.availableSelected,
    separation.takeSelected, separation.acceptedSelected⟩
  rw [eligibleEq]
  exact cellAvoidsFactor cells selection separation .eligible .available

/-- The zero input's caller frame is proved independently of the full pair certificate. -/
private lemma zeroFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (selection : FirstAccepted.Refs ctx (QuadraticScratchLayout.CandidateWidth N))
    (factorSeparation : FactorSeparation cells selection) :
    QuadraticCandidateSelect.CallerFrameAvoids
      (QuadraticScratchViews.firstSelectRefs cells
        (QuadraticScratchViews.candidateRefs cells shortLog) selection)
      (QuadraticScratchViews.zeroInput cells) := by
  let firstCandidate := QuadraticCandidates.firstCandidate
    (QuadraticScratchViews.candidateRefs cells shortLog)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact totalCallerFrame cells firstCandidate (QuadraticScratchViews.zeroInput cells)
      (cellAvoids cells distinct .zero .greaterThanOne (by decide))
      (cellAvoids cells distinct .zero .candidateWide (by decide))
      (cellAvoids cells distinct .zero .belowModulus (by decide))
      (cellAvoids cells distinct .zero .division (by decide))
      (cellAvoids cells distinct .zero .modulusAccepted (by decide))
      (cellAvoids cells distinct .zero .eligible (by decide))
  · exact cellAvoidsFactor cells selection factorSeparation .zero .accepted
  · exact cellAvoidsFactor cells selection factorSeparation .zero .selected
  · exact cellAvoidsFactor cells selection factorSeparation .zero .available
  · exact cellAvoidsFactor cells selection factorSeparation .zero .take

/-- The two ordered checks follow from physical and selector separation. -/
lemma pairSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (selection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (factorSeparation : FactorSeparation cells selection) :
    QuadraticCandidatePairSelect.Separation
      (QuadraticScratchViews.pairSelectRefs cells
        (QuadraticScratchViews.candidateRefs cells shortLog) selection) := by
  let candidates := QuadraticScratchViews.candidateRefs cells shortLog
  let firstCandidate := QuadraticCandidates.firstCandidate candidates
  let secondCandidate := QuadraticCandidates.secondCandidate candidates
  let first := QuadraticScratchViews.firstSelectRefs cells candidates selection
  let second := QuadraticScratchViews.secondSelectRefs cells candidates selection
  have firstSelection : FirstAccepted.Separated
      (QuadraticCandidateSelect.selectionInputs first) selection := by
    apply selectorSeparated cells selection factorSeparation
      (QuadraticCandidateSelect.selectionInputs first) rfl
    intro factor
    exact cellAvoidsFactor cells selection factorSeparation .firstOutput factor
  have secondSelection : FirstAccepted.Separated
      (QuadraticCandidateSelect.selectionInputs second) selection := by
    apply selectorSeparated cells selection factorSeparation
      (QuadraticCandidateSelect.selectionInputs second) rfl
    intro factor
    exact cellAvoidsFactor cells selection factorSeparation .secondCandidate factor
  have factorFrame (factor : FactorCell) (candidate : CInputRef ctx
      (.unsignedWord (QuadraticScratchLayout.CandidateWidth N))) :
      QuadraticCandidateCheck.TotalCallerFrameAvoids
        (QuadraticScratchViews.totalCheckRefs cells candidate)
        (factorInput selection factor) :=
    totalCallerFrame cells candidate (factorInput selection factor)
      (factorSeparation.avoidsQuadratic factor .greaterThanOne)
      (factorSeparation.avoidsQuadratic factor .candidateWide)
      (factorSeparation.avoidsQuadratic factor .belowModulus)
      (factorSeparation.avoidsQuadratic factor .division)
      (factorSeparation.avoidsQuadratic factor .modulusAccepted)
      (factorSeparation.avoidsQuadratic factor .eligible)
  have firstSep : QuadraticCandidateSelect.Separation first :=
    ⟨totalCheckSeparation cells distinct firstCandidate
        (firstCandidateAvoids cells distinct shortLog),
      firstSelection, factorFrame .accepted firstCandidate,
      factorFrame .selected firstCandidate⟩
  have secondSep : QuadraticCandidateSelect.Separation second :=
    ⟨totalCheckSeparation cells distinct secondCandidate
        (secondCandidateAvoids cells distinct shortLog),
      secondSelection, factorFrame .accepted secondCandidate,
      factorFrame .selected secondCandidate⟩
  refine ⟨firstSep, secondSep, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact totalCallerFrame cells firstCandidate secondCandidate
        (secondCandidateAvoids cells distinct shortLog).greaterThanOne
        (secondCandidateAvoids cells distinct shortLog).candidateWide
        (secondCandidateAvoids cells distinct shortLog).belowModulus
        (secondCandidateAvoids cells distinct shortLog).division
        (secondCandidateAvoids cells distinct shortLog).modulusAccepted
        (secondCandidateAvoids cells distinct shortLog).eligible
    · change ((factorKey selection .accepted) ∉ secondCandidate.storageKeys)
      exact cellAvoidsFactor cells selection factorSeparation .secondCandidate .accepted
    · change ((factorKey selection .selected) ∉ secondCandidate.storageKeys)
      exact cellAvoidsFactor cells selection factorSeparation .secondCandidate .selected
    · change ((factorKey selection .available) ∉ secondCandidate.storageKeys)
      exact cellAvoidsFactor cells selection factorSeparation .secondCandidate .available
    · change ((factorKey selection .take) ∉ secondCandidate.storageKeys)
      exact cellAvoidsFactor cells selection factorSeparation .secondCandidate .take
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact totalCallerFrame cells firstCandidate (QuadraticScratchViews.oneInput cells)
        (cellAvoids cells distinct .one .greaterThanOne (by decide))
        (cellAvoids cells distinct .one .candidateWide (by decide))
        (cellAvoids cells distinct .one .belowModulus (by decide))
        (cellAvoids cells distinct .one .division (by decide))
        (cellAvoids cells distinct .one .modulusAccepted (by decide))
        (cellAvoids cells distinct .one .eligible (by decide))
    · exact cellAvoidsFactor cells selection factorSeparation .one .accepted
    · exact cellAvoidsFactor cells selection factorSeparation .one .selected
    · exact cellAvoidsFactor cells selection factorSeparation .one .available
    · exact cellAvoidsFactor cells selection factorSeparation .one .take
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact totalCallerFrame cells firstCandidate
        (QuadraticScratchViews.modulusInput cells)
        (cellAvoids cells distinct .modulus .greaterThanOne (by decide))
        (cellAvoids cells distinct .modulus .candidateWide (by decide))
        (cellAvoids cells distinct .modulus .belowModulus (by decide))
        (cellAvoids cells distinct .modulus .division (by decide))
        (cellAvoids cells distinct .modulus .modulusAccepted (by decide))
        (cellAvoids cells distinct .modulus .eligible (by decide))
    · exact cellAvoidsFactor cells selection factorSeparation .modulus .accepted
    · exact cellAvoidsFactor cells selection factorSeparation .modulus .selected
    · exact cellAvoidsFactor cells selection factorSeparation .modulus .available
    · exact cellAvoidsFactor cells selection factorSeparation .modulus .take
  · exact zeroFrame cells distinct shortLog selection factorSeparation

end

end QuadraticCheckSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

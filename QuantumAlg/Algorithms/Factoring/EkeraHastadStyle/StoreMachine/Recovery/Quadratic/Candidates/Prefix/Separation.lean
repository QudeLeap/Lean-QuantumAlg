/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Views
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Layout

/-!
# Physical separation for the quadratic candidate prefix

One allocator `Distinct` certificate supplies every internal key inequality of
the quadratic prefix and candidate generator.  The only external obligation is
that the preceding short-log word avoids this later allocation.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticPrefixSeparation

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

/-- The preceding short-log word avoids every quadratic allocation cell. -/
def ShortLogAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N))) :
    Prop :=
  ∀ cell, ((Layout.cellRef cells cell).toCStorageRef.key ∉ shortLog.storageKeys)

/-- Avoidance of every cell written by the candidate generator. -/
structure CandidateCallerAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  center : ((Layout.cellRef cells .center).toCStorageRef.key ∉ other.storageKeys)
  centerSquare :
    ((Layout.cellRef cells .centerSquare).toCStorageRef.key ∉ other.storageKeys)
  subtractLessThan :
    ((Layout.cellRef cells .subtractLessThan).toCStorageRef.key ∉ other.storageKeys)
  subtractOutput :
    ((Layout.cellRef cells .subtractOutput).toCStorageRef.key ∉ other.storageKeys)
  sqrtWideInput :
    ((Layout.cellRef cells .sqrtWideInput).toCStorageRef.key ∉ other.storageKeys)
  sqrtRoot : ((Layout.cellRef cells .sqrtRoot).toCStorageRef.key ∉ other.storageKeys)
  sqrtHalf : ((Layout.cellRef cells .sqrtHalf).toCStorageRef.key ∉ other.storageKeys)
  sqrtMidCarry :
    ((Layout.cellRef cells .sqrtMidCarry).toCStorageRef.key ∉ other.storageKeys)
  sqrtSquare : ((Layout.cellRef cells .sqrtSquare).toCStorageRef.key ∉ other.storageKeys)
  sqrtTooLarge :
    ((Layout.cellRef cells .sqrtTooLarge).toCStorageRef.key ∉ other.storageKeys)
  sqrtTake : ((Layout.cellRef cells .sqrtTake).toCStorageRef.key ∉ other.storageKeys)
  sqrtOutput : ((Layout.cellRef cells .sqrtOutput).toCStorageRef.key ∉ other.storageKeys)
  centerWide : ((Layout.cellRef cells .centerWide).toCStorageRef.key ∉ other.storageKeys)
  rootWide : ((Layout.cellRef cells .rootWide).toCStorageRef.key ∉ other.storageKeys)
  firstLessThan :
    ((Layout.cellRef cells .firstLessThan).toCStorageRef.key ∉ other.storageKeys)
  firstOutput : ((Layout.cellRef cells .firstOutput).toCStorageRef.key ∉ other.storageKeys)
  secondCandidate :
    ((Layout.cellRef cells .secondCandidate).toCStorageRef.key ∉ other.storageKeys)

/-- Two distinct named physical cells avoid each other's storage key. -/
private theorem cellAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (left right : Layout.Cell) (different : left ≠ right) :
    (Layout.cellRef cells right).toCStorageRef.key ∉
      (FirstAccepted.cellRead (Layout.cellRef cells left)).storageKeys := by
  intro present
  have equal := List.mem_singleton.mp present
  exact different
    (QuadraticScratchLayout.cellRef_key_injective cells distinct equal.symm)

/-- Physical cell implementing one mutable integer-square-root round cell. -/
private def roundCell : IntegerSqrt.Cell → Layout.Cell
  | .root => .sqrtRoot
  | .half => .sqrtHalf
  | .midCarry => .sqrtMidCarry
  | .square => .sqrtSquare
  | .tooLarge => .sqrtTooLarge
  | .take => .sqrtTake

/-- The round-cell map is injective. -/
private theorem roundCell_injective : Function.Injective roundCell := by
  intro left right equal
  cases left <;> cases right <;> simp [roundCell] at equal ⊢

/-- Integer-square-root semantic keys are exactly the named physical keys. -/
private theorem roundKey_eq {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (cell : IntegerSqrt.Cell) :
    IntegerSqrt.writeKey (QuadraticScratchViews.sqrtRoundRefs cells) cell =
      (Layout.cellRef cells (roundCell cell)).toCStorageRef.key := by
  cases cell <;> rfl

/-- Distinct physical cells supply the integer-square-root round contract. -/
private theorem roundSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct) :
    IntegerSqrt.Separation
      (NatSqrt.wideInput (QuadraticScratchViews.sqrtRefs cells))
      (QuadraticScratchViews.sqrtRoundRefs cells) := by
  constructor
  · intro cell
    rw [roundKey_eq]
    exact cellAvoids cells distinct .sqrtWideInput (roundCell cell)
      (by cases cell <;> decide)
  · intro left right equal
    apply roundCell_injective
    apply QuadraticScratchLayout.cellRef_key_injective cells distinct
    simpa only [roundKey_eq] using equal

/-- Distinct physical cells supply the natural-square-root contract. -/
private theorem sqrtSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct) :
    NatSqrt.Separation (QuadraticScratchViews.sqrtRefs cells) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cellAvoids cells distinct .subtractOutput .sqrtWideInput (by decide)
  · exact cellAvoids cells distinct .subtractOutput .sqrtRoot (by decide)
  · exact cellAvoids cells distinct .subtractOutput .sqrtHalf (by decide)
  · exact cellAvoids cells distinct .sqrtWideInput .sqrtRoot (by decide)
  · exact cellAvoids cells distinct .sqrtWideInput .sqrtHalf (by decide)
  · exact cellAvoids cells distinct .sqrtRoot .sqrtHalf (by decide)
  · exact cellAvoids cells distinct .sqrtHalf .sqrtRoot (by decide)
  · exact cellAvoids cells distinct .sqrtOutput .sqrtWideInput (by decide)
  · exact cellAvoids cells distinct .sqrtOutput .sqrtRoot (by decide)
  · exact cellAvoids cells distinct .sqrtOutput .sqrtHalf (by decide)
  · exact roundSeparation cells distinct

/-- Four physical key inequalities provide a complete pre-square-root caller frame. -/
private theorem prefixFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (source : Layout.Cell) (center : source ≠ .center) (square : source ≠ .centerSquare)
    (lessThan : source ≠ .subtractLessThan) (output : source ≠ .subtractOutput) :
    QuadraticPrefix.PrefixFrameAvoids (QuadraticScratchViews.prefixRefs cells shortLog)
      (FirstAccepted.cellRead (Layout.cellRef cells source)) :=
  ⟨cellAvoids cells distinct source .center center,
    cellAvoids cells distinct source .centerSquare square,
    cellAvoids cells distinct source .subtractLessThan lessThan,
    cellAvoids cells distinct source .subtractOutput output⟩

/-- Named physical exclusions provide the complete square-root caller frame. -/
private theorem sqrtFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (source : Layout.Cell) (wideInput : source ≠ .sqrtWideInput)
    (round : ∀ cell, source ≠ roundCell cell) (output : source ≠ .sqrtOutput) :
    QuadraticPrefix.SqrtFrameAvoids (QuadraticScratchViews.prefixRefs cells shortLog)
      (FirstAccepted.cellRead (Layout.cellRef cells source)) := by
  refine ⟨cellAvoids cells distinct source .sqrtWideInput wideInput, ?_,
    cellAvoids cells distinct source .sqrtOutput output⟩
  intro cell
  change IntegerSqrt.writeKey (QuadraticScratchViews.sqrtRoundRefs cells) cell ∉
    (FirstAccepted.cellRead (Layout.cellRef cells source)).storageKeys
  rw [roundKey_eq]
  exact cellAvoids cells distinct source (roundCell cell) (round cell)

/-- Physical distinctness supplies the complete quadratic-prefix separation. -/
private theorem prefixSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (shortAvoids : ShortLogAvoids cells shortLog) :
    QuadraticPrefix.Separation
      (QuadraticScratchViews.prefixRefs cells shortLog) := by
  refine ⟨shortAvoids .center,
    cellAvoids cells distinct .modulus .center (by decide),
    cellAvoids cells distinct .modulus .centerSquare (by decide),
    cellAvoids cells distinct .center .centerSquare (by decide),
    cellAvoids cells distinct .center .subtractLessThan (by decide),
    cellAvoids cells distinct .center .subtractOutput (by decide),
    cellAvoids cells distinct .centerSquare .subtractOutput (by decide), ?_,
    sqrtSeparation cells distinct, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨cellAvoids cells distinct .centerSquare .subtractLessThan (by decide),
      cellAvoids cells distinct .modulus .subtractLessThan (by decide),
      cellAvoids cells distinct .subtractLessThan .subtractOutput (by decide)⟩
  · exact prefixFrame cells distinct shortLog .sqrtWideInput
      (by decide) (by decide) (by decide) (by decide)
  · exact prefixFrame cells distinct shortLog .sqrtRoot
      (by decide) (by decide) (by decide) (by decide)
  · exact prefixFrame cells distinct shortLog .sqrtHalf
      (by decide) (by decide) (by decide) (by decide)
  · exact prefixFrame cells distinct shortLog .sqrtOutput
      (by decide) (by decide) (by decide) (by decide)
  · exact sqrtFrame cells distinct shortLog .center (by decide)
      (fun cell => by cases cell <;> decide) (by decide)
  · exact sqrtFrame cells distinct shortLog .centerSquare (by decide)
      (fun cell => by cases cell <;> decide) (by decide)
  · exact sqrtFrame cells distinct shortLog .subtractOutput (by decide)
      (fun cell => by cases cell <;> decide) (by decide)

/-- The full candidate generator follows from one compact physical contract. -/
theorem candidateSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (shortAvoids : ShortLogAvoids cells shortLog) :
    QuadraticCandidates.Separation
      (QuadraticScratchViews.candidateRefs cells shortLog) := by
  refine ⟨prefixSeparation cells distinct shortLog shortAvoids, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact cellAvoids cells distinct .sqrtOutput .centerWide (by decide)
  · exact cellAvoids cells distinct .center .rootWide (by decide)
  · exact cellAvoids cells distinct .centerWide .rootWide (by decide)
  · exact cellAvoids cells distinct .centerWide .firstOutput (by decide)
  · exact cellAvoids cells distinct .rootWide .firstOutput (by decide)
  · exact cellAvoids cells distinct .centerWide .secondCandidate (by decide)
  · exact cellAvoids cells distinct .rootWide .secondCandidate (by decide)
  · exact cellAvoids cells distinct .firstOutput .secondCandidate (by decide)
  · exact ⟨cellAvoids cells distinct .centerWide .firstLessThan (by decide),
      cellAvoids cells distinct .rootWide .firstLessThan (by decide),
      cellAvoids cells distinct .firstLessThan .firstOutput (by decide)⟩

/-- The physical footprint projects to the generator's caller-frame contract. -/
theorem candidateCallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : CandidateCallerAvoids cells other) :
    QuadraticCandidates.CallerFrameAvoids
      (QuadraticScratchViews.candidateRefs cells shortLog) other := by
  refine ⟨⟨avoids.center, avoids.centerSquare, avoids.subtractLessThan,
      avoids.subtractOutput⟩, ?_, avoids.centerWide, avoids.rootWide,
    avoids.firstLessThan, avoids.firstOutput, avoids.secondCandidate⟩
  refine ⟨avoids.sqrtWideInput, ?_, avoids.sqrtOutput⟩
  intro cell
  cases cell with
  | root => exact avoids.sqrtRoot
  | half => exact avoids.sqrtHalf
  | midCarry => exact avoids.sqrtMidCarry
  | square => exact avoids.sqrtSquare
  | tooLarge => exact avoids.sqrtTooLarge
  | take => exact avoids.sqrtTake

end

end QuadraticPrefixSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

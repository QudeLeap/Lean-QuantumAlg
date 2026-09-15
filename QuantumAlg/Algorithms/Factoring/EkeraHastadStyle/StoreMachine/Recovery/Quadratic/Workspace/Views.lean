/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program.Guarded

/-!
# Reusable quadratic-recovery workspace views

This module maps the physical quadratic package into the natural-square-root,
candidate-generation, two checked-candidate, and guarded-recovery reference
structures.  Both ordered candidate checks share one physical check footprint;
their executions remain sequential and use the caller's persistent selector.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticScratchViews

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory

noncomputable section

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := QuadraticScratchLayout.Cell

/-- Abbreviation for the local short width interface. -/
abbrev ShortWidth (N : Nat) := QuadraticScratchLayout.ShortWidth N

/-- Abbreviation for the local center width interface. -/
abbrev CenterWidth (N : Nat) := QuadraticScratchLayout.CenterWidth N

/-- Abbreviation for the local discriminant width interface. -/
abbrev DiscriminantWidth (N : Nat) :=
  QuadraticScratchLayout.DiscriminantWidth N

/-- Abbreviation for the local work width interface. -/
abbrev WorkWidth (N : Nat) := QuadraticScratchLayout.WorkWidth N

/-- Abbreviation for the local candidate width interface. -/
abbrev CandidateWidth (N : Nat) := QuadraticScratchLayout.CandidateWidth N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  QuadraticScratchLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  QuadraticScratchLayout.cellRef cells cell

end Layout

/-- Wide public-modulus input shared by generation and both checks. -/
def modulusInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    CInputRef ctx (.unsignedWord (Layout.DiscriminantWidth N)) :=
  FirstAccepted.cellRead (Layout.cellRef cells .modulus)

/-- Candidate-width literal one shared by both strict lower-bound checks. -/
def oneInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    CInputRef ctx (.unsignedWord (Layout.CandidateWidth N)) :=
  FirstAccepted.cellRead (Layout.cellRef cells .one)

/-- Candidate-width literal zero shared by both remainder checks. -/
def zeroInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    CInputRef ctx (.unsignedWord (Layout.CandidateWidth N)) :=
  FirstAccepted.cellRead (Layout.cellRef cells .zero)

/-- Saturating subtraction feeding the natural-square-root input. -/
def prefixSubtractRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    NatSub.Refs ctx (Layout.DiscriminantWidth N) where
  left := FirstAccepted.cellRead (Layout.cellRef cells .centerSquare)
  right := modulusInput cells
  lessThan := Layout.cellRef cells .subtractLessThan
  lessThanRole :=
    QuadraticScratchLayout.cellRef_role cells .subtractLessThan
  output := Layout.cellRef cells .subtractOutput
  outputRole := QuadraticScratchLayout.cellRef_role cells .subtractOutput

/-- Six-cell binary-refinement round view used by the natural square root. -/
def sqrtRoundRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    IntegerSqrt.Refs ctx (Layout.WorkWidth N) where
  root := Layout.cellRef cells .sqrtRoot
  rootRole := QuadraticScratchLayout.cellRef_role cells .sqrtRoot
  half := Layout.cellRef cells .sqrtHalf
  halfRole := QuadraticScratchLayout.cellRef_role cells .sqrtHalf
  midCarry := Layout.cellRef cells .sqrtMidCarry
  midCarryRole := QuadraticScratchLayout.cellRef_role cells .sqrtMidCarry
  square := Layout.cellRef cells .sqrtSquare
  squareRole := QuadraticScratchLayout.cellRef_role cells .sqrtSquare
  tooLarge := Layout.cellRef cells .sqrtTooLarge
  tooLargeRole := QuadraticScratchLayout.cellRef_role cells .sqrtTooLarge
  take := Layout.cellRef cells .sqrtTake
  takeRole := QuadraticScratchLayout.cellRef_role cells .sqrtTake

/-- Complete natural-square-root reference package. -/
def sqrtRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) :
    NatSqrt.Refs ctx (Layout.DiscriminantWidth N) where
  input := FirstAccepted.cellRead (Layout.cellRef cells .subtractOutput)
  wideInput := Layout.cellRef cells .sqrtWideInput
  wideInputRole := QuadraticScratchLayout.cellRef_role cells .sqrtWideInput
  round := sqrtRoundRefs cells
  output := Layout.cellRef cells .sqrtOutput
  outputRole := Or.inl
    (QuadraticScratchLayout.cellRef_role cells .sqrtOutput)

/-- Complete quadratic-prefix view for one supplied short logarithm. -/
def prefixRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (Layout.ShortWidth N))) :
    QuadraticPrefix.Refs ctx (Layout.ShortWidth N) where
  shortLog := shortLog
  modulus := modulusInput cells
  center := Layout.cellRef cells .center
  centerRole := QuadraticScratchLayout.cellRef_role cells .center
  centerSquare := Layout.cellRef cells .centerSquare
  centerSquareRole := QuadraticScratchLayout.cellRef_role cells .centerSquare
  subtract := prefixSubtractRefs cells
  subtractLeft := rfl
  subtractRight := rfl
  sqrt := sqrtRefs cells
  sqrtInput := rfl

/-- Saturating subtraction producing the first quadratic candidate. -/
def firstCandidateSubtractRefs {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) :
    NatSub.Refs ctx (Layout.CandidateWidth N) where
  left := FirstAccepted.cellRead (Layout.cellRef cells .centerWide)
  right := FirstAccepted.cellRead (Layout.cellRef cells .rootWide)
  lessThan := Layout.cellRef cells .firstLessThan
  lessThanRole := QuadraticScratchLayout.cellRef_role cells .firstLessThan
  output := Layout.cellRef cells .firstOutput
  outputRole := QuadraticScratchLayout.cellRef_role cells .firstOutput

/-- Complete two-candidate generator view. -/
def candidateRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (Layout.ShortWidth N))) :
    QuadraticCandidates.Refs ctx (Layout.ShortWidth N) where
  quadraticPrefix := prefixRefs cells shortLog
  centerWide := Layout.cellRef cells .centerWide
  centerWideRole := QuadraticScratchLayout.cellRef_role cells .centerWide
  rootWide := Layout.cellRef cells .rootWide
  rootWideRole := QuadraticScratchLayout.cellRef_role cells .rootWide
  first := firstCandidateSubtractRefs cells
  firstLeft := rfl
  firstRight := rfl
  second := Layout.cellRef cells .secondCandidate
  secondRole := QuadraticScratchLayout.cellRef_role cells .secondCandidate

/-- Shared variable-width remainder-check scratch for either candidate. -/
def modulusCheckRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidate : CInputRef ctx (.unsignedWord (Layout.CandidateWidth N))) :
    NatModCheck.Refs ctx (Layout.DiscriminantWidth N)
      (Layout.CandidateWidth N) where
  numerator := modulusInput cells
  divisor := candidate
  division := Layout.cellRef cells .division
  divisionRole := QuadraticScratchLayout.cellRef_role cells .division
  zero := zeroInput cells
  accepted := Layout.cellRef cells .modulusAccepted
  acceptedRole := QuadraticScratchLayout.cellRef_role cells .modulusAccepted

/-- Shared positive-candidate check scratch for one candidate input. -/
def positiveCheckRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidate : CInputRef ctx (.unsignedWord (Layout.CandidateWidth N))) :
    QuadraticCandidateCheck.Refs ctx (Layout.ShortWidth N) where
  candidate := candidate
  modulus := modulusInput cells
  zero := zeroInput cells
  candidateWide := Layout.cellRef cells .candidateWide
  candidateWideRole := QuadraticScratchLayout.cellRef_role cells .candidateWide
  belowModulus := Layout.cellRef cells .belowModulus
  belowModulusRole := QuadraticScratchLayout.cellRef_role cells .belowModulus
  modulusCheck := modulusCheckRefs cells candidate
  modulusCheckNumerator := rfl
  modulusCheckDivisor := rfl
  modulusCheckZero := rfl
  eligible := Layout.cellRef cells .eligible
  eligibleRole := QuadraticScratchLayout.cellRef_role cells .eligible

/-- Complete total divisor check for one candidate input. -/
def totalCheckRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidate : CInputRef ctx (.unsignedWord (Layout.CandidateWidth N))) :
    QuadraticCandidateCheck.TotalRefs ctx (Layout.ShortWidth N) where
  positiveCheck := positiveCheckRefs cells candidate
  one := oneInput cells
  greaterThanOne := Layout.cellRef cells .greaterThanOne
  greaterThanOneRole :=
    QuadraticScratchLayout.cellRef_role cells .greaterThanOne

/-- First checked selector step over the shared persistent factor latch. -/
def firstSelectRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidates : QuadraticCandidates.Refs ctx (Layout.ShortWidth N))
    (selection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticCandidateSelect.Refs ctx (Layout.ShortWidth N) where
  check := totalCheckRefs cells (QuadraticCandidates.firstCandidate
    candidates)
  selection := selection

/-- Second checked selector step over the same persistent factor latch. -/
def secondSelectRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidates : QuadraticCandidates.Refs ctx (Layout.ShortWidth N))
    (selection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticCandidateSelect.Refs ctx (Layout.ShortWidth N) where
  check := totalCheckRefs cells (QuadraticCandidates.secondCandidate
    candidates)
  selection := selection

/-- Ordered pair of checked candidates sharing all compatible scratch. -/
def pairSelectRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (candidates : QuadraticCandidates.Refs ctx (Layout.ShortWidth N))
    (selection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticCandidatePairSelect.Refs ctx (Layout.ShortWidth N) where
  first := firstSelectRefs cells candidates selection
  second := secondSelectRefs cells candidates selection
  sharedSelection := rfl

/-- Candidate generator and both checked selectors with exact data-flow wiring. -/
def recoveryRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (Layout.ShortWidth N)))
    (selection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticRecoveryMachine.Refs ctx (Layout.ShortWidth N) :=
  let candidates := candidateRefs cells shortLog
  { candidates := candidates
    pair := pairSelectRefs cells candidates selection
    firstCandidate := rfl
    secondCandidate := rfl
    firstModulus := rfl
    secondModulus := rfl }

/-- Reusable quadratic package with a workspace square-root output. -/
def resetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLog : CInputRef ctx (.unsignedWord (Layout.ShortWidth N)))
    (selection : FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticRecoveryReset.Refs ctx (Layout.ShortWidth N) :=
  let recovery := recoveryRefs cells shortLog selection
  { recovery := recovery
    sqrtOutputRole := by
      change
        (Layout.cellRef cells .sqrtOutput).toCStorageRef.role = .workspace
      exact QuadraticScratchLayout.cellRef_role cells .sqrtOutput }

/-- Final guarded recovery view wired to the preceding short-log selector. -/
def guardedRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (shortLogSelection :
      FirstAccepted.Direct.Refs ctx (Layout.ShortWidth N))
    (factorSelection :
      FirstAccepted.Refs ctx (Layout.CandidateWidth N)) :
    QuadraticRecoveryGuarded.Refs ctx (Layout.ShortWidth N) :=
  let shortLog :=
    FirstAccepted.cellRead shortLogSelection.selected
  let quadratic := resetRefs cells shortLog factorSelection
  { shortLogSelection := shortLogSelection
    quadratic := quadratic
    shortLogInput := rfl }

end

end QuadraticScratchViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

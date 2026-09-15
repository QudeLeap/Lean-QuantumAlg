/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Separation

/-!
# Physical separation for quadratic recovery

This module combines the candidate prefix and the two ordered checks.  The
three persistent constants are physical cells outside the generator's write
footprint, while the caller's factor selector is framed by the compact
cross-allocation contract.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticRecoverySeparation

open Execution
open ClassicalRoutines

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

/-- Distinct named quadratic cells avoid each other's storage key. -/
private theorem cellAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (left right : Layout.Cell) (different : left ≠ right) :
    (Layout.cellRef cells right).toCStorageRef.key ∉
      (FirstAccepted.cellRead (Layout.cellRef cells left)).storageKeys := by
  intro present
  have equal := List.mem_singleton.mp present
  exact different
    (QuadraticScratchLayout.cellRef_key_injective cells distinct equal.symm)

/-- Any of the three persistent constants avoids every generator write. -/
private theorem constantCallerAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (source : Layout.Cell)
    (allowed : source = .one ∨ source = .zero ∨ source = .modulus) :
    QuadraticPrefixSeparation.CandidateCallerAvoids cells
      (FirstAccepted.cellRead (Layout.cellRef cells source)) := by
  rcases allowed with rfl | rfl | rfl <;>
    exact
      ⟨cellAvoids cells distinct _ .center (by decide),
        cellAvoids cells distinct _ .centerSquare (by decide),
        cellAvoids cells distinct _ .subtractLessThan (by decide),
        cellAvoids cells distinct _ .subtractOutput (by decide),
        cellAvoids cells distinct _ .sqrtWideInput (by decide),
        cellAvoids cells distinct _ .sqrtRoot (by decide),
        cellAvoids cells distinct _ .sqrtHalf (by decide),
        cellAvoids cells distinct _ .sqrtMidCarry (by decide),
        cellAvoids cells distinct _ .sqrtSquare (by decide),
        cellAvoids cells distinct _ .sqrtTooLarge (by decide),
        cellAvoids cells distinct _ .sqrtTake (by decide),
        cellAvoids cells distinct _ .sqrtOutput (by decide),
        cellAvoids cells distinct _ .centerWide (by decide),
        cellAvoids cells distinct _ .rootWide (by decide),
        cellAvoids cells distinct _ .firstLessThan (by decide),
        cellAvoids cells distinct _ .firstOutput (by decide),
        cellAvoids cells distinct _ .secondCandidate (by decide)⟩

/-- One persistent factor-selector cell avoids every generator write. -/
private theorem factorCallerAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N)
    (selection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (separation : QuadraticCheckSeparation.FactorSeparation cells selection)
    (factor : QuadraticCheckSeparation.FactorCell) :
    QuadraticPrefixSeparation.CandidateCallerAvoids cells
      (QuadraticCheckSeparation.factorInput selection factor) :=
  ⟨separation.avoidsQuadratic factor .center,
    separation.avoidsQuadratic factor .centerSquare,
    separation.avoidsQuadratic factor .subtractLessThan,
    separation.avoidsQuadratic factor .subtractOutput,
    separation.avoidsQuadratic factor .sqrtWideInput,
    separation.avoidsQuadratic factor .sqrtRoot,
    separation.avoidsQuadratic factor .sqrtHalf,
    separation.avoidsQuadratic factor .sqrtMidCarry,
    separation.avoidsQuadratic factor .sqrtSquare,
    separation.avoidsQuadratic factor .sqrtTooLarge,
    separation.avoidsQuadratic factor .sqrtTake,
    separation.avoidsQuadratic factor .sqrtOutput,
    separation.avoidsQuadratic factor .centerWide,
    separation.avoidsQuadratic factor .rootWide,
    separation.avoidsQuadratic factor .firstLessThan,
    separation.avoidsQuadratic factor .firstOutput,
    separation.avoidsQuadratic factor .secondCandidate⟩

/-- One allocator and two compact external contracts supply full recovery. -/
theorem recoverySeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Layout.Cells ctx N) (distinct : cells.Distinct)
    (shortLog : CInputRef ctx (.unsignedWord (QuadraticScratchLayout.ShortWidth N)))
    (shortAvoids : QuadraticPrefixSeparation.ShortLogAvoids cells shortLog)
    (selection : FirstAccepted.Refs ctx
      (QuadraticScratchLayout.CandidateWidth N))
    (factorSeparation :
      QuadraticCheckSeparation.FactorSeparation cells selection) :
    QuadraticRecoveryMachine.Separation
      (QuadraticScratchViews.recoveryRefs cells shortLog selection) := by
  let candidates := QuadraticScratchViews.candidateRefs cells shortLog
  have constantFrame (source : Layout.Cell)
      (allowed : source = .one ∨ source = .zero ∨ source = .modulus) :
      QuadraticCandidates.CallerFrameAvoids candidates
        (FirstAccepted.cellRead (Layout.cellRef cells source)) :=
    QuadraticPrefixSeparation.candidateCallerFrame cells shortLog _
      (constantCallerAvoids cells distinct source allowed)
  have factorFrame (factor : QuadraticCheckSeparation.FactorCell) :
      QuadraticCandidates.CallerFrameAvoids candidates
        (QuadraticCheckSeparation.factorInput selection factor) :=
    QuadraticPrefixSeparation.candidateCallerFrame cells shortLog _
      (factorCallerAvoids cells selection factorSeparation factor)
  refine ⟨QuadraticPrefixSeparation.candidateSeparation
      cells distinct shortLog shortAvoids,
    QuadraticCheckSeparation.pairSeparation
      cells distinct shortLog selection factorSeparation, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact constantFrame .one (Or.inl rfl)
  · exact constantFrame .modulus (Or.inr (Or.inr rfl))
  · exact constantFrame .zero (Or.inr (Or.inl rfl))
  · exact constantFrame .one (Or.inl rfl)
  · exact constantFrame .modulus (Or.inr (Or.inr rfl))
  · exact constantFrame .zero (Or.inr (Or.inl rfl))
  · exact factorFrame .accepted
  · exact factorFrame .selected

end

end QuadraticRecoverySeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

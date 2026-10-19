/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index

/-!
# Reusable quadratic-recovery workspace inventory

The two ordered divisor checks run sequentially and therefore share one
compatible six-cell check footprint.  The persistent factor selector remains
caller-owned and is not duplicated here.  This module names the remaining
quadratic constants and scratch cells and proves that the heterogeneous
allocator gives an injective storage-key projection.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace QuadraticScratchLayout

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory

noncomputable section

/-- Raw short-log width entering the quadratic reconstruction. -/
abbrev ShortWidth (N : Nat) : Nat := LatticePairCandidateRecovery.Width N

/-- Center word width used by the quadratic prefix. -/
abbrev CenterWidth (N : Nat) : Nat :=
  QuadraticPrefix.centerWidth (ShortWidth N)

/-- Discriminant and public-modulus work width. -/
abbrev DiscriminantWidth (N : Nat) : Nat :=
  QuadraticPrefix.discriminantWidth (ShortWidth N)

/-- Internal natural-square-root word width. -/
abbrev WorkWidth (N : Nat) : Nat := NatSqrt.workWidth (DiscriminantWidth N)

/-- Width of both candidate factors and the persistent selector word. -/
abbrev CandidateWidth (N : Nat) : Nat :=
  QuadraticCandidateCheck.CandidateWidth (ShortWidth N)

/-- Every physical quadratic constant or mutable scratch cell. -/
inductive Cell where
  | modulus | one | zero
  | center | centerSquare | subtractLessThan | subtractOutput
  | sqrtWideInput | sqrtRoot | sqrtHalf | sqrtMidCarry | sqrtSquare
  | sqrtTooLarge | sqrtTake | sqrtOutput
  | centerWide | rootWide | firstLessThan | firstOutput | secondCandidate
  | greaterThanOne | candidateWide | belowModulus | division
  | modulusAccepted | eligible
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.modulus, .one, .zero,
      .center, .centerSquare, .subtractLessThan, .subtractOutput,
      .sqrtWideInput, .sqrtRoot, .sqrtHalf, .sqrtMidCarry, .sqrtSquare,
      .sqrtTooLarge, .sqrtTake, .sqrtOutput,
      .centerWide, .rootWide, .firstLessThan, .firstOutput, .secondCandidate,
      .greaterThanOne, .candidateWide, .belowModulus, .division,
      .modulusAccepted, .eligible]
    (by
      intro cell
      cases cell <;> simp)

/-- Stable heterogeneous allocation order of the quadratic package. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  [.unsignedWord (DiscriminantWidth N),
    .unsignedWord (CandidateWidth N), .unsignedWord (CandidateWidth N),
    .unsignedWord (CenterWidth N), .unsignedWord (DiscriminantWidth N), .bit,
    .unsignedWord (DiscriminantWidth N),
    .unsignedWord (WorkWidth N + WorkWidth N),
    .unsignedWord (WorkWidth N), .unsignedWord (WorkWidth N),
    .product (.unsignedWord (WorkWidth N)) .bit,
    .unsignedWord (WorkWidth N + WorkWidth N), .bit, .bit,
    .unsignedWord (WorkWidth N), .unsignedWord (CandidateWidth N),
    .unsignedWord (CandidateWidth N), .bit, .unsignedWord (CandidateWidth N),
    .product (.unsignedWord (CandidateWidth N)) .bit, .bit,
    .unsignedWord (DiscriminantWidth N), .bit,
    .product (.unsignedWord (DiscriminantWidth N))
      (.unsignedWord (CandidateWidth N)),
    .bit, .bit]

/-- Heterogeneous storage for the reusable quadratic package. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one named quadratic cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .modulus => ⟨0, by simp [shapes]⟩
  | .one => ⟨1, by simp [shapes]⟩
  | .zero => ⟨2, by simp [shapes]⟩
  | .center => ⟨3, by simp [shapes]⟩
  | .centerSquare => ⟨4, by simp [shapes]⟩
  | .subtractLessThan => ⟨5, by simp [shapes]⟩
  | .subtractOutput => ⟨6, by simp [shapes]⟩
  | .sqrtWideInput => ⟨7, by simp [shapes]⟩
  | .sqrtRoot => ⟨8, by simp [shapes]⟩
  | .sqrtHalf => ⟨9, by simp [shapes]⟩
  | .sqrtMidCarry => ⟨10, by simp [shapes]⟩
  | .sqrtSquare => ⟨11, by simp [shapes]⟩
  | .sqrtTooLarge => ⟨12, by simp [shapes]⟩
  | .sqrtTake => ⟨13, by simp [shapes]⟩
  | .sqrtOutput => ⟨14, by simp [shapes]⟩
  | .centerWide => ⟨15, by simp [shapes]⟩
  | .rootWide => ⟨16, by simp [shapes]⟩
  | .firstLessThan => ⟨17, by simp [shapes]⟩
  | .firstOutput => ⟨18, by simp [shapes]⟩
  | .secondCandidate => ⟨19, by simp [shapes]⟩
  | .greaterThanOne => ⟨20, by simp [shapes]⟩
  | .candidateWide => ⟨21, by simp [shapes]⟩
  | .belowModulus => ⟨22, by simp [shapes]⟩
  | .division => ⟨23, by simp [shapes]⟩
  | .modulusAccepted => ⟨24, by simp [shapes]⟩
  | .eligible => ⟨25, by simp [shapes]⟩

/-- Exact runtime shape of one named quadratic cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every named quadratic cell is workspace-owned. -/
lemma cellRef_role {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.role = .workspace := by
  exact (ClassicalWorkspace.cellAt cells (cellIndex N cell)).role

/-- The named reference and numeric layout index have the same physical key. -/
lemma cellRef_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :
    (cellRef cells cell).toCStorageRef.key =
      (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref.toCStorageRef.key := by
  rfl

private lemma cellIndex_zero_injective : Function.Injective (cellIndex 0) := by
  decide

private lemma cellIndex_val_eq (N M : Nat) (cell : Cell) :
    (cellIndex N cell).val = (cellIndex M cell).val := by
  cases cell <;> rfl

/-- The stable numeric index is injective on named cells. -/
lemma cellIndex_injective (N : Nat) : Function.Injective (cellIndex N) := by
  intro left right equal
  apply cellIndex_zero_injective
  apply Fin.ext
  calc
    (cellIndex 0 left).val = (cellIndex N left).val := cellIndex_val_eq 0 N left
    _ = (cellIndex N right).val := congrArg Fin.val equal
    _ = (cellIndex 0 right).val := cellIndex_val_eq N 0 right

/-- Distinct allocation cells give an injective named key projection. -/
lemma cellRef_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    Function.Injective (fun cell => (cellRef cells cell).toCStorageRef.key) := by
  intro left right equal
  apply cellIndex_injective N
  apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
  simpa only [cellRef_key] using equal

end

end QuadraticScratchLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

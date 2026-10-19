/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout

/-!
# Reused physical candidate-slot cells without classifier or selector scratch

The actual slot requires 32 caller-owned cells: 21 coordinate words, one modulus
word and ten bits. The shared native-power circuit owns its separate lexical
scope. No classifier word or first-success availability/take cells are allocated.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceLayout

open Execution

noncomputable section

/-- Original raw-word width shared by the lattice and short-log candidate machines. -/
abbrev Width (N : Nat) : Nat := LatticeWideLllMachine.Width N

/-- Every physical mutable cell in one reusable candidate slot. -/
inductive Cell where
  | offsetFirst
  | offsetSecond
  | offsetThird
  | coefficientFirst
  | coefficientSecond
  | coefficientThird
  | pointFirst
  | pointSecond
  | pointThird
  | pointProduct
  | differenceFirst
  | differenceSecond
  | differenceThird
  | squaredDistance
  | distanceProduct
  | scaledDistance
  | rangeSquare
  | scaledRange
  | nearAccepted
  | negative
  | magnitude
  | exponent
  | positive
  | belowUpper
  | nonnegative
  | exponentAccepted
  | power
  | powerAccepted
  | selectorIntermediate
  | selectorEligible
  | shortAccepted
  | shortSelected
deriving DecidableEq

instance : Fintype Cell :=
  Fintype.ofList
    [.offsetFirst,
      .offsetSecond,
      .offsetThird,
      .coefficientFirst,
      .coefficientSecond,
      .coefficientThird,
      .pointFirst,
      .pointSecond,
      .pointThird,
      .pointProduct,
      .differenceFirst,
      .differenceSecond,
      .differenceThird,
      .squaredDistance,
      .distanceProduct,
      .scaledDistance,
      .rangeSquare,
      .scaledRange,
      .nearAccepted,
      .negative,
      .magnitude,
      .exponent,
      .positive,
      .belowUpper,
      .nonnegative,
      .exponentAccepted,
      .power,
      .powerAccepted,
      .selectorIntermediate,
      .selectorEligible,
      .shortAccepted,
      .shortSelected]
    (by intro cell; cases cell <;> simp)

/-- Physical shape list parameterized independently of the algorithm width calculation. -/
private def shapesForWidths (coordinateWidth modulusWidth : Nat) : List CShape :=
  [.unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .bit,
    .bit,
    .unsignedWord coordinateWidth,
    .unsignedWord coordinateWidth,
    .bit,
    .bit,
    .bit,
    .bit,
    .unsignedWord modulusWidth,
    .bit,
    .bit,
    .bit,
    .bit,
    .unsignedWord coordinateWidth]

private lemma shapesForWidths_bitWidth_sum (coordinateWidth modulusWidth : Nat) :
    ((shapesForWidths coordinateWidth modulusWidth).map CShape.bitWidth).sum =
      21 * coordinateWidth + modulusWidth + 10 := by
  simp only [shapesForWidths, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    CShape.bitWidth]
  omega

/-- Original stable allocation order after eliminating the three obsolete scratch cells. -/
@[implicit_reducible] def shapes (N : Nat) : List CShape :=
  shapesForWidths (Width N) (modulusBits N)

/-- Exactly 32 physical caller-owned cells are allocated by the candidate-slot layout. -/
lemma shapes_length (N : Nat) : (shapes N).length = 32 := rfl

/-- Independent storage budget for the original words and actual remaining control bits. -/
def storageBits (N : Nat) : Nat := 21 * Width N + modulusBits N + 10

/-- The concrete heterogeneous shapes account for exactly the independent classical bit budget. -/
lemma shapes_bitWidth_sum (N : Nat) : ((shapes N).map CShape.bitWidth).sum = storageBits N := by
  exact shapesForWidths_bitWidth_sum (Width N) (modulusBits N)

/-- Typed actual references for the complete reusable physical candidate-slot layout. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Stable numeric index of one actual named cell. -/
@[implicit_reducible] def cellIndex (N : Nat) : Cell → Fin (shapes N).length
  | .offsetFirst => ⟨0, by rw [shapes_length]; omega⟩
  | .offsetSecond => ⟨1, by rw [shapes_length]; omega⟩
  | .offsetThird => ⟨2, by rw [shapes_length]; omega⟩
  | .coefficientFirst => ⟨3, by rw [shapes_length]; omega⟩
  | .coefficientSecond => ⟨4, by rw [shapes_length]; omega⟩
  | .coefficientThird => ⟨5, by rw [shapes_length]; omega⟩
  | .pointFirst => ⟨6, by rw [shapes_length]; omega⟩
  | .pointSecond => ⟨7, by rw [shapes_length]; omega⟩
  | .pointThird => ⟨8, by rw [shapes_length]; omega⟩
  | .pointProduct => ⟨9, by rw [shapes_length]; omega⟩
  | .differenceFirst => ⟨10, by rw [shapes_length]; omega⟩
  | .differenceSecond => ⟨11, by rw [shapes_length]; omega⟩
  | .differenceThird => ⟨12, by rw [shapes_length]; omega⟩
  | .squaredDistance => ⟨13, by rw [shapes_length]; omega⟩
  | .distanceProduct => ⟨14, by rw [shapes_length]; omega⟩
  | .scaledDistance => ⟨15, by rw [shapes_length]; omega⟩
  | .rangeSquare => ⟨16, by rw [shapes_length]; omega⟩
  | .scaledRange => ⟨17, by rw [shapes_length]; omega⟩
  | .nearAccepted => ⟨18, by rw [shapes_length]; omega⟩
  | .negative => ⟨19, by rw [shapes_length]; omega⟩
  | .magnitude => ⟨20, by rw [shapes_length]; omega⟩
  | .exponent => ⟨21, by rw [shapes_length]; omega⟩
  | .positive => ⟨22, by rw [shapes_length]; omega⟩
  | .belowUpper => ⟨23, by rw [shapes_length]; omega⟩
  | .nonnegative => ⟨24, by rw [shapes_length]; omega⟩
  | .exponentAccepted => ⟨25, by rw [shapes_length]; omega⟩
  | .power => ⟨26, by rw [shapes_length]; omega⟩
  | .powerAccepted => ⟨27, by rw [shapes_length]; omega⟩
  | .selectorIntermediate => ⟨28, by rw [shapes_length]; omega⟩
  | .selectorEligible => ⟨29, by rw [shapes_length]; omega⟩
  | .shortAccepted => ⟨30, by rw [shapes_length]; omega⟩
  | .shortSelected => ⟨31, by rw [shapes_length]; omega⟩

/-- Exact runtime shape of one candidate-slot cell. -/
@[implicit_reducible] def cellShape (N : Nat) (cell : Cell) : CShape :=
  (shapes N).get (cellIndex N cell)

/-- Resolve one named cell to its typed writable reference. -/
def cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) : CWriteRef ctx (cellShape N cell) :=
  (ClassicalWorkspace.cellAt cells (cellIndex N cell)).ref

/-- Every named candidate-slot cell is workspace-owned. -/
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

/-- Distinct allocation cells give an injective named storage-key projection. -/
lemma cellRef_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    Function.Injective (fun cell => (cellRef cells cell).toCStorageRef.key) := by
  intro left right equal
  apply cellIndex_injective N
  apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
  simpa only [cellRef_key] using equal

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSlotWorkspaceLayout

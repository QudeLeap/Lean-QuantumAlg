/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Actual fresh feedback cells for a recycled point sampler

The heterogeneous layout contains one output cell per measured result bit,
one packed mask, a finite family of parity bits and one temporary bit.
Distinctness follows from the actual allocator's cells, including cells
with identical classical shapes. No initial scratch values are assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

open Execution ClassicalWorkspace

/-- Output cells, packed mask, parity cells and temporary cell in one real scope. -/
def cellCount (wordWidth parityCount : Nat) : Nat := wordWidth + parityCount + 2

def cellShape (wordWidth parityCount : Nat) (index : Fin (cellCount wordWidth parityCount)) :
    CShape :=
  if index.val < wordWidth then .finite 2
  else if index.val = wordWidth then .bits wordWidth else .bit

def shapes (wordWidth parityCount : Nat) : List CShape :=
  List.ofFn (cellShape wordWidth parityCount)

private def outputIndex (wordWidth parityCount : Nat) (index : Fin wordWidth) :
    Fin (cellCount wordWidth parityCount) := ⟨index.val, by unfold cellCount; omega⟩

private def maskIndex (wordWidth parityCount : Nat) :
    Fin (cellCount wordWidth parityCount) := ⟨wordWidth, by unfold cellCount; omega⟩

private def parityIndex (wordWidth parityCount : Nat) (index : Fin parityCount) :
    Fin (cellCount wordWidth parityCount) :=
  ⟨wordWidth + 1 + index.val, by unfold cellCount; omega⟩

private def temporaryIndex (wordWidth parityCount : Nat) :
    Fin (cellCount wordWidth parityCount) :=
  ⟨wordWidth + 1 + parityCount, by unfold cellCount; omega⟩

private def listedIndex {count : Nat} (shape : Fin count → CShape) (index : Fin count) :
    Fin (List.ofFn shape).length := Fin.cast (by simp) index

private lemma castCell_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first second : CShape} (same : first = second) (cell : Cell ctx first) :
    (same ▸ cell).ref.key = cell.ref.key := by
  cases same
  rfl

private lemma refAt_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {count : Nat}
    (shape : Fin count → CShape) (cells : Cells ctx (List.ofFn shape)) (index : Fin count) :
    (refAt shape cells index).key =
      (cellAt cells (listedIndex shape index)).ref.key := by
  dsimp only [refAt, cellAtOfFn, listedIndex]
  rw [castCell_key]

private lemma refAt_key_injective {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {count : Nat} (shape : Fin count → CShape) (cells : Cells ctx (List.ofFn shape))
    (distinct : cells.Distinct) :
    Function.Injective (fun index => (refAt shape cells index).key) := by
  intro first second same
  have indices := workspaceCells_cellAt_key_injective cells distinct
    ((refAt_key shape cells first).symm.trans (same.trans (refAt_key shape cells second)))
  have values := congrArg (fun index : Fin (List.ofFn shape).length => index.val) indices
  exact Fin.ext values

private def castWrite {kind : ProblemKind} {ctx : RuntimeCtx kind} {first second : CShape}
    (same : first = second) (ref : CWriteRef ctx first) : CWriteRef ctx second := same ▸ ref

private lemma castWrite_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first second : CShape} (same : first = second) (ref : CWriteRef ctx first) :
    (castWrite same ref).key = ref.key := by
  cases same
  rfl

/-- These same-shaped key laws are supplied by actual fresh allocation. -/
structure Frame {kind : ProblemKind} (ctx : RuntimeCtx kind) (wordWidth parityCount : Nat) where
  output : Fin wordWidth → CWriteRef ctx (.finite 2)
  mask : CWriteRef ctx (.bits wordWidth)
  parity : Fin parityCount → CWriteRef ctx .bit
  temporary : CWriteRef ctx .bit
  outputDistinct : Function.Injective (fun index => (output index).key)
  parityDistinct : Function.Injective (fun index => (parity index).key)
  temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key

namespace Frame

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {wordWidth parityCount : Nat}

private def outputOfCells (cells : Cells ctx (shapes wordWidth parityCount))
    (index : Fin wordWidth) : CWriteRef ctx (.finite 2) :=
  castWrite (by simp [cellShape, outputIndex, index.isLt])
    (refAt (cellShape wordWidth parityCount) cells
      (outputIndex wordWidth parityCount index))

private def maskOfCells (cells : Cells ctx (shapes wordWidth parityCount)) :
    CWriteRef ctx (.bits wordWidth) :=
  castWrite (by simp [cellShape, maskIndex])
    (refAt (cellShape wordWidth parityCount) cells (maskIndex wordWidth parityCount))

private def parityOfCells (cells : Cells ctx (shapes wordWidth parityCount))
    (index : Fin parityCount) : CWriteRef ctx .bit :=
  castWrite (by simp [cellShape, parityIndex, show ¬wordWidth + 1 + index.val < wordWidth by omega,
    show wordWidth + 1 + index.val ≠ wordWidth by omega])
    (refAt (cellShape wordWidth parityCount) cells
      (parityIndex wordWidth parityCount index))

private def temporaryOfCells (cells : Cells ctx (shapes wordWidth parityCount)) :
    CWriteRef ctx .bit :=
  castWrite (by simp [cellShape, temporaryIndex,
    show ¬wordWidth + 1 + parityCount < wordWidth by omega,
    show wordWidth + 1 + parityCount ≠ wordWidth by omega])
    (refAt (cellShape wordWidth parityCount) cells (temporaryIndex wordWidth parityCount))

/-- Read the literal allocated cells; no existing caller scratch is accepted or ignored. -/
def ofCells (cells : Cells ctx (shapes wordWidth parityCount)) (distinct : cells.Distinct) :
    Frame ctx wordWidth parityCount where
  output := outputOfCells cells
  mask := maskOfCells cells
  parity := parityOfCells cells
  temporary := temporaryOfCells cells
  outputDistinct := by
    intro first second same
    simp only [outputOfCells, castWrite_key] at same
    have indices := refAt_key_injective (cellShape wordWidth parityCount) cells distinct same
    have values := congrArg
      (fun index : Fin (cellCount wordWidth parityCount) => index.val) indices
    exact Fin.ext values
  parityDistinct := by
    intro first second same
    simp only [parityOfCells, castWrite_key] at same
    have indices := refAt_key_injective (cellShape wordWidth parityCount) cells distinct same
    have values := congrArg Fin.val indices
    apply Fin.ext
    change wordWidth + 1 + first.val = wordWidth + 1 + second.val at values
    omega
  temporaryDifferent := by
    intro index same
    simp only [parityOfCells, temporaryOfCells, castWrite_key] at same
    have indices := refAt_key_injective (cellShape wordWidth parityCount) cells distinct same
    have values := congrArg Fin.val indices
    change wordWidth + 1 + index.val = wordWidth + 1 + parityCount at values
    have within := index.isLt
    omega

end Frame

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

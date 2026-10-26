/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Frame
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Frame

/-!
# Fresh five-array windows over the same persistent four-word frame

The window arrays are actual heterogeneous workspace cells. Freshness
separates all five from the complete caller reads, while the persistent
frame's physical distinctness protects the constants and small-base rows
from each of the same four scalar overwrites.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace

/-- Only the five large arrays have the shorter per-window lexical lifetime. -/
def tableShapes (width length : Nat) : List CShape :=
  List.replicate 5 (.fixedVector length (.unsignedWord width))

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- The five actual allocated cells in their original X/Y/C/D/E order. -/
def arraysOfCells (cells : Cells ctx (tableShapes width length))
    (distinct : cells.Distinct) : Arrays ctx width length := by
  have unique := Cells.workspaceCells_distinct_keys_nodup cells distinct
  cases cells with
  | cons x rest =>
    cases rest with
    | cons y rest =>
      cases rest with
      | cons c rest =>
        cases rest with
        | cons d rest =>
          cases rest with
          | cons e rest =>
            cases rest
            exact ⟨x.ref, y.ref, c.ref, d.ref, e.ref, unique⟩

/-- The actual five-array key list is exactly the allocated package's key list. -/
lemma arraysOfCells_keys (cells : Cells ctx (tableShapes width length))
    (distinct : cells.Distinct) :
    let arrays := arraysOfCells cells distinct
    [arrays.x.key, arrays.y.key, arrays.c.key, arrays.d.key, arrays.e.key] = cells.keys := by
  cases cells with
  | cons x rest =>
    cases rest with
    | cons y rest =>
      cases rest with
      | cons c rest =>
        cases rest with
        | cons d rest =>
          cases rest with
          | cons e rest =>
            cases rest
            rfl

namespace Frame

variable (frame : Frame ctx width)

/-- Every original table input is protected from the same four persistent scalar outputs. -/
lemma work_protectedReads (row : Fin 34)
    (input : CInputRef ctx (.unsignedWord width))
    (selected : input ∈ [.storage frame.zero.toCStorageRef,
      .storage frame.one.toCStorageRef, .storage frame.curveA.toCStorageRef,
      rowRead frame.x row, rowRead frame.y row])
    (key : StorageKey)
    (written : key ∈ [frame.product.key, frame.inverse.key,
      frame.temporary.key, frame.slope.key]) : key ∉ input.storageKeys := by
  have separate : List.Disjoint
      [frame.product.key, frame.inverse.key, frame.temporary.key, frame.slope.key]
      [frame.modulus.key, frame.zero.key, frame.one.key, frame.curveA.key,
        frame.x.key, frame.y.key] :=
    List.disjoint_of_nodup_append frame.distinct
  have supported : input.storageKeys ⊆
      [frame.modulus.key, frame.zero.key, frame.one.key, frame.curveA.key,
        frame.x.key, frame.y.key] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    rcases selected with rfl | rfl | rfl | rfl | rfl
    all_goals simp [rowRead, CInputRef.storageKeys]
  exact fun member => List.disjoint_left.mp separate written (supported member)

/-- Build the window frame from real fresh arrays and structurally retained base rows. -/
def tableFrame {inner : RuntimeCtx kind} (lift : Transport ctx inner)
    (cells : Cells inner (tableShapes width length)) (distinct : cells.Distinct)
    (separated : cells.TransportSeparated lift) (row : Fin 34) :
    TableFrame inner width length where
  arrays := arraysOfCells cells distinct
  work := (frame.transport lift).work
  modulus := lift.liftWrite frame.modulus
  zero := lift.liftInput (.storage frame.zero.toCStorageRef)
  one := lift.liftInput (.storage frame.one.toCStorageRef)
  curveA := lift.liftInput (.storage frame.curveA.toCStorageRef)
  baseX := lift.liftInput (rowRead frame.x row)
  baseY := lift.liftInput (rowRead frame.y row)
  protectedReads := by
    intro input selected key written
    have inputSelected : ∃ original ∈ [.storage frame.zero.toCStorageRef,
        .storage frame.one.toCStorageRef, .storage frame.curveA.toCStorageRef,
        rowRead frame.x row, rowRead frame.y row], input = lift.liftInput original := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
      rcases selected with rfl | rfl | rfl | rfl | rfl
      all_goals exact ⟨_, by simp, rfl⟩
    rcases inputSelected with ⟨original, originalSelected, rfl⟩
    have writes : key ∈
        [((arraysOfCells cells distinct).x).key, ((arraysOfCells cells distinct).y).key,
          ((arraysOfCells cells distinct).c).key, ((arraysOfCells cells distinct).d).key,
          ((arraysOfCells cells distinct).e).key] ++
          [frame.product.key, frame.inverse.key, frame.temporary.key, frame.slope.key] := by
      simpa only [transport, work, Transport.liftWrite_key,
        List.cons_append, List.nil_append] using written
    rcases List.mem_append.mp writes with fresh | persistent
    · rw [arraysOfCells_keys] at fresh
      exact Cells.workspaceCells_transportSeparated_avoids_of_mem
        cells lift separated fresh original
    · rw [Transport.liftInput_storageKeys]
      exact frame.work_protectedReads row original originalSelected key persistent

end Frame

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Indexed.Values
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package

/-!
# Actual persistent storage of one paired-base window schedule

The literal allocation contains exactly four scalar working words, one
shared widened modulus, the zero/one/curve words, and two coordinate arrays
of length thirty-four. The arrays hold both seventeen-row base families.
The five large window arrays have separate shorter lexical lifetimes.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace

/-- Exactly four work words, four shared constants and two small coordinate arrays. -/
def sharedShapes (width : Nat) : List CShape :=
  [.unsignedWord width, .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord (width + 1), .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .fixedVector 34 (.unsignedWord width), .fixedVector 34 (.unsignedWord width)]

/-- References to those actual ten persistent cells, with their physical key separation. -/
structure Frame {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  product : CWriteRef ctx (.unsignedWord width)
  inverse : CWriteRef ctx (.unsignedWord width)
  temporary : CWriteRef ctx (.unsignedWord width)
  slope : CWriteRef ctx (.unsignedWord width)
  modulus : CWriteRef ctx (.unsignedWord (width + 1))
  zero : CWriteRef ctx (.unsignedWord width)
  one : CWriteRef ctx (.unsignedWord width)
  curveA : CWriteRef ctx (.unsignedWord width)
  x : CWriteRef ctx (.fixedVector 34 (.unsignedWord width))
  y : CWriteRef ctx (.fixedVector 34 (.unsignedWord width))
  distinct : [product.key, inverse.key, temporary.key, slope.key, modulus.key,
    zero.key, one.key, curveA.key, x.key, y.key].Nodup

namespace Frame

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual lexical allocation establishes every persistent physical separation. -/
def ofCells (cells : Cells ctx (sharedShapes width)) (distinct : cells.Distinct) :
    Frame ctx width := by
  have unique := Cells.workspaceCells_distinct_keys_nodup cells distinct
  cases cells with
  | cons product rest =>
    cases rest with
    | cons inverse rest =>
      cases rest with
      | cons temporary rest =>
        cases rest with
        | cons slope rest =>
          cases rest with
          | cons modulus rest =>
            cases rest with
            | cons zero rest =>
              cases rest with
              | cons one rest =>
                cases rest with
                | cons curveA rest =>
                  cases rest with
                  | cons x rest =>
                    cases rest with
                    | cons y rest =>
                      cases rest
                      exact {
                        product := product.ref
                        inverse := inverse.ref
                        temporary := temporary.ref
                        slope := slope.ref
                        modulus := modulus.ref
                        zero := zero.ref
                        one := one.ref
                        curveA := curveA.ref
                        x := x.ref
                        y := y.ref
                        distinct := unique
                      }

variable (frame : Frame ctx width)

/-- Literal allocation order of the same actual persistent keys. -/
def keyAt : Fin 10 → StorageKey :=
  ![frame.product.key, frame.inverse.key, frame.temporary.key, frame.slope.key,
    frame.modulus.key, frame.zero.key, frame.one.key, frame.curveA.key, frame.x.key, frame.y.key]

/-- Every persistent cell has its own actual storage key. -/
lemma keyAt_injective : Function.Injective frame.keyAt := by
  apply List.nodup_ofFn.mp
  simpa only [keyAt, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ] using frame.distinct

/-- Different declared persistent cells cannot alias through any of their typed references. -/
lemma keyAt_ne (first second : Fin 10) (different : first ≠ second) :
    frame.keyAt first ≠ frame.keyAt second := fun same => different (frame.keyAt_injective same)

/-- The builder and small-base preparation share these same four actual scalar words. -/
def work : Work ctx width where
  product := frame.product
  inverse := frame.inverse
  temporary := frame.temporary
  slope := frame.slope
  distinct := List.Nodup.of_append_left (l₂ :=
    [frame.modulus.key, frame.zero.key, frame.one.key, frame.curveA.key, frame.x.key, frame.y.key])
    frame.distinct

/-- Both original point families occupy the same two real arrays of length thirty-four. -/
def coordinates : CoordinateFrame ctx width 34 where
  x := frame.x
  y := frame.y
  separate := frame.keyAt_ne 8 9 (by decide)
  work := frame.work
  modulus := frame.modulus
  curveA := .storage frame.curveA.toCStorageRef
  protectedCoefficient := by
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change _ ∉ [frame.curveA.key]
      first
        | simpa [keyAt, work] using frame.keyAt_ne 8 7 (by decide)
        | simpa [keyAt, work] using frame.keyAt_ne 9 7 (by decide)
        | simpa [keyAt, work] using frame.keyAt_ne 0 7 (by decide)
        | simpa [keyAt, work] using frame.keyAt_ne 1 7 (by decide)
        | simpa [keyAt, work] using frame.keyAt_ne 2 7 (by decide)
        | simpa [keyAt, work] using frame.keyAt_ne 3 7 (by decide)

/-- Further lexical allocation preserves every original physical reference and its separation. -/
def transport {inner : RuntimeCtx kind} (lift : Transport ctx inner) : Frame inner width where
  product := lift.liftWrite frame.product
  inverse := lift.liftWrite frame.inverse
  temporary := lift.liftWrite frame.temporary
  slope := lift.liftWrite frame.slope
  modulus := lift.liftWrite frame.modulus
  zero := lift.liftWrite frame.zero
  one := lift.liftWrite frame.one
  curveA := lift.liftWrite frame.curveA
  x := lift.liftWrite frame.x
  y := lift.liftWrite frame.y
  distinct := by simpa only [Transport.liftWrite_key] using frame.distinct

end Frame

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

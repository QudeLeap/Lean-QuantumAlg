/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual five-array table frame and four scalar working words

The arrays are caller-supplied existing storage. During construction X/Y
hold coordinates, C holds denominators and their inverses, and D holds
prefix products. The final five columns are -x, -y, 3x, the negative
exceptional slope and x+1. No additional complete prefix array is allocated.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Five physical classical array cells reused across all construction phases. -/
structure Arrays (ctx : RuntimeCtx kind) (width length : Nat) where
  x : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  y : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  c : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  d : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  e : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  distinct : [x.key, y.key, c.key, d.key, e.key].Nodup

/-- Exactly four persistent scalar words; arithmetic scratch has its own lexical lifetime. -/
structure Work (ctx : RuntimeCtx kind) (width : Nat) where
  product : CWriteRef ctx (.unsignedWord width)
  inverse : CWriteRef ctx (.unsignedWord width)
  temporary : CWriteRef ctx (.unsignedWord width)
  slope : CWriteRef ctx (.unsignedWord width)
  distinct : [product.key, inverse.key, temporary.key, slope.key].Nodup

/-- Read the original array entry structurally at a statically valid row. -/
def rowRead (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) : CInputRef ctx (.unsignedWord width) :=
  .vectorGet (.storage array.toCStorageRef) index

/-- One paid native row overwrite retains every other element of the same real array. -/
def rowWriteOp (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (value : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.fixedVector length (.unsignedWord width)) (.unsignedWord width))
      (.fixedVector length (.unsignedWord width)) ctx ctx :=
  .vectorWrite length width index ctx (.product (.storage array.toCStorageRef) value) array

/-- The source C and scratch D arrays of one in-place prefix/reverse batch. -/
structure BatchFrame (ctx : RuntimeCtx kind) (width length : Nat) where
  denominators : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  prefixes : CWriteRef ctx (.fixedVector length (.unsignedWord width))
  work : Work ctx width
  modulus : CInputRef ctx (.unsignedWord (width + 1))
  one : CInputRef ctx (.unsignedWord width)
  separate : denominators.key ≠ prefixes.key

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

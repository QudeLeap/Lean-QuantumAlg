/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Circuit
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual loading of the retained GF(2) sample matrix

Each row retains the original self-XOR clear, big-endian terminal decoder and
vector write. One fresh word is allocated and released for each row, so the
same lexical key is reused in the ordered sequence. The caller's matrix is
the actual destination; no mathematical evaluation chooses an instruction.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original real self-XOR instruction before decoding a row. -/
def rowClearOp (loader : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitXor width ctx
    (.product (.storage loader.toCStorageRef) (.storage loader.toCStorageRef)) loader

/-- The actual decoded word is written into its original statically selected matrix row. -/
def rowWriteOp (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.fixedVector rowCount (.unsignedWord width)) (.unsignedWord width))
      (.fixedVector rowCount (.unsignedWord width)) ctx ctx :=
  .vectorWrite rowCount width row ctx
    (.product (.storage matrix.toCStorageRef) (.storage loader.toCStorageRef)) matrix

/-- The three original stages run on the same real matrix and decoded word. -/
def rowBody (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (rowClearOp loader))
    (.seq (TerminalDecode.into .bigEndian input loader) (.classical (rowWriteOp row matrix loader)))

/-- The single actual temporary word used during a row's decoding. -/
@[reducible] def rowContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The fresh decoding cell is consumed before its lexical scope ends. -/
def rowCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (rowContext ctx width) (.unsignedWord width) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh

/-- The source row and matrix are lifted without changing any original key. -/
def placedRow (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount) :
    Circuit (rowContext ctx width) (rowContext ctx width) :=
  rowBody ((CInputRef.vectorGet input row).underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh) row
    (matrix.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (rowCell ctx width)

/-- Allocate the one temporary word, execute the original row stages, then release it. -/
def loadRow (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (placedRow input matrix row)

/-- Increasing row order reuses the same one-word lexical scope across the complete matrix. -/
def loadMatrix (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) : Circuit ctx ctx :=
  Circuit.forRange rowCount (loadRow input matrix)

end QuantumAlg.ClassicalRoutines.GF2.Native

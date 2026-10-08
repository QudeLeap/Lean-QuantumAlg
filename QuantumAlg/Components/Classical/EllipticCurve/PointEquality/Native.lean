/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Model
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Actual native comparison of complete point codes

The original eight operations unpack both points, compare their tags and both
coordinate words, and conjoin the results. Five actual lexical cells contain
the two raw points and three Boolean intermediates. Their allocation and
release belong to the existing Circuit interpreter.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exactly the two unpacked points and three Boolean intermediates stay live. -/
def scratchShapes (width : Nat) : List CShape :=
  [RawPointShape width, RawPointShape width, .bit, .bit, .bit]

/-- Actual typed references to the five internally allocated cells. -/
structure Scratch (ctx : RuntimeCtx kind) (width : Nat) where
  leftRaw : CWriteRef ctx (RawPointShape width)
  rightRaw : CWriteRef ctx (RawPointShape width)
  tag : CWriteRef ctx .bit
  x : CWriteRef ctx .bit
  y : CWriteRef ctx .bit

/-- The actual heterogeneous allocation supplies all scratch references. -/
def scratchOfCells (cells : Cells ctx (scratchShapes width)) : Scratch ctx width :=
  ⟨cells.head.ref, cells.tail.head.ref, cells.tail.tail.head.ref,
    cells.tail.tail.tail.head.ref, cells.tail.tail.tail.tail.head.ref⟩

/-- Read the same actual writable storage cell. -/
def read {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Materialize the first complete nominal point in its raw scratch cell. -/
def unpackLeft (left : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width) :
    ClassicalOp (PointShape width) (RawPointShape width) ctx ctx :=
  .unpackEllipticCurvePoint width ctx left scratch.leftRaw

/-- Materialize the second complete point before any caller output is written. -/
def unpackRight (right : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width) :
    ClassicalOp (PointShape width) (RawPointShape width) ctx ctx :=
  .unpackEllipticCurvePoint width ctx right scratch.rightRaw

/-- Compare infinity tags with the original native xor. -/
def tagXor (scratch : Scratch ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (.first (read scratch.leftRaw))
    (.first (read scratch.rightRaw))) scratch.tag

/-- Negating that actual xor yields tag equality. -/
def tagNot (scratch : Scratch ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (read scratch.tag) scratch.tag

/-- The original unsigned word equality compares both X coordinates. -/
def equalX (scratch : Scratch ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.first (.second (read scratch.leftRaw)))
      (.first (.second (read scratch.rightRaw)))) scratch.x

/-- The original unsigned word equality compares both Y coordinates. -/
def equalY (scratch : Scratch ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.second (.second (read scratch.leftRaw)))
      (.second (.second (read scratch.rightRaw)))) scratch.y

/-- Reuse the X scratch for the coordinate conjunction. -/
def coordinateAnd (scratch : Scratch ctx width) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (read scratch.x) (read scratch.y)) scratch.x

/-- The final native conjunction writes the supplied actual Boolean destination. -/
def outputAnd (scratch : Scratch ctx width) (output : CWriteRef ctx .bit) :
    ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (read scratch.tag) (read scratch.x)) output

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Each indexed stage is one of the original eight actual instructions. -/
def stage (left right : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width)
    (output : CWriteRef ctx .bit) : Fin 8 → Circuit model ctx ctx :=
  ![BitWord.instruction (execution := model) (unpackLeft left scratch),
    BitWord.instruction (execution := model) (unpackRight right scratch),
    BitWord.instruction (execution := model) (tagXor scratch),
    BitWord.instruction (execution := model) (tagNot scratch),
    BitWord.instruction (execution := model) (equalX scratch),
    BitWord.instruction (execution := model) (equalY scratch),
    BitWord.instruction (execution := model) (coordinateAnd scratch),
    BitWord.instruction (execution := model) (outputAnd scratch output)]

/-- The original ordered eight-stage comparison uses the actual circuit composition. -/
def core (left right : CInputRef ctx (PointShape width)) (scratch : Scratch ctx width)
    (output : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  Circuit.forRange 8 (stage left right scratch output)

/-- Allocate the complete original workspace, execute the comparator and release that workspace. -/
def compareInto (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  withCells ctx (scratchShapes width) fun cells _distinct transport _separated =>
    core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native

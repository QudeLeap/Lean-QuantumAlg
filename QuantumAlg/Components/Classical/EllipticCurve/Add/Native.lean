/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Model
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Native complete-addition classification and branch selection

Two actual point adapters and three actual unsigned comparisons establish the
original affine branch predicates. The following branch tree reads only those
stored values. Finite formula arms remain ordinary supplied circuits; this
module makes no correctness claim for an unimplemented field operation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Both complete raw points, three predicates and the original allocated zero word. -/
def classifierShapes (width : Nat) : List CShape :=
  [PointEquality.RawPointShape width, PointEquality.RawPointShape width,
    .bit, .bit, .unsignedWord width, .bit]

/-- Structural references to the actual complete-addition classifier cells. -/
structure Classifier (ctx : RuntimeCtx kind) (width : Nat) where
  leftRaw : CWriteRef ctx (PointEquality.RawPointShape width)
  rightRaw : CWriteRef ctx (PointEquality.RawPointShape width)
  xEqual : CWriteRef ctx .bit
  yEqual : CWriteRef ctx .bit
  zero : CWriteRef ctx (.unsignedWord width)
  yZero : CWriteRef ctx .bit

/-- The internally allocated cells retain their exact shapes and original logical roles. -/
def classifierOfCells (cells : Cells ctx (classifierShapes width)) : Classifier ctx width :=
  ⟨cells.head.ref, cells.tail.head.ref, cells.tail.tail.head.ref,
    cells.tail.tail.tail.head.ref, cells.tail.tail.tail.tail.head.ref,
    cells.tail.tail.tail.tail.tail.head.ref⟩

/-- A structural read of the same actual writable cell. -/
def classifierRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- The original left nominal point adapter writes its full tag and two coordinate words. -/
def classifierUnpackLeft (left : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) :
    ClassicalOp (PointShape width) (PointEquality.RawPointShape width) ctx ctx :=
  .unpackEllipticCurvePoint width ctx left classifier.leftRaw

/-- The original right adapter snapshots the second full nominal point. -/
def classifierUnpackRight (right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) :
    ClassicalOp (PointShape width) (PointEquality.RawPointShape width) ctx ctx :=
  .unpackEllipticCurvePoint width ctx right classifier.rightRaw

/-- Actual unsigned comparison of the two stored X coordinates. -/
def classifierEqualX (classifier : Classifier ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.first (.second (classifierRead classifier.leftRaw)))
      (.first (.second (classifierRead classifier.rightRaw)))) classifier.xEqual

/-- Actual unsigned comparison of the two stored Y coordinates. -/
def classifierEqualY (classifier : Classifier ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.second (.second (classifierRead classifier.leftRaw)))
      (.second (.second (classifierRead classifier.rightRaw)))) classifier.yEqual

/-- Actual comparison of the left Y coordinate with the internally allocated zero word. -/
def classifierZeroY (classifier : Classifier ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.second (.second (classifierRead classifier.leftRaw)))
      (classifierRead classifier.zero)) classifier.yZero

/-- The original five operations occur before any branch is selected. -/
def classifierStage (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) : Fin 5 → Circuit ctx ctx :=
  ![.classical (classifierUnpackLeft left classifier),
    .classical (classifierUnpackRight right classifier),
    .classical (classifierEqualX classifier), .classical (classifierEqualY classifier),
    .classical (classifierZeroY classifier)]

/-- Native classification has precisely the original two-adapter, three-comparison order. -/
def classifierBody (left right : CInputRef ctx (PointShape width))
    (classifier : Classifier ctx width) : Circuit ctx ctx :=
  Circuit.forRange 5 (classifierStage left right classifier)

/-- The complete runtime arms distinguished by the original affine classifier. -/
inductive Case where
  | leftInfinity
  | rightInfinity
  | vertical
  | doubling
  | generic
  deriving DecidableEq

/-- The original complete case distinction on nominal tag and coordinate values. -/
def classifyValues (left right : CShape.Value (PointShape width)) : Case :=
  if left.ellipticCurvePointInfinityTag then .leftInfinity
  else if right.ellipticCurvePointInfinityTag then .rightInfinity
  else if left.ellipticCurvePointX = right.ellipticCurvePointX then
    if left.ellipticCurvePointY = right.ellipticCurvePointY then
      if left.ellipticCurvePointY = 0 then .vertical else .doubling
    else .vertical
  else .generic

/-- Branch on one actual stored bit through the existing shaped branch instruction. -/
def classifierBranch (input : CInputRef ctx .bit)
    (whenTrue whenFalse : Circuit ctx ctx) : Circuit ctx ctx :=
  .branch input fun value => if value.toBool then whenTrue else whenFalse

/-- The complete original branch order reads the live classifier, including all infinity cases. -/
def dispatch (classifier : Classifier ctx width) (arms : Case → Circuit ctx ctx) :
    Circuit ctx ctx :=
  classifierBranch (.first (classifierRead classifier.leftRaw)) (arms .leftInfinity)
    (classifierBranch (.first (classifierRead classifier.rightRaw)) (arms .rightInfinity)
      (classifierBranch (classifierRead classifier.xEqual)
        (classifierBranch (classifierRead classifier.yEqual)
          (classifierBranch (classifierRead classifier.yZero) (arms .vertical) (arms .doubling))
          (arms .vertical)) (arms .generic)))

/-- Allocate the original classifier and execute the supplied ordinary circuit continuation. -/
def withClassification (left right : CInputRef ctx (PointShape width))
    (body : ∀ {inner : RuntimeCtx kind}, Classifier inner width →
      Transport ctx inner → Circuit inner inner) : Circuit ctx ctx :=
  withCells ctx (classifierShapes width) fun cells _ transport _ =>
    .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
      (classifierOfCells cells)) (body (classifierOfCells cells) transport)

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

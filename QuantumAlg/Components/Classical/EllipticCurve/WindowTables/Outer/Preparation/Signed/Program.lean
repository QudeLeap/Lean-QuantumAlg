/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub
import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Paid signed-row preparation from borrowed nominal points

This module contains the literal circuit prefix. Its Store and table-value
semantics are proved separately from the construction, before it is connected
to the complete calling run.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalAlgorithms.Modular

noncomputable section

/-- Two real raw point cells and one real signed-coordinate output cell. -/
def scratchShapes (width : Nat) : List CShape :=
  [PointEquality.RawPointShape width, PointEquality.RawPointShape width,
    .unsignedWord width]

structure Scratch {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  rawBase : CWriteRef ctx (PointEquality.RawPointShape width)
  rawTarget : CWriteRef ctx (PointEquality.RawPointShape width)
  signedY : CWriteRef ctx (.unsignedWord width)

/-- The lexical allocation fixes all three destinations without loading data. -/
def scratchOfCells {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (cells : Cells ctx (scratchShapes width)) : Scratch ctx width :=
  ⟨cells.head.ref, cells.tail.head.ref, cells.tail.tail.head.ref⟩

/-- Structural X projection of an actually unpacked raw point. -/
def rawX {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (raw : CWriteRef ctx (PointEquality.RawPointShape width)) :
    CInputRef ctx (.unsignedWord width) :=
  .first (.second (.storage raw.toCStorageRef))

/-- Structural Y projection of an actually unpacked raw point. -/
def rawY {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (raw : CWriteRef ctx (PointEquality.RawPointShape width)) :
    CInputRef ctx (.unsignedWord width) :=
  .second (.second (.storage raw.toCStorageRef))

/-- The three newly allocated destinations cannot alias any original caller read. -/
lemma scratch_avoids_original {kind : ProblemKind} {outer inner : RuntimeCtx kind} {width : Nat}
    (lift : Transport outer inner) (cells : Cells inner (scratchShapes width))
    (separated : cells.TransportSeparated lift)
    {shape : CShape} (input : CInputRef outer shape) :
    let scratch := scratchOfCells cells
    scratch.rawBase.key ∉ (lift.liftInput input).storageKeys ∧
      scratch.rawTarget.key ∉ (lift.liftInput input).storageKeys ∧
      scratch.signedY.key ∉ (lift.liftInput input).storageKeys := by
  cases cells with
  | cons rawBase rest =>
    cases rest with
    | cons rawTarget rest =>
      cases rest with
      | cons signedY rest =>
        exact ⟨separated.1 input, separated.2.1 input, separated.2.2.1 input⟩

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual initialize/unpack/subtract/base-table sequence. The target nominal
cell remains a caller input; the second table family reads only the newly
computed signed Y word. All three scratch cells are released afterward. -/
def prepare (frame : WindowTables.Outer.Frame ctx width)
    (spec : ModulusSpec width) (coefficient : Nat)
    (base target : CInputRef ctx (PointShape width)) : Circuit model ctx ctx :=
  .seq (frame.initializeConstants spec coefficient)
    (withCells (model := model) ctx (scratchShapes width) fun
      {inner} cells _ lift _ =>
        let scratch := scratchOfCells cells
        let localFrame := frame.transport lift
        .seq
          (BitWord.instruction (execution := model)
            (.unpackEllipticCurvePoint width inner (lift.liftInput base) scratch.rawBase))
          (.seq
            (BitWord.instruction (execution := model)
              (.unpackEllipticCurvePoint width inner (lift.liftInput target) scratch.rawTarget))
            (.seq
              (Field.Native.subIntoWord spec
                (.storage localFrame.zero.toCStorageRef)
                (rawY scratch.rawTarget) scratch.signedY)
              (localFrame.preparePairedBases spec
                (rawX scratch.rawBase) (rawY scratch.rawBase)
                (rawX scratch.rawTarget)
                (.storage scratch.signedY.toCStorageRef)))))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing

/-!
# Original public XGCD body through actual raw-result storage

Three real raw-result cells are allocated in the original gcd, left and right
order. The shared raw engine runs before the original five packing operations.
All three raw cells are released, while the caller's public result remains live.
The outer retained-result allocation is a separate entry boundary.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Deepest-first shape order retains original gcd, left and right allocation order. -/
def publicRawShapes (width : Nat) : List CShape :=
  [.unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width), .unsignedWord width]

/-- Actual raw-result references preserve the original three output roles. -/
def publicRawOutputs (cells : Cells ctx (publicRawShapes width)) : RawOutputs ctx width where
  gcd := cells.tail.tail.head.ref
  leftCoefficient := cells.tail.head.ref
  rightCoefficient := cells.head.ref

/-- Fresh actual raw-result cells provide all output distinctness required by the shared engine. -/
lemma xgcdNativePublicRawOutputs_distinct (cells : Cells ctx (publicRawShapes width))
    (distinct : cells.Distinct) : (publicRawOutputs cells).Distinct := by
  cases cells with
  | cons right rest =>
    cases rest with
    | cons left rest =>
      cases rest with
      | cons gcd rest =>
        cases rest
        exact ⟨distinct.2.1.1, distinct.1.2.1, distinct.1.1⟩

/-- Execute the original raw engine and then the original public nominal packing. -/
def publicBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.product (.unsignedWord width)
      (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width)) :
    Circuit model ctx ctx :=
  .seq (rawEngine (model := model) input outputs) (packRawOutputs (model := model) outputs result)

/-- Allocate the raw results, execute both original phases, and release the raw cells. -/
def publicIntoResult {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) : Circuit model ctx ctx :=
  withCells ctx (publicRawShapes width) fun cells _ transport _ =>
    publicBody (model := model) (transport.liftInput input) (publicRawOutputs cells)
      (transport.liftWrite result)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Store values of the two actual nominal-point unpack instructions

The same two native instructions used by signed-row preparation preserve
borrowed structural inputs and write both complete raw point values. This
interface is generic in point width and runtime context.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def unpackOp (input : CInputRef ctx (PointShape width))
    (raw : CWriteRef ctx (PointEquality.RawPointShape width)) :
    ClassicalOp (PointShape width) (PointEquality.RawPointShape width) ctx ctx :=
  .unpackEllipticCurvePoint width ctx input raw

/-- The Store after the actual first and second nominal-point unpack operations. -/
def twoUnpackStore (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) : Store ctx :=
  (store.applyOp (unpackOp base rawBase)).applyOp (unpackOp target rawTarget)

/-- The two actual writes preserve every separately supported original read. -/
lemma twoUnpackStore_read_other (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) {shape : CShape} (input : CInputRef ctx shape)
    (baseFree : rawBase.key ∉ input.storageKeys)
    (targetFree : rawTarget.key ∉ input.storageKeys) :
    (twoUnpackStore base target rawBase rawTarget store).read input = store.read input := by
  unfold twoUnpackStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (unpackOp target rawTarget) input
    (by simpa only [unpackOp, ClassicalOp.outputRef_unpackEllipticCurvePoint] using targetFree)]
  exact Store.read_applyOp_of_not_mem_storageKeys store (unpackOp base rawBase) input
    (by simpa only [unpackOp, ClassicalOp.outputRef_unpackEllipticCurvePoint] using baseFree)

/-- The first raw output still holds the original complete nominal-point unpack value. -/
lemma twoUnpackStore_base (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) (distinct : rawBase.key ≠ rawTarget.key) :
    (twoUnpackStore base target rawBase rawTarget store).read
      (.storage rawBase.toCStorageRef) =
        CShape.unpackEllipticCurvePoint width (store.read base) := by
  have first := Store.read_applyOp_output store (unpackOp base rawBase)
  have retained := Store.read_applyOp_of_not_mem_storageKeys
    (store.applyOp (unpackOp base rawBase)) (unpackOp target rawTarget)
    (.storage rawBase.toCStorageRef) (by
      change rawTarget.key ∉ (CInputRef.storage rawBase.toCStorageRef).storageKeys
      simpa [CInputRef.storageKeys] using Ne.symm distinct)
  unfold twoUnpackStore
  rw [retained]
  simpa only [unpackOp, ClassicalOp.outputRef_unpackEllipticCurvePoint,
    ClassicalOp.inputRef_unpackEllipticCurvePoint,
    ClassicalOp.eval_unpackEllipticCurvePoint] using first

/-- The second raw output holds the original target's complete unpack value. -/
lemma twoUnpackStore_target (base target : CInputRef ctx (PointShape width))
    (rawBase rawTarget : CWriteRef ctx (PointEquality.RawPointShape width))
    (store : Store ctx) (baseFree : rawBase.key ∉ target.storageKeys) :
    (twoUnpackStore base target rawBase rawTarget store).read
      (.storage rawTarget.toCStorageRef) =
        CShape.unpackEllipticCurvePoint width (store.read target) := by
  have source := Store.read_applyOp_of_not_mem_storageKeys store
    (unpackOp base rawBase) target (by
      simpa only [unpackOp, ClassicalOp.outputRef_unpackEllipticCurvePoint] using baseFree)
  have written := Store.read_applyOp_output
    (store.applyOp (unpackOp base rawBase)) (unpackOp target rawTarget)
  unfold twoUnpackStore
  calc
    _ = CShape.unpackEllipticCurvePoint width
          ((store.applyOp (unpackOp base rawBase)).read target) := by
      simpa only [unpackOp, ClassicalOp.outputRef_unpackEllipticCurvePoint,
        ClassicalOp.inputRef_unpackEllipticCurvePoint,
        ClassicalOp.eval_unpackEllipticCurvePoint] using written
    _ = _ := congrArg (CShape.unpackEllipticCurvePoint width) source

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation

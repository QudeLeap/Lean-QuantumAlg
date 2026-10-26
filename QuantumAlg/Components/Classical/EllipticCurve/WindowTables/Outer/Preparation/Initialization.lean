/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Record
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Values and preserved inputs of the actual paired-frame initialization

The three actual operations load the widened modulus and coefficient, then
increment the one-cell. The zero-cell is only preserved: its initial value
is an explicit premise. Both borrowed caller reads remain unchanged when
they avoid the three written keys.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

open Execution ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

/-- The Store projection of the existing actual initialization record. -/
def initializedStore (spec : ModulusSpec width) (coefficient : Nat)
    (store : Store ctx) : Store ctx :=
  let loadedModulus :=
    (ConstantWord.foldStep (model := model) frame.modulus
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) store).1
  let loadedCoefficient :=
    (ConstantWord.foldStep (model := model) frame.curveA
      (List.ofFn (ConstantWord.constantBits width coefficient)) loadedModulus).1
  loadedCoefficient.applyOp (ConstantWord.incrementOp frame.one)

/-- This Store view is definitionally the result of the real three-step record. -/
lemma initializationRecord_store (spec : ModulusSpec width) (coefficient : Nat)
    (before : Store ctx × model.HiddenState) :
    (frame.initializationRecord (model := model) spec coefficient before).1.1 =
      frame.initializedStore spec coefficient before.1 := by
  rfl

/-- The three actual writes preserve any structural read avoiding their keys. -/
lemma initializedStore_read_other (spec : ModulusSpec width) (coefficient : Nat)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (modulusFree : frame.modulus.key ∉ other.storageKeys)
    (curveAFree : frame.curveA.key ∉ other.storageKeys)
    (oneFree : frame.one.key ∉ other.storageKeys) :
    (frame.initializedStore (model := model) spec coefficient store).read other =
      store.read other := by
  unfold initializedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (ConstantWord.incrementOp frame.one) other oneFree]
  rw [ConstantWord.constantWord_fold_read_other (model := model) frame.curveA _
    other curveAFree]
  exact ConstantWord.constantWord_fold_read_other (model := model) frame.modulus _
    other modulusFree store

/-- The original pair of borrowed structural reads survives unchanged. -/
lemma initializationRecord_borrowed_pair (spec : ModulusSpec width)
    (coefficient : Nat) (before : Store ctx × model.HiddenState)
    {baseShape targetShape : CShape}
    (base : CInputRef ctx baseShape) (target : CInputRef ctx targetShape)
    (baseFree : ∀ key ∈ [frame.modulus.key, frame.curveA.key, frame.one.key],
      key ∉ base.storageKeys)
    (targetFree : ∀ key ∈ [frame.modulus.key, frame.curveA.key, frame.one.key],
      key ∉ target.storageKeys) :
    let returned := (frame.initializationRecord (model := model) spec coefficient before).1.1
    returned.read base = before.1.read base ∧
      returned.read target = before.1.read target := by
  dsimp only
  rw [frame.initializationRecord_store]
  constructor
  · exact frame.initializedStore_read_other spec coefficient before.1 base
      (baseFree _ (by simp)) (baseFree _ (by simp)) (baseFree _ (by simp))
  · exact frame.initializedStore_read_other spec coefficient before.1 target
      (targetFree _ (by simp)) (targetFree _ (by simp)) (targetFree _ (by simp))

omit [BitWord.Selected model] in
private lemma keyFree {writtenWidth observedWidth : Nat}
    (write : CWriteRef ctx (.unsignedWord writtenWidth))
    (read : CWriteRef ctx (.unsignedWord observedWidth))
    (different : write.key ≠ read.key) :
    write.key ∉ (ConstantWord.targetRead read).storageKeys :=
  fun present => different (List.mem_singleton.mp present)

/-- The loaded modulus includes the capacity boundary, not a truncated width word. -/
lemma initializedStore_modulus_toNat (spec : ModulusSpec width)
    (coefficient : Nat) (store : Store ctx) :
    ((frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.modulus)).toNat = spec.modulus := by
  unfold initializedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (ConstantWord.incrementOp frame.one) (ConstantWord.targetRead frame.modulus)
    (keyFree frame.one frame.modulus (by
      simpa [Frame.keyAt] using frame.keyAt_ne 6 4 (by decide)))]
  rw [ConstantWord.constantWord_fold_read_other (model := model) frame.curveA _
    (ConstantWord.targetRead frame.modulus)
    (keyFree frame.curveA frame.modulus (by
      simpa [Frame.keyAt] using frame.keyAt_ne 7 4 (by decide)))]
  exact (ConstantWord.constantWord_read (model := model) frame.modulus spec.modulus store).trans
    (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec))

/-- The loaded modulus is the exact intrinsic widened word. -/
lemma initializedStore_modulus (spec : ModulusSpec width)
    (coefficient : Nat) (store : Store ctx) :
    (frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.modulus) = .unsignedWord spec.extendedWord := by
  have actual := frame.initializedStore_modulus_toNat (model := model) spec coefficient store
  cases sampled : (frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.modulus) with
  | unsignedWord value =>
      rw [sampled] at actual
      exact congrArg CShape.Value.unsignedWord (Fin.ext actual)

/-- The coefficient loader overwrites its target with the width-truncated parameter. -/
lemma initializedStore_curveA_toNat (spec : ModulusSpec width)
    (coefficient : Nat) (store : Store ctx) :
    ((frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.curveA)).toNat = coefficient % 2 ^ width := by
  unfold initializedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (ConstantWord.incrementOp frame.one) (ConstantWord.targetRead frame.curveA)
    (keyFree frame.one frame.curveA (by
      simpa [Frame.keyAt] using frame.keyAt_ne 6 7 (by decide)))]
  exact ConstantWord.constantWord_read (model := model) frame.curveA coefficient _

/-- Loading the curve's actual canonical coefficient satisfies the table premise. -/
lemma initializedStore_curveA_curveValue (curve : CurveSpec width) (store : Store ctx) :
    (((frame.initializedStore (model := model) curve.field curve.curve.a.val store).read
      (ConstantWord.targetRead frame.curveA)).toNat : ZMod curve.field.modulus) =
      curve.curve.a := by
  have actual := frame.initializedStore_curveA_toNat (model := model)
    curve.field curve.curve.a.val store
  have bound : curve.curve.a.val < 2 ^ width :=
    (ZMod.val_lt curve.curve.a).trans_le curve.field.le_capacity
  rw [actual, Nat.mod_eq_of_lt bound, ZMod.natCast_zmod_val]

/-- Initialization does not create zero: it preserves an explicitly zero input cell. -/
lemma initializedStore_zero_toNat (spec : ModulusSpec width)
    (coefficient : Nat) (store : Store ctx)
    (zeroInitial : (store.read (ConstantWord.targetRead frame.zero)).toNat = 0) :
    ((frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.zero)).toNat = 0 := by
  have preserved := frame.initializedStore_read_other (model := model) spec coefficient
    store (ConstantWord.targetRead frame.zero)
    (keyFree frame.modulus frame.zero (by
      simpa [Frame.keyAt] using frame.keyAt_ne 4 5 (by decide)))
    (keyFree frame.curveA frame.zero (by
      simpa [Frame.keyAt] using frame.keyAt_ne 7 5 (by decide)))
    (keyFree frame.one frame.zero (by
      simpa [Frame.keyAt] using frame.keyAt_ne 6 5 (by decide)))
  exact (congrArg CShape.Value.toNat preserved).trans zeroInitial

/-- The actual two loaders followed by the paid native increment set an
initially zero one-cell to one. -/
lemma initializedStore_one_toNat (spec : ModulusSpec width)
    (coefficient : Nat) (store : Store ctx) (widthPositive : 0 < width)
    (oneInitial : (store.read (ConstantWord.targetRead frame.one)).toNat = 0) :
    ((frame.initializedStore (model := model) spec coefficient store).read
      (ConstantWord.targetRead frame.one)).toNat = 1 := by
  let oneRead := ConstantWord.targetRead frame.one
  let loadedModulus :=
    (ConstantWord.foldStep (model := model) frame.modulus
      (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus)) store).1
  let loadedCoefficient :=
    (ConstantWord.foldStep (model := model) frame.curveA
      (List.ofFn (ConstantWord.constantBits width coefficient)) loadedModulus).1
  have modulusFree : frame.modulus.key ∉ oneRead.storageKeys :=
    keyFree frame.modulus frame.one (by
      simpa [Frame.keyAt] using frame.keyAt_ne 4 6 (by decide))
  have curveAFree : frame.curveA.key ∉ oneRead.storageKeys :=
    keyFree frame.curveA frame.one (by
      simpa [Frame.keyAt] using frame.keyAt_ne 7 6 (by decide))
  have modulusPreserved : loadedModulus.read oneRead = store.read oneRead :=
    ConstantWord.constantWord_fold_read_other (model := model) frame.modulus _
      oneRead modulusFree store
  have curveAPreserved : loadedCoefficient.read oneRead = loadedModulus.read oneRead :=
    ConstantWord.constantWord_fold_read_other (model := model) frame.curveA _
      oneRead curveAFree loadedModulus
  have preserved : (loadedCoefficient.read oneRead).toNat =
      (store.read oneRead).toNat :=
    congrArg CShape.Value.toNat (curveAPreserved.trans modulusPreserved)
  have incremented := Store.read_applyOp_output loadedCoefficient
    (ConstantWord.incrementOp frame.one)
  change (loadedCoefficient.applyOp (ConstantWord.incrementOp frame.one)).read
      oneRead = CShape.wordOfNat width
        ((loadedCoefficient.read oneRead).toNat + 1) at incremented
  have incrementedNat := congrArg CShape.Value.toNat incremented
  change ((loadedCoefficient.applyOp (ConstantWord.incrementOp frame.one)).read
      oneRead).toNat =
        ((loadedCoefficient.read oneRead).toNat + 1) % CShape.wordModulus width
    at incrementedNat
  have oneFits : 1 < CShape.wordModulus width := by
    change 1 < 2 ^ width
    have exponentBound : 1 ≤ width := widthPositive
    have lower : 2 ^ 1 ≤ 2 ^ width :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) exponentBound
    norm_num at lower
    omega
  change ((loadedCoefficient.applyOp (ConstantWord.incrementOp frame.one)).read
      oneRead).toNat = 1
  calc
    _ = ((loadedCoefficient.read oneRead).toNat + 1) % CShape.wordModulus width :=
      incrementedNat
    _ = 1 := by
      rw [preserved, oneInitial, Nat.zero_add]
      exact Nat.mod_eq_of_lt oneFits

/-- The Store projection of the actual paid initialization record contains one. -/
lemma initializationRecord_one_toNat (spec : ModulusSpec width)
    (coefficient : Nat) (before : Store ctx × model.HiddenState)
    (widthPositive : 0 < width)
    (oneInitial : (before.1.read (ConstantWord.targetRead frame.one)).toNat = 0) :
    (((frame.initializationRecord (model := model) spec coefficient before).1.1).read
      (ConstantWord.targetRead frame.one)).toNat = 1 := by
  rw [frame.initializationRecord_store]
  exact frame.initializedStore_one_toNat spec coefficient before.1 widthPositive oneInitial

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame

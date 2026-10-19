/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Execution

/-!
# Exact actual finite values of the original doubling arm

The original square, doubled/tripled square, loaded public coefficient and
slope operands are written in their original order. The same total affine
program returns the exact finite nominal value on every raw input.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All six original finite doubling-prefix results. -/
structure DoublingValues (width : Nat) where
  xSquared : CShape.Word width
  doubledXSquared : CShape.Word width
  tripledXSquared : CShape.Word width
  a : CShape.Word width
  numerator : CShape.Word width
  denominator : CShape.Word width

/-- Original arithmetic and actual constant loading give these total finite expressions. -/
def doublingValues (spec : CurveSpec width) (x y : CShape.Word width) : DoublingValues width :=
  let xSquared := CShape.wordOfNat width (x.toNat * x.toNat % spec.field.modulus)
  let doubled := CShape.wordOfNat width ((xSquared.toNat + xSquared.toNat) % spec.field.modulus)
  let tripled := CShape.wordOfNat width ((doubled.toNat + xSquared.toNat) % spec.field.modulus)
  let a := CShape.wordOfNat width (doublingCurveAWord spec).toNat
  let numerator := CShape.wordOfNat width ((tripled.toNat + a.toNat) % spec.field.modulus)
  let denominator := CShape.wordOfNat width ((y.toNat + y.toNat) % spec.field.modulus)
  ⟨xSquared, doubled, tripled, a, numerator, denominator⟩

/-- The original final affine tail consumes exactly the two materialized slope operands. -/
def doublingOutputValue (spec : CurveSpec width)
    (point : CShape.Value (PointEquality.RawPointShape width)) : CShape.Value (PointShape width) :=
  let x := point.second.first
  let y := point.second.second
  let values := doublingValues spec x y
  affineOutputValue spec.field x x y values.numerator values.denominator

/-- Actual physical keys of the six original chronological prefix cells. -/
def DoublingScratch.keys (scratch : DoublingScratch ctx width) : List StorageKey :=
  [scratch.xSquared.key, scratch.doubledXSquared.key, scratch.tripledXSquared.key,
    scratch.a.key, scratch.numerator.key, scratch.denominator.key]

/-- Separation is restricted to the original internally allocated cells and input snapshots. -/
structure DoublingScratch.Separation (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  pointX : ∀ key ∈ scratch.keys, key ∉ pointX.storageKeys
  pointY : ∀ key ∈ scratch.keys, key ∉ pointY.storageKeys

/-- Every actual stage writes its certified finite result into its sole real destination. -/
def doublingStageStore (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Fin 7 → Store ctx → Store ctx :=
  ![fun store => store.write scratch.xSquared (CShape.wordOfNat width
      ((store.read pointX).toNat * (store.read pointX).toNat % spec.field.modulus)),
    fun store => store.write scratch.doubledXSquared (CShape.wordOfNat width
      (((store.read (classifierRead scratch.xSquared)).toNat +
        (store.read (classifierRead scratch.xSquared)).toNat) % spec.field.modulus)),
    fun store => store.write scratch.tripledXSquared (CShape.wordOfNat width
      (((store.read (classifierRead scratch.doubledXSquared)).toNat +
        (store.read (classifierRead scratch.xSquared)).toNat) % spec.field.modulus)),
    fun store => store.write scratch.a (CShape.wordOfNat width (doublingCurveAWord spec).toNat),
    fun store => store.write scratch.numerator (CShape.wordOfNat width
      (((store.read (classifierRead scratch.tripledXSquared)).toNat +
        (store.read (classifierRead scratch.a)).toNat) % spec.field.modulus)),
    fun store => store.write scratch.denominator (CShape.wordOfNat width
      (((store.read pointY).toNat + (store.read pointY).toNat) % spec.field.modulus)),
    fun store => store.write output (affineOutputValue spec.field
      (store.read pointX) (store.read pointX) (store.read pointY)
      (store.read (classifierRead scratch.numerator))
      (store.read (classifierRead scratch.denominator)))]

section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The certified actual path of each original stage returns that precise complete Store. -/
lemma doublingStageRecord_store (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 7) (store : Store ctx) (hidden : model.HiddenState) :
    (doublingStageRecord (environment := environment) spec pointX pointY scratch output index
      (store, hidden)).1.1 =
      doublingStageStore spec pointX pointY scratch output index store := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.mulIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact ConstantWord.constantWord_fold_store _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · exact affineIntoStep_store (model := model) _ _ _ _ _ _ _ _ _
  exact Fin.elim0 index

end

/-- Actual chronological fold of the seven certified destination writes. -/
def doublingBodyStore (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) : Store ctx :=
  (List.ofFn (doublingStageStore spec pointX pointY scratch output)).foldl
    (fun current update => update current) store

section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual complete execution returns the same seven-stage chronological Store. -/
lemma doublingBodyStep_store (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) (hidden : model.HiddenState) :
    (doublingBodyStep (environment := environment) spec pointX pointY scratch output (store,
      hidden)).1.1 =
      doublingBodyStore spec pointX pointY scratch output store := by
  have fold_store (indices : List (Fin 7))
      (entry : Store ctx × model.HiddenState) :
      ((indices.map (fun index => fun current =>
        (doublingStageRecord (environment := environment) spec pointX pointY scratch output
          index current).1)).foldl
          (fun current update => update current) entry).1 =
        (indices.map (doublingStageStore spec pointX pointY scratch output)).foldl
          (fun current update => update current) entry.1 := by
    induction indices generalizing entry with
    | nil => rfl
    | cons index rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [ih, doublingStageRecord_store]
  rw [doublingBodyStep, Circuit.forRangeRecord_store]
  simpa only [doublingBodyStore, List.map_ofFn, Function.comp_def] using
    fold_store (List.ofFn (fun index : Fin 7 => index)) (store, hidden)

end

/-- Exact actual six-prefix-cell contents immediately before entering the original affine tail. -/
def doublingArithmeticStore (scratch : DoublingScratch ctx width) (values : DoublingValues width)
    (store : Store ctx) : Store ctx :=
  ((((((store.write scratch.xSquared values.xSquared).write scratch.doubledXSquared
    values.doubledXSquared).write scratch.tripledXSquared values.tripledXSquared).write
    scratch.a values.a).write scratch.numerator values.numerator).write
    scratch.denominator values.denominator)

private lemma doubling_key_ne (scratch : DoublingScratch ctx width)
    (distinct : scratch.keys.Nodup) (first second : Fin 6) (different : first ≠ second) :
    scratch.keys.get first ≠ scratch.keys.get second :=
  fun same => different ((List.nodup_iff_injective_get.mp distinct) same)

/-- The actual seven-call body writes exactly the original finite prefix and nominal result. -/
lemma doublingBodyStore_values (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (separate : scratch.Separation pointX pointY) (store : Store ctx) :
    doublingBodyStore spec pointX pointY scratch output store =
      (doublingArithmeticStore scratch (doublingValues spec (store.read pointX) (store.read pointY))
        store).write output (affineOutputValue spec.field (store.read pointX) (store.read pointX)
          (store.read pointY)
          (doublingValues spec (store.read pointX) (store.read pointY)).numerator
          (doublingValues spec (store.read pointX) (store.read pointY)).denominator) := by
  have h10 : scratch.doubledXSquared.key ≠ scratch.xSquared.key :=
    doubling_key_ne scratch separate.distinct 1 0 (by decide)
  have h32 : scratch.a.key ≠ scratch.tripledXSquared.key :=
    doubling_key_ne scratch separate.distinct 3 2 (by decide)
  have h54 : scratch.denominator.key ≠ scratch.numerator.key :=
    doubling_key_ne scratch separate.distinct 5 4 (by decide)
  have pointX0 := separate.pointX scratch.xSquared.key (by simp [DoublingScratch.keys])
  have pointX1 := separate.pointX scratch.doubledXSquared.key (by simp [DoublingScratch.keys])
  have pointX2 := separate.pointX scratch.tripledXSquared.key (by simp [DoublingScratch.keys])
  have pointX3 := separate.pointX scratch.a.key (by simp [DoublingScratch.keys])
  have pointX4 := separate.pointX scratch.numerator.key (by simp [DoublingScratch.keys])
  have pointX5 := separate.pointX scratch.denominator.key (by simp [DoublingScratch.keys])
  have pointY0 := separate.pointY scratch.xSquared.key (by simp [DoublingScratch.keys])
  have pointY1 := separate.pointY scratch.doubledXSquared.key (by simp [DoublingScratch.keys])
  have pointY2 := separate.pointY scratch.tripledXSquared.key (by simp [DoublingScratch.keys])
  have pointY3 := separate.pointY scratch.a.key (by simp [DoublingScratch.keys])
  have pointY4 := separate.pointY scratch.numerator.key (by simp [DoublingScratch.keys])
  have pointY5 := separate.pointY scratch.denominator.key (by simp [DoublingScratch.keys])
  let values := doublingValues spec (store.read pointX) (store.read pointY)
  let s0 := store
  let s1 := s0.write scratch.xSquared values.xSquared
  let s2 := s1.write scratch.doubledXSquared values.doubledXSquared
  let s3 := s2.write scratch.tripledXSquared values.tripledXSquared
  let s4 := s3.write scratch.a values.a
  let s5 := s4.write scratch.numerator values.numerator
  let s6 := s5.write scratch.denominator values.denominator
  let s7 := s6.write output (affineOutputValue spec.field (store.read pointX) (store.read pointX)
    (store.read pointY) values.numerator values.denominator)
  have step0 : doublingStageStore spec pointX pointY scratch output 0 s0 = s1 := by
    rfl
  have step1 : doublingStageStore spec pointX pointY scratch output 1 s1 = s2 := by
    change s1.write scratch.doubledXSquared (CShape.wordOfNat width
      (((s1.read (classifierRead scratch.xSquared)).toNat +
        (s1.read (classifierRead scratch.xSquared)).toNat) % spec.field.modulus)) = s2
    dsimp only [s0, s1, s2]
    simp only [
      classifierRead,
      Store.read_write_same]
    rfl
  have step2 : doublingStageStore spec pointX pointY scratch output 2 s2 = s3 := by
    change s2.write scratch.tripledXSquared (CShape.wordOfNat width
      (((s2.read (classifierRead scratch.doubledXSquared)).toNat +
        (s2.read (classifierRead scratch.xSquared)).toNat) % spec.field.modulus)) = s3
    dsimp only [s0, s1, s2, s3]
    simp only [
      classifierRead,
      Store.read_write_same,
      Store.read_write_other _ scratch.doubledXSquared scratch.xSquared.toCStorageRef _ h10]
    rfl
  have step3 : doublingStageStore spec pointX pointY scratch output 3 s3 = s4 := by
    rfl
  have step4 : doublingStageStore spec pointX pointY scratch output 4 s4 = s5 := by
    change s4.write scratch.numerator (CShape.wordOfNat width
      (((s4.read (classifierRead scratch.tripledXSquared)).toNat +
        (s4.read (classifierRead scratch.a)).toNat) % spec.field.modulus)) = s5
    dsimp only [s0, s1, s2, s3, s4, s5]
    simp only [
      classifierRead,
      Store.read_write_same,
      Store.read_write_other _ scratch.a scratch.tripledXSquared.toCStorageRef _ h32]
    rfl
  have step5 : doublingStageStore spec pointX pointY scratch output 5 s5 = s6 := by
    change s5.write scratch.denominator (CShape.wordOfNat width
      (((s5.read pointY).toNat + (s5.read pointY).toNat) % spec.field.modulus)) = s6
    dsimp only [s0, s1, s2, s3, s4, s5, s6]
    simp only [
      Store.read_write_of_not_mem_storageKeys _ scratch.numerator _ pointY pointY4,
      Store.read_write_of_not_mem_storageKeys _ scratch.a _ pointY pointY3,
      Store.read_write_of_not_mem_storageKeys _ scratch.tripledXSquared _ pointY pointY2,
      Store.read_write_of_not_mem_storageKeys _ scratch.doubledXSquared _ pointY pointY1,
      Store.read_write_of_not_mem_storageKeys _ scratch.xSquared _ pointY pointY0]
    rfl
  have step6 : doublingStageStore spec pointX pointY scratch output 6 s6 = s7 := by
    change s6.write output (affineOutputValue spec.field (s6.read pointX) (s6.read pointX)
      (s6.read pointY) (s6.read (classifierRead scratch.numerator))
        (s6.read (classifierRead scratch.denominator))) = s7
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7]
    simp only [
      classifierRead,
      Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.denominator _ pointX pointX5,
      Store.read_write_of_not_mem_storageKeys _ scratch.numerator _ pointX pointX4,
      Store.read_write_of_not_mem_storageKeys _ scratch.a _ pointX pointX3,
      Store.read_write_of_not_mem_storageKeys _ scratch.tripledXSquared _ pointX pointX2,
      Store.read_write_of_not_mem_storageKeys _ scratch.doubledXSquared _ pointX pointX1,
      Store.read_write_of_not_mem_storageKeys _ scratch.xSquared _ pointX pointX0,
      Store.read_write_of_not_mem_storageKeys _ scratch.denominator _ pointY pointY5,
      Store.read_write_of_not_mem_storageKeys _ scratch.numerator _ pointY pointY4,
      Store.read_write_of_not_mem_storageKeys _ scratch.a _ pointY pointY3,
      Store.read_write_of_not_mem_storageKeys _ scratch.tripledXSquared _ pointY pointY2,
      Store.read_write_of_not_mem_storageKeys _ scratch.doubledXSquared _ pointY pointY1,
      Store.read_write_of_not_mem_storageKeys _ scratch.xSquared _ pointY pointY0,
      Store.read_write_other _ scratch.denominator scratch.numerator.toCStorageRef _ h54]
  change (doublingStageStore spec pointX pointY scratch output 6
    (doublingStageStore spec pointX pointY scratch output 5
    (doublingStageStore spec pointX pointY scratch output 4
    (doublingStageStore spec pointX pointY scratch output 3
    (doublingStageStore spec pointX pointY scratch output 2
    (doublingStageStore spec pointX pointY scratch output 1
    (doublingStageStore spec pointX pointY scratch output 0
    store))))))) = _
  rw [step0, step1, step2, step3, step4, step5, step6]
  rfl

/-- Every caller read is retained outside the six actual prefix destinations. -/
lemma doublingArithmeticStore_preserves (scratch : DoublingScratch ctx width)
    (values : DoublingValues width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (doublingArithmeticStore scratch values store).read input = store.read input := by
  have xSquaredFree := separate scratch.xSquared.key (by simp [DoublingScratch.keys])
  have doubledXSquaredFree := separate scratch.doubledXSquared.key (by simp [DoublingScratch.keys])
  have tripledXSquaredFree := separate scratch.tripledXSquared.key (by simp [DoublingScratch.keys])
  have aFree := separate scratch.a.key (by simp [DoublingScratch.keys])
  have numeratorFree := separate scratch.numerator.key (by simp [DoublingScratch.keys])
  have denominatorFree := separate scratch.denominator.key (by simp [DoublingScratch.keys])
  simp only [doublingArithmeticStore,
    Store.read_write_of_not_mem_storageKeys _ scratch.denominator _ input denominatorFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.numerator _ input numeratorFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.a _ input aFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.tripledXSquared _ input tripledXSquaredFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.doubledXSquared _ input doubledXSquaredFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.xSquared _ input xSquaredFree]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

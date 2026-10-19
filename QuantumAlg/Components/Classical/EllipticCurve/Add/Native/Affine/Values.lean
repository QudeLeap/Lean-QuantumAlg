/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Execution
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Actual finite values of the original common affine tail

The nine certified calls write their real intermediate stores in the original
order. Their finite-word equations remain total on raw inputs. Allocation
supplies the false tag and separation; no inverse or field-domain promise is
required for the exact returned nominal word and complete caller-store frame.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The exact eight original finite arithmetic results, in chronological order. -/
structure AffineValues (width : Nat) where
  coefficient : CShape.Word width
  slope : CShape.Word width
  slopeSquared : CShape.Word width
  xPartial : CShape.Word width
  xOutput : CShape.Word width
  xDifference : CShape.Word width
  yProduct : CShape.Word width
  yOutput : CShape.Word width

/-- Closed finite-word expressions preserve the original total coefficient and raw subtractions. -/
def affineValues (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CShape.Word width) : AffineValues width :=
  let coefficient := CShape.wordOfNat width (Field.Native.coefficientResidue spec denominator).val
  let slope := CShape.wordOfNat width (numerator.toNat * coefficient.toNat % spec.modulus)
  let slopeSquared := CShape.wordOfNat width (slope.toNat * slope.toNat % spec.modulus)
  let xPartial := Field.Native.subtractionWord spec slopeSquared leftX
  let xOutput := Field.Native.subtractionWord spec xPartial rightX
  let xDifference := Field.Native.subtractionWord spec leftX xOutput
  let yProduct := CShape.wordOfNat width (slope.toNat * xDifference.toNat % spec.modulus)
  let yOutput := Field.Native.subtractionWord spec yProduct leftY
  ⟨coefficient, slope, slopeSquared, xPartial, xOutput, xDifference, yProduct, yOutput⟩

/-- Actual nominal packing uses the supplied original tag and the final two computed words. -/
def AffineValues.point (values : AffineValues width) (tag : CShape.Value .bit) :
    CShape.Value (PointShape width) :=
  CShape.packEllipticCurvePoint width (.product tag (.product values.xOutput values.yOutput))

/-- Every cell potentially modified by the original arithmetic prefix, together with its tag. -/
def AffineScratch.keys (scratch : AffineScratch ctx width) : List StorageKey :=
  [scratch.coefficient.key, scratch.slope.key, scratch.slopeSquared.key, scratch.xPartial.key,
    scratch.xOutput.key, scratch.xDifference.key, scratch.yProduct.key, scratch.yOutput.key,
    scratch.tag.key]

/-- The internal cells alone are distinct and disjoint from the actual source snapshots. -/
structure AffineScratch.Separation
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  leftX : ∀ key ∈ scratch.keys, key ∉ leftX.storageKeys
  rightX : ∀ key ∈ scratch.keys, key ∉ rightX.storageKeys
  leftY : ∀ key ∈ scratch.keys, key ∉ leftY.storageKeys
  numerator : ∀ key ∈ scratch.keys, key ∉ numerator.storageKeys
  denominator : ∀ key ∈ scratch.keys, key ∉ denominator.storageKeys

section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Each actual native component has exactly its certified one-destination Store update. -/
def affineStageStore (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Fin 9 → Store ctx → Store ctx :=
  ![fun store => store.write scratch.coefficient
      (CShape.wordOfNat width (Field.Native.coefficientResidue spec (store.read denominator)).val),
    fun store => store.write scratch.slope (CShape.wordOfNat width
      ((store.read numerator).toNat * (store.read (classifierRead scratch.coefficient)).toNat %
        spec.modulus)),
    fun store => store.write scratch.slopeSquared (CShape.wordOfNat width
      ((store.read (classifierRead scratch.slope)).toNat *
        (store.read (classifierRead scratch.slope)).toNat % spec.modulus)),
    fun store => store.write scratch.xPartial (Field.Native.subtractionWord spec
      (store.read (classifierRead scratch.slopeSquared)) (store.read leftX)),
    fun store => store.write scratch.xOutput (Field.Native.subtractionWord spec
      (store.read (classifierRead scratch.xPartial)) (store.read rightX)),
    fun store => store.write scratch.xDifference (Field.Native.subtractionWord spec
      (store.read leftX) (store.read (classifierRead scratch.xOutput))),
    fun store => store.write scratch.yProduct (CShape.wordOfNat width
      ((store.read (classifierRead scratch.slope)).toNat *
        (store.read (classifierRead scratch.xDifference)).toNat % spec.modulus)),
    fun store => store.write scratch.yOutput (Field.Native.subtractionWord spec
      (store.read (classifierRead scratch.yProduct)) (store.read leftY)),
    repackStore (model := model) (.product (classifierRead scratch.tag)
      (.product (classifierRead scratch.xOutput) (classifierRead scratch.yOutput))) output]

/-- The exact Store part of each certified actual path is its native arithmetic update. -/
lemma affineStageRecord_store (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9) (before : Store ctx × model.HiddenState) :
    (affineStageRecord (environment := environment) spec leftX rightX leftY numerator
      denominator scratch output index
      before).1.1 =
      affineStageStore spec leftX rightX leftY numerator denominator scratch output
        index before.1 := by
  rcases before with ⟨store, hidden⟩
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.coefficientIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.mulIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.mulIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.subIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.subIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.subIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.mulIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStageRecord, affineStageStore]
    exact Field.Native.subIntoWordStep_store _ _ _ _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · rfl
  exact Fin.elim0 index

/-- The original arithmetic chronology is the fold of the nine actual destination writes. -/
def affineBodyStore (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) : Store ctx :=
  (List.ofFn (affineStageStore spec leftX rightX leftY numerator denominator scratch output)).foldl
    (fun current update => update current) store

/-- The actual nine-call execution record returns precisely that complete chronological Store. -/
lemma affineBodyStep_store (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) (hidden : model.HiddenState) :
    (affineBodyStep (environment := environment) spec leftX rightX leftY numerator denominator
      scratch output
      (store, hidden)).1.1 =
      affineBodyStore spec leftX rightX leftY numerator denominator scratch output store := by
  rw [affineBodyStep, Circuit.forRangeRecord_store]
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil,
    affineStageRecord_store, affineBodyStore]

end

/-- The eight actual arithmetic cells contain these complete finite values before packing. -/
def affineArithmeticStore (scratch : AffineScratch ctx width) (values : AffineValues width)
    (store : Store ctx) : Store ctx :=
  ((((((((store.write scratch.coefficient values.coefficient).write
    scratch.slope values.slope).write
    scratch.slopeSquared values.slopeSquared).write scratch.xPartial values.xPartial).write
    scratch.xOutput values.xOutput).write scratch.xDifference values.xDifference).write
    scratch.yProduct values.yProduct).write scratch.yOutput values.yOutput)

private lemma scratch_key_ne (scratch : AffineScratch ctx width)
    (distinct : scratch.keys.Nodup) (first second : Fin 9) (different : first ≠ second) :
    scratch.keys.get first ≠ scratch.keys.get second :=
  fun same => different ((List.nodup_iff_injective_get.mp distinct) same)

private lemma read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

omit [BitWord.Selected model] in
/-- The real chronological arithmetic and pack yield exactly the closed original finite values. -/
lemma affineBodyStore_values (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (separate : scratch.Separation leftX rightX leftY numerator denominator) (store : Store ctx) :
    affineBodyStore spec leftX rightX leftY numerator denominator scratch output store =
      (affineArithmeticStore scratch (affineValues spec (store.read leftX) (store.read rightX)
        (store.read leftY) (store.read numerator) (store.read denominator)) store).write output
          ((affineValues spec (store.read leftX) (store.read rightX) (store.read leftY)
            (store.read numerator) (store.read denominator)).point
              (store.read (classifierRead scratch.tag))) := by
  have h08 : scratch.coefficient.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 0 8 (by decide)
  have h18 : scratch.slope.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 1 8 (by decide)
  have h28 : scratch.slopeSquared.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 2 8 (by decide)
  have h38 : scratch.xPartial.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 3 8 (by decide)
  have h48 : scratch.xOutput.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 4 8 (by decide)
  have h58 : scratch.xDifference.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 5 8 (by decide)
  have h68 : scratch.yProduct.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 6 8 (by decide)
  have h78 : scratch.yOutput.key ≠ scratch.tag.key :=
    scratch_key_ne scratch separate.distinct 7 8 (by decide)
  have h21 : scratch.slopeSquared.key ≠ scratch.slope.key :=
    scratch_key_ne scratch separate.distinct 2 1 (by decide)
  have h31 : scratch.xPartial.key ≠ scratch.slope.key :=
    scratch_key_ne scratch separate.distinct 3 1 (by decide)
  have h41 : scratch.xOutput.key ≠ scratch.slope.key :=
    scratch_key_ne scratch separate.distinct 4 1 (by decide)
  have h51 : scratch.xDifference.key ≠ scratch.slope.key :=
    scratch_key_ne scratch separate.distinct 5 1 (by decide)
  have h54 : scratch.xDifference.key ≠ scratch.xOutput.key :=
    scratch_key_ne scratch separate.distinct 5 4 (by decide)
  have h64 : scratch.yProduct.key ≠ scratch.xOutput.key :=
    scratch_key_ne scratch separate.distinct 6 4 (by decide)
  have h74 : scratch.yOutput.key ≠ scratch.xOutput.key :=
    scratch_key_ne scratch separate.distinct 7 4 (by decide)
  have numerator0 := separate.numerator scratch.coefficient.key (by simp [AffineScratch.keys])
  have leftX0 := separate.leftX scratch.coefficient.key (by simp [AffineScratch.keys])
  have leftX1 := separate.leftX scratch.slope.key (by simp [AffineScratch.keys])
  have leftX2 := separate.leftX scratch.slopeSquared.key (by simp [AffineScratch.keys])
  have leftX3 := separate.leftX scratch.xPartial.key (by simp [AffineScratch.keys])
  have leftX4 := separate.leftX scratch.xOutput.key (by simp [AffineScratch.keys])
  have rightX0 := separate.rightX scratch.coefficient.key (by simp [AffineScratch.keys])
  have rightX1 := separate.rightX scratch.slope.key (by simp [AffineScratch.keys])
  have rightX2 := separate.rightX scratch.slopeSquared.key (by simp [AffineScratch.keys])
  have rightX3 := separate.rightX scratch.xPartial.key (by simp [AffineScratch.keys])
  have leftY0 := separate.leftY scratch.coefficient.key (by simp [AffineScratch.keys])
  have leftY1 := separate.leftY scratch.slope.key (by simp [AffineScratch.keys])
  have leftY2 := separate.leftY scratch.slopeSquared.key (by simp [AffineScratch.keys])
  have leftY3 := separate.leftY scratch.xPartial.key (by simp [AffineScratch.keys])
  have leftY4 := separate.leftY scratch.xOutput.key (by simp [AffineScratch.keys])
  have leftY5 := separate.leftY scratch.xDifference.key (by simp [AffineScratch.keys])
  have leftY6 := separate.leftY scratch.yProduct.key (by simp [AffineScratch.keys])
  let values := affineValues spec (store.read leftX) (store.read rightX) (store.read leftY)
    (store.read numerator) (store.read denominator)
  let s0 := store
  let s1 := s0.write scratch.coefficient values.coefficient
  let s2 := s1.write scratch.slope values.slope
  let s3 := s2.write scratch.slopeSquared values.slopeSquared
  let s4 := s3.write scratch.xPartial values.xPartial
  let s5 := s4.write scratch.xOutput values.xOutput
  let s6 := s5.write scratch.xDifference values.xDifference
  let s7 := s6.write scratch.yProduct values.yProduct
  let s8 := s7.write scratch.yOutput values.yOutput
  let s9 := s8.write output (values.point (store.read (classifierRead scratch.tag)))
  have step0 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      0 s0 = s1 := by
    rfl
  have step1 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      1 s1 = s2 := by
    change s1.write scratch.slope (CShape.wordOfNat width
      ((s1.read numerator).toNat * (s1.read (classifierRead scratch.coefficient)).toNat %
        spec.modulus)) = s2
    dsimp only [s0, s1, s2]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ numerator numerator0]
    rfl
  have step2 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      2 s2 = s3 := by
    change s2.write scratch.slopeSquared (CShape.wordOfNat width
      ((s2.read (classifierRead scratch.slope)).toNat *
        (s2.read (classifierRead scratch.slope)).toNat % spec.modulus)) = s3
    dsimp only [s0, s1, s2, s3]
    simp only [classifierRead, Store.read_write_same]
    rfl
  have step3 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      3 s3 = s4 := by
    change s3.write scratch.xPartial (Field.Native.subtractionWord spec
      (s3.read (classifierRead scratch.slopeSquared)) (s3.read leftX)) = s4
    dsimp only [s0, s1, s2, s3, s4]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.slopeSquared _ leftX leftX2,
      Store.read_write_of_not_mem_storageKeys _ scratch.slope _ leftX leftX1,
      Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ leftX leftX0]
    rfl
  have step4 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      4 s4 = s5 := by
    change s4.write scratch.xOutput (Field.Native.subtractionWord spec
      (s4.read (classifierRead scratch.xPartial)) (s4.read rightX)) = s5
    dsimp only [s0, s1, s2, s3, s4, s5]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.xPartial _ rightX rightX3,
      Store.read_write_of_not_mem_storageKeys _ scratch.slopeSquared _ rightX rightX2,
      Store.read_write_of_not_mem_storageKeys _ scratch.slope _ rightX rightX1,
      Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ rightX rightX0]
    rfl
  have step5 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      5 s5 = s6 := by
    change s5.write scratch.xDifference (Field.Native.subtractionWord spec
      (s5.read leftX) (s5.read (classifierRead scratch.xOutput))) = s6
    dsimp only [s0, s1, s2, s3, s4, s5, s6]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.xOutput _ leftX leftX4,
      Store.read_write_of_not_mem_storageKeys _ scratch.xPartial _ leftX leftX3,
      Store.read_write_of_not_mem_storageKeys _ scratch.slopeSquared _ leftX leftX2,
      Store.read_write_of_not_mem_storageKeys _ scratch.slope _ leftX leftX1,
      Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ leftX leftX0]
    rfl
  have step6 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      6 s6 = s7 := by
    change s6.write scratch.yProduct (CShape.wordOfNat width
      ((s6.read (classifierRead scratch.slope)).toNat *
        (s6.read (classifierRead scratch.xDifference)).toNat % spec.modulus)) = s7
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_other _ scratch.xDifference scratch.slope.toCStorageRef _ h51,
      Store.read_write_other _ scratch.xOutput scratch.slope.toCStorageRef _ h41,
      Store.read_write_other _ scratch.xPartial scratch.slope.toCStorageRef _ h31,
      Store.read_write_other _ scratch.slopeSquared scratch.slope.toCStorageRef _ h21]
    rfl
  have step7 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      7 s7 = s8 := by
    change s7.write scratch.yOutput (Field.Native.subtractionWord spec
      (s7.read (classifierRead scratch.yProduct)) (s7.read leftY)) = s8
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8]
    simp only [classifierRead, Store.read_write_same,
      Store.read_write_of_not_mem_storageKeys _ scratch.yProduct _ leftY leftY6,
      Store.read_write_of_not_mem_storageKeys _ scratch.xDifference _ leftY leftY5,
      Store.read_write_of_not_mem_storageKeys _ scratch.xOutput _ leftY leftY4,
      Store.read_write_of_not_mem_storageKeys _ scratch.xPartial _ leftY leftY3,
      Store.read_write_of_not_mem_storageKeys _ scratch.slopeSquared _ leftY leftY2,
      Store.read_write_of_not_mem_storageKeys _ scratch.slope _ leftY leftY1,
      Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ leftY leftY0]
    rfl
  have step8 : affineStageStore spec leftX rightX leftY numerator denominator scratch output
      8 s8 = s9 := by
    change repackStore (.product (classifierRead scratch.tag)
      (.product (classifierRead scratch.xOutput) (classifierRead scratch.yOutput))) output s8 = s9
    dsimp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
    rw [repackStore]
    simp only [read_product, classifierRead, Store.read_write_same,
      Store.read_write_other _ scratch.yOutput scratch.tag.toCStorageRef _ h78,
      Store.read_write_other _ scratch.yProduct scratch.tag.toCStorageRef _ h68,
      Store.read_write_other _ scratch.xDifference scratch.tag.toCStorageRef _ h58,
      Store.read_write_other _ scratch.xOutput scratch.tag.toCStorageRef _ h48,
      Store.read_write_other _ scratch.xPartial scratch.tag.toCStorageRef _ h38,
      Store.read_write_other _ scratch.slopeSquared scratch.tag.toCStorageRef _ h28,
      Store.read_write_other _ scratch.slope scratch.tag.toCStorageRef _ h18,
      Store.read_write_other _ scratch.coefficient scratch.tag.toCStorageRef _ h08,
      Store.read_write_other _ scratch.yOutput scratch.xOutput.toCStorageRef _ h74,
      Store.read_write_other _ scratch.yProduct scratch.xOutput.toCStorageRef _ h64,
      Store.read_write_other _ scratch.xDifference scratch.xOutput.toCStorageRef _ h54]
    rfl
  change (affineStageStore spec leftX rightX leftY numerator denominator scratch output 8
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 7
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 6
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 5
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 4
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 3
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 2
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 1
    (affineStageStore spec leftX rightX leftY numerator denominator scratch output 0
    store))))))))) = _
  rw [step0, step1, step2, step3, step4, step5, step6, step7, step8]
  rfl

end

/-- The exact arithmetic prefix preserves every read outside the actual eight written cells. -/
lemma affineArithmeticStore_preserves (scratch : AffineScratch ctx width)
    (values : AffineValues width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (affineArithmeticStore scratch values store).read input = store.read input := by
  have coefficientFree := separate scratch.coefficient.key (by simp [AffineScratch.keys])
  have slopeFree := separate scratch.slope.key (by simp [AffineScratch.keys])
  have slopeSquaredFree := separate scratch.slopeSquared.key (by simp [AffineScratch.keys])
  have xPartialFree := separate scratch.xPartial.key (by simp [AffineScratch.keys])
  have xOutputFree := separate scratch.xOutput.key (by simp [AffineScratch.keys])
  have xDifferenceFree := separate scratch.xDifference.key (by simp [AffineScratch.keys])
  have yProductFree := separate scratch.yProduct.key (by simp [AffineScratch.keys])
  have yOutputFree := separate scratch.yOutput.key (by simp [AffineScratch.keys])
  simp only [affineArithmeticStore,
    Store.read_write_of_not_mem_storageKeys _ scratch.yOutput _ input yOutputFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.yProduct _ input yProductFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.xDifference _ input xDifferenceFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.xOutput _ input xOutputFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.xPartial _ input xPartialFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.slopeSquared _ input slopeSquaredFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.slope _ input slopeFree,
    Store.read_write_of_not_mem_storageKeys _ scratch.coefficient _ input coefficientFree
  ]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

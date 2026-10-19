/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Program

/-!
# Original binary-refinement values and full actual caller frame
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

private lemma storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

private lemma read_product {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) {left right : CShape}
    (first : CInputRef ctx left) (second : CInputRef ctx right) :
    store.read (.product first second) =
      .product (store.read first) (store.read second) := rfl

private lemma bitNotEval_toBool (value : CShape.Value .bit) :
    (Resource.BitOpcode.not.eval value).toBool = !value.toBool := by
  cases value
  rfl

/-- Every actual caller read outside the four prefix destinations survives the prefix. -/
lemma roundPrefixInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width : Nat} (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (midCarryAvoids : refs.midCarry.key ∉ other.storageKeys)
    (squareAvoids : refs.square.key ∉ other.storageKeys)
    (tooLargeAvoids : refs.tooLarge.key ∉ other.storageKeys)
    (takeAvoids : refs.take.key ∉ other.storageKeys) :
    (roundPrefixStep (model := model) input refs store).1.read other = store.read other := by
  change ((((store.applyOp (addOp refs)).applyOp (squareOp refs)).applyOp
    (compareOp input refs)).applyOp (takeOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (takeOp refs) other takeAvoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (compareOp input refs) other tooLargeAvoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (squareOp refs) other squareAvoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (addOp refs) other midCarryAvoids]

/-- The actual prefix materializes the original midpoint and its exact acceptance flag. -/
lemma roundPrefixStep_values {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (separated : Separation input refs) (store : Store ctx)
    (initial : RoundInitial input refs store) :
    ((roundPrefixStep (model := model) input refs store).1.read (.first (writeInput
      refs.midCarry))).toNat =
        midpoint refs store ∧
      ((roundPrefixStep (model := model) input refs store).1.read (writeInput refs.take)).toBool =
        decide (midpoint refs store * midpoint refs store ≤ (store.read input).toNat) := by
  rcases separated with ⟨inputAvoids, injective⟩
  have keyNe : ∀ {left right : Cell}, left ≠ right →
      writeKey refs left ≠ writeKey refs right := by
    intro left right different equal
    exact different (injective equal)
  have midCarryAvoidsSquare :
      refs.square.toCStorageRef.key ∉ (CInputRef.first (writeInput refs.midCarry)).storageKeys := by
    apply storageRead_not_mem
    exact keyNe (left := .midCarry) (right := .square) (by intro equal; cases equal)
  have midCarryAvoidsTooLarge :
      refs.tooLarge.toCStorageRef.key ∉
        (CInputRef.first (writeInput refs.midCarry)).storageKeys := by
    apply storageRead_not_mem
    exact keyNe (left := .midCarry) (right := .tooLarge) (by intro equal; cases equal)
  have midCarryAvoidsTake :
      refs.take.toCStorageRef.key ∉ (CInputRef.first (writeInput refs.midCarry)).storageKeys := by
    apply storageRead_not_mem
    exact keyNe (left := .midCarry) (right := .take) (by intro equal; cases equal)
  let afterAdd := store.applyOp (addOp refs)
  let afterSquare := afterAdd.applyOp (squareOp refs)
  let afterCompare := afterSquare.applyOp (compareOp input refs)
  let afterTake := afterCompare.applyOp (takeOp refs)
  have addWritten := Store.read_applyOp_output store (addOp refs)
  have squareWritten := Store.read_applyOp_output afterAdd (squareOp refs)
  have compareWritten := Store.read_applyOp_output afterSquare (compareOp input refs)
  have takeWritten := Store.read_applyOp_output afterCompare (takeOp refs)
  have prefixEval : (roundPrefixStep (model := model) input refs store).1 = afterTake := rfl
  have midpointAtAdd :
      (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat =
        midpoint refs store := by
    have written := congrArg (fun value => value.first.toNat) addWritten
    change (afterAdd.read (writeInput refs.midCarry)).first.toNat =
      ((addOp refs).eval (store.read
        (.product (writeInput refs.root) (writeInput refs.half)))).first.toNat at written
    rw [read_product] at written
    have midpointMod : (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat =
        ((store.read (writeInput refs.root)).toNat +
          (store.read (writeInput refs.half)).toNat) % CShape.wordModulus width := by
      calc
        (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat =
            ((addOp refs).eval (.product (store.read (writeInput refs.root))
              (store.read (writeInput refs.half)))).first.toNat := written
        _ = ((store.read (writeInput refs.root)).toNat +
            (store.read (writeInput refs.half)).toNat) % CShape.wordModulus width := by
          exact ClassicalOp.eval_addCarry_low width ctx
            (.product (writeInput refs.root) (writeInput refs.half)) refs.midCarry
            (.product (store.read (writeInput refs.root))
              (store.read (writeInput refs.half)))
    unfold midpoint
    rw [midpointMod, Nat.mod_eq_of_lt initial.1]
  have squareAtSquare : (afterSquare.read (writeInput refs.square)).toNat =
      midpoint refs store * midpoint refs store := by
    have squareRead : afterSquare.read (writeInput refs.square) =
        (squareOp refs).eval (afterAdd.read
          (.product (CInputRef.first (writeInput refs.midCarry))
            (CInputRef.first (writeInput refs.midCarry)))) := by
      change afterSquare.read (writeInput refs.square) = _ at squareWritten
      exact squareWritten
    have squareNat := congrArg CShape.Value.toNat squareRead
    rw [read_product] at squareNat
    have squareExact : (afterSquare.read (writeInput refs.square)).toNat =
        (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat *
          (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat := by
      calc
        (afterSquare.read (writeInput refs.square)).toNat =
            ((squareOp refs).eval
              (.product (afterAdd.read (CInputRef.first (writeInput refs.midCarry)))
                (afterAdd.read (CInputRef.first (writeInput refs.midCarry))))).toNat := squareNat
        _ = (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat *
            (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat := by
          exact ClassicalOp.eval_mulFull_exact width width ctx
            (.product (CInputRef.first (writeInput refs.midCarry))
              (CInputRef.first (writeInput refs.midCarry))) refs.square
            (.product (afterAdd.read (CInputRef.first (writeInput refs.midCarry)))
              (afterAdd.read (CInputRef.first (writeInput refs.midCarry))))
    rw [squareExact, midpointAtAdd]
  have inputAfterAdd : afterAdd.read input = store.read input :=
    Store.read_applyOp_of_not_mem_storageKeys store (addOp refs) _ (inputAvoids .midCarry)
  have inputAfterSquare : afterSquare.read input = store.read input :=
    (Store.read_applyOp_of_not_mem_storageKeys afterAdd (squareOp refs) _
      (inputAvoids .square)).trans inputAfterAdd
  have tooLargeAtCompare : (afterCompare.read (writeInput refs.tooLarge)).toBool =
      decide ((store.read input).toNat <
        midpoint refs store * midpoint refs store) := by
    have compareRead : afterCompare.read (writeInput refs.tooLarge) =
        (compareOp input refs).eval (afterSquare.read
          (.product input (writeInput refs.square))) := by
      change afterCompare.read (writeInput refs.tooLarge) = _ at compareWritten
      exact compareWritten
    have compareBool := congrArg CShape.Value.toBool compareRead
    rw [read_product] at compareBool
    simpa only [compareOp, ClassicalOp.eval_wordBinary, Resource.WordBinaryOpcode.eval,
      CShape.Value.first, CShape.Value.second, CShape.Value.toBool,
      inputAfterSquare, squareAtSquare] using compareBool
  have takeValue : (afterTake.read (writeInput refs.take)).toBool =
      decide (midpoint refs store * midpoint refs store ≤
        (store.read input).toNat) := by
    have takeRead : afterTake.read (writeInput refs.take) =
        (takeOp refs).eval (afterCompare.read (writeInput refs.tooLarge)) := by
      change afterTake.read (writeInput refs.take) = _ at takeWritten
      exact takeWritten
    have takeBool := congrArg CShape.Value.toBool takeRead
    have takeEvaluated :
        ((takeOp refs).eval
          (afterCompare.read (writeInput refs.tooLarge))).toBool =
            !(afterCompare.read (writeInput refs.tooLarge)).toBool := by
      change (Resource.BitOpcode.not.eval
        (afterCompare.read (writeInput refs.tooLarge))).toBool = _
      exact bitNotEval_toBool _
    have takeNot : (afterTake.read (writeInput refs.take)).toBool =
        !(afterCompare.read (writeInput refs.tooLarge)).toBool :=
      takeBool.trans takeEvaluated
    rw [takeNot, tooLargeAtCompare]
    by_cases selected : midpoint refs store * midpoint refs store ≤
        (store.read input).toNat
    · have notTooLarge : ¬ (store.read input).toNat <
        midpoint refs store * midpoint refs store := Nat.not_lt.mpr selected
      simp [selected, notTooLarge]
    · have tooLarge : (store.read input).toNat <
        midpoint refs store * midpoint refs store := Nat.lt_of_not_ge selected
      simp [selected, tooLarge]
  have midpointAfterTake :
      (afterTake.read (CInputRef.first (writeInput refs.midCarry))).toNat =
        midpoint refs store := by
    have midAfterSquare :
        (afterSquare.read (CInputRef.first (writeInput refs.midCarry))).toNat =
          (afterAdd.read (CInputRef.first (writeInput refs.midCarry))).toNat :=
      congrArg CShape.Value.toNat
        (Store.read_applyOp_of_not_mem_storageKeys afterAdd (squareOp refs) _
          midCarryAvoidsSquare)
    have midAfterCompare :
        (afterCompare.read (CInputRef.first (writeInput refs.midCarry))).toNat =
          (afterSquare.read (CInputRef.first (writeInput refs.midCarry))).toNat :=
      congrArg CShape.Value.toNat
        (Store.read_applyOp_of_not_mem_storageKeys afterSquare (compareOp input refs) _
          midCarryAvoidsTooLarge)
    have midAfterTake :
        (afterTake.read (CInputRef.first (writeInput refs.midCarry))).toNat =
          (afterCompare.read (CInputRef.first (writeInput refs.midCarry))).toNat :=
      congrArg CShape.Value.toNat
        (Store.read_applyOp_of_not_mem_storageKeys afterCompare (takeOp refs) _
          midCarryAvoidsTake)
    exact midAfterTake.trans (midAfterCompare.trans (midAfterSquare.trans midpointAtAdd))
  rw [prefixEval]
  exact ⟨midpointAfterTake, takeValue⟩

private lemma rootOp_value {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (flag : Bool) (store : Store ctx) :
    ((store.applyOp (rootOp refs flag)).read (writeInput refs.root)).toNat =
      if flag then (store.read (.first (writeInput refs.midCarry))).toNat
      else (store.read (writeInput refs.root)).toNat := by
  cases flag with
  | false =>
    exact congrArg CShape.Value.toNat (Store.read_applyOp_output store (rootOp refs false))
  | true =>
    exact congrArg CShape.Value.toNat (Store.read_applyOp_output store (rootOp refs true))

private lemma halfOp_value {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (halfOp refs)).read (writeInput refs.half)).toNat =
      (store.read (writeInput refs.half)).toNat / 2 := by
  have written := congrArg CShape.Value.toNat (Store.read_applyOp_output store (halfOp refs))
  change ((store.applyOp (halfOp refs)).read (writeInput refs.half)).toNat =
    (CShape.wordOfNat width ((store.read (writeInput refs.half)).toNat / 2)).toNat at written
  have fits : (store.read (writeInput refs.half)).toNat / 2 < CShape.wordModulus width :=
    lt_of_le_of_lt (Nat.div_le_self _ 2) (store.read (writeInput refs.half)).toNat_lt
  rw [CShape.wordOfNat_val, Nat.mod_eq_of_lt fits] at written
  exact written

/-- The complete actual round frames every original read outside its six destinations. -/
lemma roundInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, writeKey refs cell ∉ other.storageKeys) :
    (roundStep (model := model) input refs store).1.read other = store.read other := by
  let prefixResult := (roundPrefixStep (model := model) input refs store).1
  let chosen := (prefixResult.read (writeInput refs.take)).toBool
  change ((prefixResult.applyOp (rootOp refs chosen)).applyOp (halfOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (halfOp refs) other (avoids .half),
    Store.read_applyOp_of_not_mem_storageKeys _ (rootOp refs chosen) other (avoids .root)]
  exact roundPrefixInto_callerFrame input refs store other (avoids .midCarry)
    (avoids .square) (avoids .tooLarge) (avoids .take)

/-- One actual refinement round implements the original binary choice and retains its interval. -/
lemma roundStep_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width)
    (separated : Separation input refs) (store : Store ctx)
    (initial : RoundInitial input refs store) :
    RoundOutcome input refs store (roundStep (model := model) input refs store).1 := by
  have keyNe : ∀ {left right : Cell}, left ≠ right →
      writeKey refs left ≠ writeKey refs right := by
    intro left right different equal
    exact different (separated.2 equal)
  have rootAvoids {cell : Cell} (different : Cell.root ≠ cell) :
      writeKey refs cell ∉ (writeInput refs.root).storageKeys :=
    storageRead_not_mem (keyNe different)
  have halfAvoids {cell : Cell} (different : Cell.half ≠ cell) :
      writeKey refs cell ∉ (writeInput refs.half).storageKeys :=
    storageRead_not_mem (keyNe different)
  let prefixResult := (roundPrefixStep (model := model) input refs store).1
  let chosen := (prefixResult.read (writeInput refs.take)).toBool
  let afterRoot := prefixResult.applyOp (rootOp refs chosen)
  have prefixValues := roundPrefixStep_values (model := model) input refs separated store initial
  have rootAfterPrefix : prefixResult.read (writeInput refs.root) =
      store.read (writeInput refs.root) :=
    roundPrefixInto_callerFrame input refs store _
      (rootAvoids (cell := .midCarry) (by intro equal; cases equal))
      (rootAvoids (cell := .square) (by intro equal; cases equal))
      (rootAvoids (cell := .tooLarge) (by intro equal; cases equal))
      (rootAvoids (cell := .take) (by intro equal; cases equal))
  have halfAfterPrefix : prefixResult.read (writeInput refs.half) =
      store.read (writeInput refs.half) :=
    roundPrefixInto_callerFrame input refs store _
      (halfAvoids (cell := .midCarry) (by intro equal; cases equal))
      (halfAvoids (cell := .square) (by intro equal; cases equal))
      (halfAvoids (cell := .tooLarge) (by intro equal; cases equal))
      (halfAvoids (cell := .take) (by intro equal; cases equal))
  have rootAtRoot : (afterRoot.read (writeInput refs.root)).toNat =
      selectedRoot input refs store := by
    change ((prefixResult.applyOp (rootOp refs chosen)).read (writeInput refs.root)).toNat = _
    rw [rootOp_value]
    change (if (prefixResult.read (writeInput refs.take)).toBool then _ else _) = _
    rw [prefixValues.2]
    by_cases selected : midpoint refs store * midpoint refs store ≤ (store.read input).toNat
    · simpa only [selectedRoot, selected, decide_true, if_true] using prefixValues.1
    · simp only [selectedRoot, selected, decide_false, Bool.false_eq_true, if_false]
      exact congrArg CShape.Value.toNat rootAfterPrefix
  have rootAfterHalf := Store.read_applyOp_of_not_mem_storageKeys afterRoot (halfOp refs)
    (writeInput refs.root) (rootAvoids (cell := .half) (by intro equal; cases equal))
  have halfAfterRoot := Store.read_applyOp_of_not_mem_storageKeys prefixResult (rootOp refs chosen)
    (writeInput refs.half) (halfAvoids (cell := .root) (by intro equal; cases equal))
  have finalRoot : ((roundStep (model := model) input refs store).1.read (writeInput
    refs.root)).toNat =
      selectedRoot input refs store :=
    (congrArg CShape.Value.toNat rootAfterHalf).trans rootAtRoot
  have finalHalf : ((roundStep (model := model) input refs store).1.read (writeInput
    refs.half)).toNat =
      (store.read (writeInput refs.half)).toNat / 2 := by
    change ((afterRoot.applyOp (halfOp refs)).read (writeInput refs.half)).toNat = _
    rw [halfOp_value, halfAfterRoot, halfAfterPrefix]
  have bounds : selectedRoot input refs store * selectedRoot input refs store ≤
      (store.read input).toNat ∧
      (store.read input).toNat <
        (selectedRoot input refs store + (store.read (writeInput refs.half)).toNat) *
          (selectedRoot input refs store + (store.read (writeInput refs.half)).toNat) :=
    roundArithmetic_bounds initial
  refine ⟨finalRoot, finalHalf, ?_, ?_, roundInto_callerFrame input refs store⟩
  · rw [finalRoot]
    exact bounds.1
  · rw [finalRoot]
    exact bounds.2

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

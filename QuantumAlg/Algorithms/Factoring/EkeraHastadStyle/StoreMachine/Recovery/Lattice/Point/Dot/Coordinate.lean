/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Coordinate

/-!
# Actual lattice multiply-accumulate

Two native classical operations update one accumulator using one shared product
word. The equations use the actual circuit interpreter and preserve all input
quantum-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDot

open ClassicalRoutines.NumberTheory.SignedWord
open Execution
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Separation needed by one multiply-then-add coordinate update. -/
structure CoordinateAccumulateSeparation {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {width : Nat}
    (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) : Prop where
  leftAvoidsProduct :
    product.toCStorageRef.key ∉ left.storageKeys
  rightAvoidsProduct : product.toCStorageRef.key ∉ right.storageKeys
  accumulatorAvoidsProduct :
    product.toCStorageRef.key ∉ (writeInput accumulator).storageKeys
  leftAvoidsAccumulator : accumulator.toCStorageRef.key ∉ left.storageKeys
  rightAvoidsAccumulator : accumulator.toCStorageRef.key ∉ right.storageKeys
  productAvoidsAccumulator :
    accumulator.toCStorageRef.key ∉ (writeInput product).storageKeys

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual low-word multiplication writes the shared product cell. -/
def coordinateProductOp (left right : CInputRef ctx (.unsignedWord width))
    (product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product left right) product

/-- The actual addition reads the accumulator and the newly written product. -/
def coordinateAddOp (accumulator product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx (.product (writeInput accumulator) (writeInput product)) accumulator

/-- Replace the accumulator by accumulator plus left times right modulo the raw width. -/
def coordinateAccumulate (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (coordinateProductOp left right product))
    (.classical (coordinateAddOp accumulator product))

/-- The two actual instruction updates on the classical store. -/
def coordinateStore (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (store.applyOp (coordinateProductOp left right product)).applyOp
    (coordinateAddOp accumulator product)

/-- The complete incoming quantum-reference blocks follow these actual store updates. -/
theorem coordinateAccumulate_execute (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : Execution.State ctx Reference History) :
    (coordinateAccumulate left right accumulator product).execute Reference state =
      state.mapClassical (fun entry =>
        (coordinateStore left right accumulator product entry.1, (entry.2, ((), ())))) := by
  simp only [coordinateAccumulate, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Every actual coordinate path contains exactly the native multiply and addition. -/
theorem coordinateAccumulate_events (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (path : (coordinateAccumulate left right accumulator product).Path) :
    (coordinateAccumulate left right accumulator product).eventTrace path =
      [.classicalOperation (.wordBinary .mulLow width),
        .classicalOperation (.wordBinary .add width)] := rfl

/-- Reads outside the two actual writes are preserved, with no operand-separation premise. -/
theorem coordinateAccumulate_callerFrame
    (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsProduct : product.key ∉ other.storageKeys)
    (avoidsAccumulator : accumulator.key ∉ other.storageKeys) :
    (coordinateStore left right accumulator product store).read other = store.read other := by
  unfold coordinateStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsAccumulator,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsProduct]

/-- Actual coordinate readout and all caller reads outside the two writes. -/
def CoordinateAccumulateRelation (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (before after : Store ctx) : Prop :=
  (∀ leftValue rightValue accumulatorValue : Int,
    RawSignedRepresents (before.read left) leftValue →
      RawSignedRepresents (before.read right) rightValue →
        RawSignedRepresents (before.read (writeInput accumulator)) accumulatorValue →
          RawSignedRepresents (after.read (writeInput accumulator))
            (accumulatorValue + leftValue * rightValue)) ∧
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      product.key ∉ other.storageKeys → accumulator.key ∉ other.storageKeys →
        after.read other = before.read other)

/-- The two real updates implement signed addition of the product modulo the word width. -/
theorem coordinateAccumulate_correct (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width))
    (separation : CoordinateAccumulateSeparation left right accumulator product)
    (store : Store ctx) :
    CoordinateAccumulateRelation left right accumulator product store
      (coordinateStore left right accumulator product store) := by
  refine ⟨?_, coordinateAccumulate_callerFrame left right accumulator product store⟩
  intro leftValue rightValue accumulatorValue leftRep rightRep accumulatorRep
  let multiplied := store.applyOp (coordinateProductOp left right product)
  have productRep : RawSignedRepresents (multiplied.read (writeInput product))
      (leftValue * rightValue) := by
    change RawSignedRepresents
      ((store.applyOp (coordinateProductOp left right product)).read
        (.storage (coordinateProductOp left right product).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    exact rawSignedWordRepresents_mulLow (store.read left) (store.read right)
      leftValue rightValue leftRep rightRep
  have accumulatorFrame : multiplied.read (writeInput accumulator) =
      store.read (writeInput accumulator) :=
    Store.read_applyOp_of_not_mem_storageKeys store
      (coordinateProductOp left right product) (writeInput accumulator)
      separation.accumulatorAvoidsProduct
  change RawSignedRepresents
    ((multiplied.applyOp (coordinateAddOp accumulator product)).read
      (.storage (coordinateAddOp accumulator product).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  change RawSignedRepresents
    (Resource.WordBinaryOpcode.eval .add width
      (.product (multiplied.read (writeInput accumulator))
        (multiplied.read (writeInput product)))) _
  apply rawSignedWordRepresents_add _ _ accumulatorValue (leftValue * rightValue)
  · rw [accumulatorFrame]
    exact accumulatorRep
  · exact productRep

/-- Every coordinate accumulation preserves the complete borrowed interface. -/
theorem coordinateAccumulate_borrowedRestored
    (left right : CInputRef ctx (.unsignedWord width))
    (accumulator product : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (coordinateAccumulate left right accumulator product).BorrowedRestored Reference state
      ((coordinateAccumulate left right accumulator product).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical _ state) (Circuit.borrowedRestored_classical _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeDot

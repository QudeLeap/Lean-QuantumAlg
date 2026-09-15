/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord

/-!
# Actual difference of two products

Two native multiplications and one subtraction write the actual output.
The original words represent integers modulo the same width, including width
zero; all values are read from chronological circuit stores.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.ProductDifference

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Multiply two actual raw words into the supplied destination. -/
def productOp (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product left right) output

/-- The subtraction reads the two actual stored products into the output. -/
def subtractProductsOp (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx
    (.product (.storage productLeft.toCStorageRef) (.storage productRight.toCStorageRef)) output

/-- Native multiplication, multiplication and subtraction for one difference of products. -/
def computeInto (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (productOp a b productLeft))
    (.seq (.classical (productOp c d productRight))
      (.classical (subtractProductsOp output productLeft productRight)))

/-- The three actual chronological writes of one difference of products. -/
def computedStore (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  ((store.applyOp (productOp a b productLeft)).applyOp
    (productOp c d productRight)).applyOp
      (subtractProductsOp output productLeft productRight)

/-- The complete arithmetic interpreter retains the original history and quantum-reference block. -/
theorem computeInto_execute (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (computeInto a b c d output productLeft productRight).execute Reference state =
      state.mapClassical (fun entry => (computedStore a b c d output productLeft productRight
        entry.1, (entry.2, ((), ((), ()))))) := by
  simp only [computeInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- All reads outside the three actual output keys remain unchanged. -/
theorem computeInto_callerFrame (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsOutput : output.key ∉ other.storageKeys)
    (avoidsLeft : productLeft.key ∉ other.storageKeys)
    (avoidsRight : productRight.key ∉ other.storageKeys) :
    (computedStore a b c d output productLeft productRight store).read other =
      store.read other := by
  unfold computedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsOutput,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsRight,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoidsLeft]

/-- The real output represents the difference of the original two integer products. -/
theorem computeInto_correct (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (cAvoidsLeft : productLeft.key ∉ c.storageKeys)
    (dAvoidsLeft : productLeft.key ∉ d.storageKeys)
    (productsDifferent : productRight.key ≠ productLeft.key)
    (av bv cv dv : Int) (aRep : RawSignedRepresents (store.read a) av)
    (bRep : RawSignedRepresents (store.read b) bv)
    (cRep : RawSignedRepresents (store.read c) cv)
    (dRep : RawSignedRepresents (store.read d) dv) :
    RawSignedRepresents ((computedStore a b c d output productLeft productRight store).read
      (.storage output.toCStorageRef)) (av * bv - cv * dv) := by
  let first := store.applyOp (productOp a b productLeft)
  let second := first.applyOp (productOp c d productRight)
  have leftValue : RawSignedRepresents
      (first.read (.storage productLeft.toCStorageRef)) (av * bv) := by
    change RawSignedRepresents ((store.applyOp
      (productOp a b productLeft)).read
        (.storage
          (productOp a b productLeft).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    exact rawSignedWordRepresents_mulLow _ _ av bv aRep bRep
  have rightValue : RawSignedRepresents
      (second.read (.storage productRight.toCStorageRef)) (cv * dv) := by
    change RawSignedRepresents ((first.applyOp
      (productOp c d productRight)).read
        (.storage
          (productOp c d productRight).outputRef.toCStorageRef)) _
    rw [Store.read_applyOp_output]
    apply rawSignedWordRepresents_mulLow (first.read c) (first.read d) cv dv
    · rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ cAvoidsLeft]
      exact cRep
    · rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ dAvoidsLeft]
      exact dRep
  have leftFrame : second.read (.storage productLeft.toCStorageRef) =
      first.read (.storage productLeft.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys first
      (productOp c d productRight) (.storage productLeft.toCStorageRef)
      (by
        change productRight.key ∉ (CInputRef.storage productLeft.toCStorageRef).storageKeys
        simpa only [CInputRef.storageKeys, List.mem_singleton] using productsDifferent)
  change RawSignedRepresents
    ((second.applyOp (subtractProductsOp output productLeft productRight)).read
      (.storage (subtractProductsOp output productLeft productRight).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  apply rawSignedWordRepresents_sub (second.read (.storage productLeft.toCStorageRef))
    (second.read (.storage productRight.toCStorageRef)) (av * bv) (cv * dv)
  · rw [leftFrame]; exact leftValue
  · exact rightValue

/-- All borrowed classical and quantum correlations survive the three actual arithmetic writes. -/
theorem computeInto_borrowedRestored (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (computeInto a b c d output productLeft productRight).BorrowedRestored Reference state
      ((computeInto a b c d output productLeft productRight).execute Reference state) := by
  exact Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (Circuit.borrowedRestored_seq _ _ _ (Circuit.borrowedRestored_classical _ _)
      (Circuit.borrowedRestored_classical _ _))

/-- Independent three-operation native instruction formula. -/
def operationTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .sub width)]

/-- Every actual path emits the two multiplications followed by the subtraction. -/
theorem computeInto_events (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (computeInto a b c d output productLeft productRight).Path) :
    (computeInto a b c d output productLeft productRight).eventTrace path =
      operationTrace width := rfl

/-- All three actual native operations are sequentially dependent. -/
theorem computeInto_depth (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (computeInto a b c d output productLeft productRight).Path) :
    (computeInto a b c d output productLeft productRight).depth (fun _ => 1) path = 3 := rfl

/-- All three operations visit the original supplied context without allocating storage. -/
theorem computeInto_visited (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (path : (computeInto a b c d output productLeft productRight).Path) :
    (computeInto a b c d output productLeft productRight).visitedContexts path =
      [ctx, ctx, ctx] := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.SignedWord.ProductDifference

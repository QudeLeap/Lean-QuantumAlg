/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.ProductDifference

/-!
# Actual cross-product coordinate

Two native multiplications and one subtraction write the actual coordinate.
The original words represent integers modulo the same width, including width
zero; all values are read from chronological circuit stores.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The subtraction reads the two actual stored products into the coordinate output. -/
def subtractProductsOp (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  ProductDifference.subtractProductsOp output productLeft productRight

/-- Native multiplication, multiplication and subtraction for one cross-product coordinate. -/
def coordinateCross {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  ProductDifference.computeInto a b c d output productLeft productRight

/-- The three actual chronological writes of one cross-product coordinate. -/
def coordinateStore (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  ProductDifference.computedStore a b c d output productLeft productRight store

/-- Actual selected stores and operation paths of one cross-product coordinate. -/
def coordinateStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    Store ctx × (coordinateCross (model := model) a b c d output productLeft productRight).Path :=
  ProductDifference.computationStep (model := model) a b c d output productLeft productRight
    store

lemma coordinateStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (coordinateStep (model := model) a b c d output productLeft productRight store).1 =
      coordinateStore a b c d output productLeft productRight store := rfl

/-- The complete coordinate interpreter retains the original history and quantum-reference block. -/
lemma coordinateCross_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (coordinateCross (model := model) a b c d output productLeft productRight).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := coordinateStep (model := model) a b c d output productLeft productRight
          entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  ProductDifference.computeInto_execute a b c d output productLeft productRight Reference state

/-- All reads outside the three actual output keys remain unchanged. -/
lemma coordinateCross_callerFrame (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsOutput : output.key ∉ other.storageKeys)
    (avoidsLeft : productLeft.key ∉ other.storageKeys)
    (avoidsRight : productRight.key ∉ other.storageKeys) :
    (coordinateStore a b c d output productLeft productRight store).read other =
      store.read other :=
  ProductDifference.computeInto_callerFrame a b c d output productLeft productRight store other
    avoidsOutput avoidsLeft avoidsRight

/-- The real output represents the difference of the original two integer products. -/
lemma coordinateCross_correct (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (cAvoidsLeft : productLeft.key ∉ c.storageKeys)
    (dAvoidsLeft : productLeft.key ∉ d.storageKeys)
    (productsDifferent : productRight.key ≠ productLeft.key)
    (av bv cv dv : Int) (aRep : RawSignedRepresents (store.read a) av)
    (bRep : RawSignedRepresents (store.read b) bv)
    (cRep : RawSignedRepresents (store.read c) cv)
    (dRep : RawSignedRepresents (store.read d) dv) :
    RawSignedRepresents ((coordinateStore a b c d output productLeft productRight store).read
      (writeInput output)) (av * bv - cv * dv) :=
  ProductDifference.computeInto_correct a b c d output productLeft productRight store
    cAvoidsLeft dAvoidsLeft productsDifferent av bv cv dv aRep bRep cRep dRep

/-- All borrowed classical and quantum correlations survive the three actual coordinate writes. -/
lemma coordinateCross_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (a b c d : CInputRef ctx (.unsignedWord width))
    (output productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (coordinateCross (model := model) a b c d output productLeft productRight).BorrowedRestored
      Reference state
      ((coordinateCross (model := model) a b c d output productLeft productRight).execute
        environment
        Reference state) :=
  ProductDifference.computeInto_borrowedRestored a b c d output productLeft productRight
    Reference state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

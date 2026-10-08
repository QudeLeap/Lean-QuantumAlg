/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Correctness

/-!
# Original quadratic center and natural truncated discriminant
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

/-- The three actual preparation writes preserve every read outside center and square. -/
theorem prepareInto_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (centerAvoids : refs.center.key ∉ other.storageKeys)
    (squareAvoids : refs.centerSquare.key ∉ other.storageKeys) :
    (prepareStep refs store).1.read other = store.read other := by
  change (((store.applyOp (resizeOp refs)).applyOp (incrementOp refs)).applyOp
    (squareOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (squareOp refs) other squareAvoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (incrementOp refs) other centerAvoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (resizeOp refs) other centerAvoids]

/-- All original caller reads outside the five pre-square-root operations survive. -/
theorem discriminantInto_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : PrefixFrameAvoids refs other) :
    (discriminantStep refs store).1.read other = store.read other :=
  (NatSub.into_callerFrame refs.subtract (prepareStep refs store).1 other
    avoids.subtractLessThan avoids.subtractOutput).trans
      (prepareInto_callerFrame refs store other avoids.center avoids.centerSquare)

/-- Actual widening, increment, full square and subtraction yield the original discriminant. -/
theorem discriminantStep_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) : DiscriminantOutcome refs store (discriminantStep refs store).1 := by
  let afterResize := store.applyOp (resizeOp refs)
  let afterIncrement := afterResize.applyOp (incrementOp refs)
  let afterSquare := afterIncrement.applyOp (squareOp refs)
  let afterSubtract := (NatSub.step refs.subtract afterSquare).1
  have resizeWritten := Store.read_applyOp_output store (resizeOp refs)
  have incrementWritten := Store.read_applyOp_output afterResize (incrementOp refs)
  have squareWritten := Store.read_applyOp_output afterIncrement (squareOp refs)
  have subtractHolds := NatSub.into_correct refs.subtract separation.subtract afterSquare
  have inputFits : (store.read refs.shortLog).toNat <
      CShape.wordModulus (centerWidth shortWidth) := by
    calc
      (store.read refs.shortLog).toNat < CShape.wordModulus shortWidth :=
        (store.read refs.shortLog).toNat_lt
      _ ≤ CShape.wordModulus (centerWidth shortWidth) := by
        unfold centerWidth CShape.wordModulus
        exact Nat.pow_le_pow_right (by omega) (by omega)
  have resized : (afterResize.read (writeInput refs.center)).toNat =
      (store.read refs.shortLog).toNat := by
    have written := congrArg CShape.Value.toNat resizeWritten
    change (afterResize.read (writeInput refs.center)).toNat =
      ((resizeOp refs).eval (store.read refs.shortLog)).toNat at written
    exact written.trans (by
      simpa only [resizeOp] using
        ClassicalOp.eval_wordResize_exact shortWidth (centerWidth shortWidth) ctx
          refs.shortLog refs.center (store.read refs.shortLog) inputFits)
  have incrementFits :
      (afterResize.read (writeInput refs.center)).toNat + 1 <
        CShape.wordModulus (centerWidth shortWidth) := by
    rw [resized]
    exact center_capacity refs store
  have incremented : (afterIncrement.read (writeInput refs.center)).toNat =
      (store.read refs.shortLog).toNat + 1 := by
    have written := congrArg CShape.Value.toNat incrementWritten
    change (afterIncrement.read (writeInput refs.center)).toNat =
      (CShape.wordOfNat (centerWidth shortWidth)
        ((afterResize.read (writeInput refs.center)).toNat + 1)).toNat at written
    rw [CShape.wordOfNat_val, Nat.mod_eq_of_lt incrementFits, resized] at written
    exact written
  have squared : (afterSquare.read (writeInput refs.centerSquare)).toNat =
      ((store.read refs.shortLog).toNat + 1) ^ 2 := by
    have written := congrArg CShape.Value.toNat squareWritten
    change (afterSquare.read (writeInput refs.centerSquare)).toNat =
      ((squareOp refs).eval (.product
        (afterIncrement.read (writeInput refs.center))
        (afterIncrement.read (writeInput refs.center)))).toNat at written
    calc
      (afterSquare.read (writeInput refs.centerSquare)).toNat =
          (afterIncrement.read (writeInput refs.center)).toNat *
            (afterIncrement.read (writeInput refs.center)).toNat := written.trans (by
              exact ClassicalOp.eval_mulFull_exact (centerWidth shortWidth)
                (centerWidth shortWidth) ctx
                (.product (writeInput refs.center) (writeInput refs.center))
                refs.centerSquare
                (.product (afterIncrement.read (writeInput refs.center))
                  (afterIncrement.read (writeInput refs.center))))
      _ = ((store.read refs.shortLog).toNat + 1) ^ 2 := by
        rw [incremented, pow_two]
  have modulusAtSquare : afterSquare.read refs.modulus = store.read refs.modulus :=
    (Store.read_applyOp_of_not_mem_storageKeys afterIncrement (squareOp refs)
      refs.modulus separation.modulusAvoidsSquare).trans
      ((Store.read_applyOp_of_not_mem_storageKeys afterResize (incrementOp refs)
        refs.modulus separation.modulusAvoidsCenter).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (resizeOp refs)
          refs.modulus separation.modulusAvoidsCenter))
  have discriminant :
      (afterSubtract.read (writeInput refs.subtract.output)).toNat =
        ((store.read refs.shortLog).toNat + 1) ^ 2 -
          (store.read refs.modulus).toNat := by
    have value := subtractHolds.1
    rw [refs.subtractLeft, refs.subtractRight, squared] at value
    change (afterSubtract.read (writeInput refs.subtract.output)).toNat =
      ((store.read refs.shortLog).toNat + 1) ^ 2 -
        (afterSquare.read refs.modulus).toNat at value
    rw [modulusAtSquare] at value
    exact value
  have centerAtSquare : afterSquare.read (writeInput refs.center) =
      afterIncrement.read (writeInput refs.center) :=
    Store.read_applyOp_of_not_mem_storageKeys afterIncrement (squareOp refs)
      (writeInput refs.center) separation.centerAvoidsSquare
  have centerAtSubtract : afterSubtract.read (writeInput refs.center) =
      afterSquare.read (writeInput refs.center) :=
    subtractHolds.2.2 (writeInput refs.center)
      separation.centerAvoidsSubtractLessThan separation.centerAvoidsSubtractOutput
  have squareAvoidsLessThan :
      refs.subtract.lessThan.toCStorageRef.key ∉ (writeInput refs.centerSquare).storageKeys := by
    rw [← refs.subtractLeft]
    exact separation.subtract.leftAvoidsLessThan
  have squareAtSubtract :
      afterSubtract.read (writeInput refs.centerSquare) =
        afterSquare.read (writeInput refs.centerSquare) :=
    subtractHolds.2.2 (writeInput refs.centerSquare) squareAvoidsLessThan
      separation.squareAvoidsSubtractOutput
  refine ⟨?_, ?_, discriminant, discriminantInto_callerFrame refs store⟩
  · exact (congrArg CShape.Value.toNat centerAtSubtract).trans
      ((congrArg CShape.Value.toNat centerAtSquare).trans incremented)
  · exact (congrArg CShape.Value.toNat squareAtSubtract).trans squared

/-- Every caller read outside the actual prefix and square-root writes survives execution. -/
theorem into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (prefixAvoids : PrefixFrameAvoids refs other) (sqrtAvoids : SqrtFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  (NatSqrt.into_callerFrame refs.sqrt (discriminantStep refs store).1 other
    sqrtAvoids.wideInput sqrtAvoids.round sqrtAvoids.output).trans
      (discriminantInto_callerFrame refs store other prefixAvoids)

/-- The actual circuit computes the original center, square, truncated discriminant and root. -/
theorem step_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) : Outcome refs store (step refs store).1 := by
  have prefixHolds := discriminantStep_correct refs separation store
  have positive : 0 < discriminantWidth shortWidth := by
    have atLeastTwo := discriminantWidth_two_le shortWidth
    omega
  have sqrtHolds := NatSqrt.step_correct refs.sqrt separation.sqrt positive
    (discriminantStep refs store).1
  have centerFrame := sqrtHolds.callerFrame (writeInput refs.center)
    separation.centerAvoidsSqrt.wideInput separation.centerAvoidsSqrt.round
    separation.centerAvoidsSqrt.output
  have squareFrame := sqrtHolds.callerFrame (writeInput refs.centerSquare)
    separation.squareAvoidsSqrt.wideInput separation.squareAvoidsSqrt.round
    separation.squareAvoidsSqrt.output
  have discriminantFrame := sqrtHolds.callerFrame (writeInput refs.subtract.output)
    separation.discriminantAvoidsSqrt.wideInput separation.discriminantAvoidsSqrt.round
    separation.discriminantAvoidsSqrt.output
  refine ⟨(congrArg CShape.Value.toNat centerFrame).trans prefixHolds.center,
    (congrArg CShape.Value.toNat squareFrame).trans prefixHolds.square,
    (congrArg CShape.Value.toNat discriminantFrame).trans prefixHolds.discriminant,
    ?_, into_callerFrame refs store⟩
  have output := sqrtHolds.output
  rw [refs.sqrtInput, prefixHolds.discriminant] at output
  exact output

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticPrefix

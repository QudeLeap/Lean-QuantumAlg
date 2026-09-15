/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Candidates.Prefix.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Correctness

/-!
# Exact actual natural quadratic candidates and complete caller preservation
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

open Execution
open ClassicalRoutines.NumberTheory
open QuadraticPrefix (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {shortWidth : Nat}

/-- The five actual suffix instructions preserve every read outside their writable cells. -/
theorem suffixInto_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (suffixStep refs store).1.read other = store.read other := by
  let afterCenter := store.applyOp (centerOp refs)
  let afterRoot := afterCenter.applyOp (rootOp refs)
  let afterFirst := (NatSub.step refs.first afterRoot).1
  exact (Store.read_applyOp_of_not_mem_storageKeys afterFirst (secondOp refs)
    other avoids.second).trans
    ((NatSub.into_callerFrame refs.first afterRoot other avoids.firstLessThan
      avoids.firstOutput).trans
      ((Store.read_applyOp_of_not_mem_storageKeys afterCenter (rootOp refs)
        other avoids.rootWide).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (centerOp refs)
          other avoids.centerWide)))

/-- The complete actual prefix and candidate writes retain the original seven-part frame. -/
theorem into_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other :=
  (suffixInto_callerFrame refs (QuadraticPrefix.step refs.quadraticPrefix store).1
    other avoids).trans
    (QuadraticPrefix.into_callerFrame refs.quadraticPrefix store other
      avoids.prefixAvoids avoids.sqrt)

/-- Original word widths suffice for both natural candidates and an actual false carry bit. -/
theorem step_correct (refs : Refs ctx shortWidth) (separation : Separation refs)
    (store : Store ctx) : Outcome refs store (step refs store).1 := by
  let afterPrefix := (QuadraticPrefix.step refs.quadraticPrefix store).1
  let afterCenter := afterPrefix.applyOp (centerOp refs)
  let afterRoot := afterCenter.applyOp (rootOp refs)
  let afterFirst := (NatSub.step refs.first afterRoot).1
  let afterSecond := afterFirst.applyOp (secondOp refs)
  let center := (store.read refs.quadraticPrefix.shortLog).toNat + 1
  let root := Nat.sqrt (center ^ 2 - (store.read refs.quadraticPrefix.modulus).toNat)
  have prefixHolds := QuadraticPrefix.step_correct refs.quadraticPrefix
    separation.prefixSeparation store
  have sumFits : center + root < CShape.wordModulus (candidateWidth shortWidth) :=
    candidate_capacity refs store
  have centerFits : center < CShape.wordModulus (candidateWidth shortWidth) := by omega
  have rootFits : root < CShape.wordModulus (candidateWidth shortWidth) := by omega
  have centerWritten : (afterCenter.read (writeInput refs.centerWide)).toNat = center := by
    have written := congrArg CShape.Value.toNat
      (Store.read_applyOp_output afterPrefix (centerOp refs))
    change (afterCenter.read (writeInput refs.centerWide)).toNat =
      ((centerOp refs).eval (afterPrefix.read
        (writeInput refs.quadraticPrefix.center))).toNat at written
    calc
      _ = (afterPrefix.read (writeInput refs.quadraticPrefix.center)).toNat :=
        written.trans (ClassicalOp.eval_wordResize_exact _ _ _ _ _ _
          (prefixHolds.center.trans_lt centerFits))
      _ = center := prefixHolds.center
  have rootAtCenter : afterCenter.read (writeInput refs.quadraticPrefix.sqrt.output) =
      afterPrefix.read (writeInput refs.quadraticPrefix.sqrt.output) :=
    Store.read_applyOp_of_not_mem_storageKeys afterPrefix (centerOp refs)
      (writeInput refs.quadraticPrefix.sqrt.output) separation.sqrtAvoidsCenterWide
  have rootWritten : (afterRoot.read (writeInput refs.rootWide)).toNat = root := by
    have written := congrArg CShape.Value.toNat
      (Store.read_applyOp_output afterCenter (rootOp refs))
    change (afterRoot.read (writeInput refs.rootWide)).toNat =
      ((rootOp refs).eval (afterCenter.read
        (writeInput refs.quadraticPrefix.sqrt.output))).toNat at written
    calc
      _ = (afterCenter.read (writeInput refs.quadraticPrefix.sqrt.output)).toNat :=
        written.trans (ClassicalOp.eval_wordResize_exact _ _ _ _ _ _
          (((congrArg CShape.Value.toNat rootAtCenter).trans prefixHolds.root).trans_lt rootFits))
      _ = root := (congrArg CShape.Value.toNat rootAtCenter).trans prefixHolds.root
  have centerAtRoot : afterRoot.read (writeInput refs.centerWide) =
      afterCenter.read (writeInput refs.centerWide) :=
    Store.read_applyOp_of_not_mem_storageKeys afterCenter (rootOp refs)
      (writeInput refs.centerWide) separation.centerWideAvoidsRootWide
  have centerValue : (afterRoot.read (writeInput refs.centerWide)).toNat = center :=
    (congrArg CShape.Value.toNat centerAtRoot).trans centerWritten
  have firstHolds := NatSub.into_correct refs.first separation.first afterRoot
  have firstValue : (afterFirst.read (firstCandidate refs)).toNat = center - root := by
    have value := firstHolds.1
    rw [refs.firstLeft, refs.firstRight, centerValue, rootWritten] at value
    exact value
  have centerAvoidsFlag :
      refs.first.lessThan.key ∉ (writeInput refs.centerWide).storageKeys := by
    rw [← refs.firstLeft]
    exact separation.first.leftAvoidsLessThan
  have rootAvoidsFlag : refs.first.lessThan.key ∉ (writeInput refs.rootWide).storageKeys := by
    rw [← refs.firstRight]
    exact separation.first.rightAvoidsLessThan
  have centerAtFirst : afterFirst.read (writeInput refs.centerWide) =
      afterRoot.read (writeInput refs.centerWide) :=
    firstHolds.2.2 (writeInput refs.centerWide) centerAvoidsFlag
      separation.centerWideAvoidsFirstOutput
  have rootAtFirst : afterFirst.read (writeInput refs.rootWide) =
      afterRoot.read (writeInput refs.rootWide) :=
    firstHolds.2.2 (writeInput refs.rootWide) rootAvoidsFlag
      separation.rootWideAvoidsFirstOutput
  have centerFinal : (afterFirst.read (writeInput refs.centerWide)).toNat = center :=
    (congrArg CShape.Value.toNat centerAtFirst).trans centerValue
  have rootFinal : (afterFirst.read (writeInput refs.rootWide)).toNat = root :=
    (congrArg CShape.Value.toNat rootAtFirst).trans rootWritten
  have firstAtSecond : afterSecond.read (firstCandidate refs) =
      afterFirst.read (firstCandidate refs) :=
    Store.read_applyOp_of_not_mem_storageKeys afterFirst (secondOp refs)
      (firstCandidate refs) separation.firstOutputAvoidsSecond
  have secondWritten := Store.read_applyOp_output afterFirst (secondOp refs)
  have secondValue : (afterSecond.read (secondCandidate refs)).toNat = center + root := by
    have written := congrArg (fun value => value.first.toNat) secondWritten
    change (afterSecond.read (secondCandidate refs)).toNat =
      ((secondOp refs).eval (.product (afterFirst.read (writeInput refs.centerWide))
        (afterFirst.read (writeInput refs.rootWide)))).first.toNat at written
    calc
      _ = ((afterFirst.read (writeInput refs.centerWide)).toNat +
          (afterFirst.read (writeInput refs.rootWide)).toNat) %
            CShape.wordModulus (candidateWidth shortWidth) :=
        written.trans (ClassicalOp.eval_addCarry_low _ _ _ _ _)
      _ = center + root := by rw [centerFinal, rootFinal, Nat.mod_eq_of_lt sumFits]
  have carryValue :
      (afterSecond.read (CInputRef.second (writeInput refs.second))).toBool = false := by
    have written := congrArg (fun value => value.second.toBool) secondWritten
    change (afterSecond.read (CInputRef.second (writeInput refs.second))).toBool =
      ((secondOp refs).eval (.product (afterFirst.read (writeInput refs.centerWide))
        (afterFirst.read (writeInput refs.rootWide)))).second.toBool at written
    calc
      _ = decide (CShape.wordModulus (candidateWidth shortWidth) ≤
          (afterFirst.read (writeInput refs.centerWide)).toNat +
            (afterFirst.read (writeInput refs.rootWide)).toNat) :=
        written.trans (ClassicalOp.eval_addCarry_flag _ _ _ _ _)
      _ = false := by rw [centerFinal, rootFinal]; exact decide_eq_false (by omega)
  exact ⟨(congrArg CShape.Value.toNat firstAtSecond).trans firstValue,
    secondValue, carryValue, into_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidates

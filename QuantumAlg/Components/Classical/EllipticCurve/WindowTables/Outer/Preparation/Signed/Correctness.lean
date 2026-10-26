/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Callback
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness

/-! # Complete execution and returned-Store correctness of paid signed preparation -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.Execution.ClassicalWorkspace
open QuantumAlg.ClassicalAlgorithms.EllipticCurve
open QuantumAlg.ClassicalRoutines.Modular.NativePower

noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma InputFree.outputs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (frame : Frame ctx width) {shape : CShape} (input : CInputRef ctx shape)
    (free : InputFree frame input) : OutputFree frame.coordinates input := by
  intro key member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact free 8
  · exact free 9
  · exact free 0
  · exact free 1
  · exact free 2
  · exact free 3

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

attribute [local irreducible] callbackRecord callbackStore Frame.initializationRecord

/-- Real lexical allocation and release return all proved rows in the caller's actual Store. -/
lemma scope_actualRecord_post (frame : Frame ctx width) (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width))
    (environment : model.Environment)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (secondOrder : addOrderOf second.toMathlib = order)
    (baseFree : InputFree frame base) (targetFree : InputFree frame target) :
    let code := withCells (model := model) ctx (scratchShapes width)
      (callbackBody frame curve.field base target)
    ∃ step : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × code.Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        code.execute environment Reference state = state.mapClassical (fun entry =>
          let result := step (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before, Constants frame curve before.1 →
        PointRepresents curve (before.1.read base) first.toMathlib →
        PointRepresents curve (before.1.read target) second.toMathlib →
        Constants frame curve (step before).1.1 ∧
          pairedRows curve frame first second (step before).1.1 ∧
          (step before).1.1.read base = before.1.read base ∧
          (step before).1.1.read target = before.1.read target := by
  apply withCells_actualRecord_post environment ctx (scratchShapes width)
    (callbackBody frame curve.field base target)
    (fun source returned => Constants frame curve source →
      PointRepresents curve (source.read base) first.toMathlib →
      PointRepresents curve (source.read target) second.toMathlib →
      Constants frame curve returned ∧ pairedRows curve frame first second returned ∧
        returned.read base = source.read base ∧ returned.read target = source.read target)
  intro inner cells distinct lift separated
  refine ⟨callbackRecord frame curve.field base target cells distinct lift separated environment,
    callbackBody_execute frame curve.field base target cells distinct lift separated environment,
    ?_⟩
  intro source before reads
  refine ⟨lift.restrict (callbackRecord frame curve.field base target cells distinct lift
    separated environment before).1.1, ?_, lift.workspaceTransport_restrict_readsAs _⟩
  intro constants baseRep targetRep
  exact callback_restricted_post frame curve base target cells distinct lift separated
    environment source before reads first second order prime large firstOrder secondOrder
    baseRep targetRep constants (baseFree.outputs frame base) (targetFree.outputs frame target)

/-- The actual loaders and increment establish all four constants and preserve P and Q. -/
lemma initializedStore_post (frame : Frame ctx width) (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width)) (store : Store ctx)
    (widthPositive : 0 < width)
    (baseFree : InputFree frame base) (targetFree : InputFree frame target)
    (zeroInitial : (store.read (.storage frame.zero.toCStorageRef)).toNat = 0)
    (oneInitial : (store.read (.storage frame.one.toCStorageRef)).toNat = 0) :
    let after := frame.initializedStore (model := model) curve.field curve.curve.a.val store
    Constants frame curve after ∧ after.read base = store.read base ∧
      after.read target = store.read target := by
  refine ⟨⟨frame.initializedStore_modulus curve.field curve.curve.a.val store,
    frame.initializedStore_zero_toNat curve.field curve.curve.a.val store zeroInitial,
    frame.initializedStore_one_toNat curve.field curve.curve.a.val store widthPositive oneInitial,
    frame.initializedStore_curveA_curveValue curve store⟩, ?_, ?_⟩
  · exact frame.initializedStore_read_other curve.field curve.curve.a.val store base
      (baseFree 4) (baseFree 7) (baseFree 6)
  · exact frame.initializedStore_read_other curve.field curve.curve.a.val store target
      (targetFree 4) (targetFree 7) (targetFree 6)

/-- Paid initialization and the exact signed callback establish the complete table postcondition. -/
lemma prepare_actualRecord_post (frame : Frame ctx width) (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width)) (environment : model.Environment)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (secondOrder : addOrderOf second.toMathlib = order)
    (widthPositive : 0 < width)
    (baseFree : InputFree frame base) (targetFree : InputFree frame target) :
    ∃ step : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (prepare (model := model) frame curve.field curve.curve.a.val base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (prepare (model := model) frame curve.field curve.curve.a.val base target).execute
          environment Reference state = state.mapClassical (fun entry =>
            let result := step (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before, PointRepresents curve (before.1.read base) first.toMathlib →
        PointRepresents curve (before.1.read target) second.toMathlib →
        (before.1.read (.storage frame.zero.toCStorageRef)).toNat = 0 →
        (before.1.read (.storage frame.one.toCStorageRef)).toNat = 0 →
        Constants frame curve (step before).1.1 ∧
          pairedRows curve frame first second (step before).1.1 ∧
          (step before).1.1.read base = before.1.read base ∧
          (step before).1.1.read target = before.1.read target := by
  rw [prepare_eq_named_callback]
  obtain ⟨tail, tailEquation, tailCorrect⟩ := scope_actualRecord_post frame curve base target
    environment first second order prime large firstOrder secondOrder baseFree targetFree
  let scope := withCells (model := model) ctx (scratchShapes width)
    (callbackBody frame curve.field base target)
  refine ⟨Circuit.sequenceRecord (frame.initializeConstants curve.field curve.curve.a.val)
    scope (frame.initializationRecord curve.field curve.curve.a.val) tail, ?_, ?_⟩
  · apply Circuit.execute_sequenceRecord
    · exact frame.initializeConstants_execute curve.field curve.curve.a.val environment
    · exact tailEquation
  · intro before baseRep targetRep zeroInitial oneInitial
    rw [Circuit.sequenceRecord_store]
    have initialized := initializedStore_post (model := model) frame curve base target before.1
      widthPositive baseFree targetFree zeroInitial oneInitial
    have same := frame.initializationRecord_store (model := model)
      curve.field curve.curve.a.val before
    have constants : Constants frame curve
        (frame.initializationRecord (model := model) curve.field curve.curve.a.val before).1.1 :=
      same.symm ▸ initialized.1
    have baseSame :
        (frame.initializationRecord (model := model) curve.field curve.curve.a.val before).1.1.read
          base = before.1.read base := by
      rw [same]
      exact initialized.2.1
    have targetSame :
        (frame.initializationRecord (model := model) curve.field curve.curve.a.val before).1.1.read
          target = before.1.read target := by
      rw [same]
      exact initialized.2.2
    have correct := tailCorrect
      (frame.initializationRecord curve.field curve.curve.a.val before).1 constants
      (by rw [baseSame]; exact baseRep) (by rw [targetSame]; exact targetRep)
    exact ⟨correct.1, correct.2.1, correct.2.2.1.trans baseSame,
      correct.2.2.2.trans targetSame⟩

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

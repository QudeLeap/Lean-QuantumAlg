/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Loop
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Trajectory

/-!
# Actual XGCD iteration follows the original bounded trajectory

The original input and fuel bound supply every signed range through the
original mathematical execution-state list. The actual loop therefore needs
no caller promise about intermediate coefficients. One record connects the
full interpreter equation, caller framing, readiness and decoded result.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual selected transitions follow every allowed prefix of the original mathematical run. -/
theorem xgcdNativeLoop_state (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (guardedActive cells zero).Path)
    (transition : ∀ before : Store ctx, storedReady cells zero before →
      ((storedState cells before).first ≠ 0 →
        ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState cells before)).firstLeftCoefficient ∧
        ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
          (PureXGCD.executionCoefficientWidth width)
          (PureXGCD.step (storedState cells before)).firstRightCoefficient) →
      storedReady cells zero (record before).1 ∧
        storedState cells (record before).1 =
          if (storedState cells before).first = 0 then storedState cells before
          else PureXGCD.step (storedState cells before))
    (count : Nat) (store : Store ctx) (input : PureXGCD.Input width)
    (ready : storedReady cells zero store)
    (initial : storedState cells store = PureXGCD.initialState input)
    (within : count ≤ ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width) :
    storedReady cells zero (iteratedActiveRecord cells zero record count store).1 ∧
      storedState cells (iteratedActiveRecord cells zero record count store).1 =
        PureXGCD.run count (PureXGCD.initialState input) := by
  let update := fun before : Store ctx => (record before).1
  have invariant : ∀ index : Nat, index ≤ count →
      storedReady cells zero ((update^[index]) store) ∧
        storedState cells ((update^[index]) store) =
          PureXGCD.run index (PureXGCD.initialState input) := by
    intro index
    induction index with
    | zero =>
        intro _
        exact ⟨ready, initial⟩
    | succ index inductionHypothesis =>
        intro indexBound
        have prior := inductionHypothesis (by omega)
        have actual := transition ((update^[index]) store) prior.1 (by
          intro active
          have pureActive : (PureXGCD.run index (PureXGCD.initialState input)).first ≠ 0 := by
            rw [← prior.2]
            exact active
          have ranges :=
            ClassicalAlgorithms.NumberTheory.XGCD.xgcdStep_run_initial_coefficients_representable
              (width := width) input index (by omega) pureActive
          rw [prior.2]
          exact ⟨ranges.1, ranges.2.1⟩)
        rw [Function.iterate_succ_apply']
        refine ⟨actual.1, ?_⟩
        rw [actual.2, prior.2]
        exact (ClassicalAlgorithms.NumberTheory.XGCD.xgcdRun_succ_last
          index (PureXGCD.initialState input)).symm
  exact invariant count le_rfl

/-- The actual loop record discharges all intermediate ranges from the original input and fuel. -/
theorem xgcdNativeLoop_actualRecord
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys) (count : Nat) :
    ∃ record : Store ctx → Store ctx × (Circuit.iterate count (guardedActive cells zero)).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (Circuit.iterate count (guardedActive cells zero)).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ index : Fin 7, stateKey cells index ∉ other.storageKeys) →
            ((record before).1).read other = before.read other) ∧
        (∀ input : PureXGCD.Input width, storedReady cells zero before →
          storedState cells before = PureXGCD.initialState input →
          count ≤ ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width →
          storedReady cells zero (record before).1 ∧
            storedState cells (record before).1 =
              PureXGCD.run count (PureXGCD.initialState input)) := by
  obtain ⟨bodyRecord, equation, correct⟩ :=
    xgcdNativeGuardedActive_actualRecord (width := width) cells distinct zero stateZero
  refine ⟨iteratedActiveRecord cells zero bodyRecord count,
    xgcdNativeLoop_execute cells zero bodyRecord equation count, ?_⟩
  intro before
  constructor
  · intro shape other free
    exact xgcdNativeLoop_read_other cells zero bodyRecord other
      (fun store => (correct store).1 other free) count before
  · intro input ready initial within
    exact xgcdNativeLoop_state (width := width) cells zero bodyRecord
      (fun store => (correct store).2) count before input ready initial within

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

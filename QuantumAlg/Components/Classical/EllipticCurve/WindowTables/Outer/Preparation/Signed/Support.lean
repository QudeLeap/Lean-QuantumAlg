/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Correctness
import all QuantumAlg.Core.Execution.State.Support

/-! # Actual positive-block support after paid signed preparation -/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.ClassicalAlgorithms.EllipticCurve
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Every reachable returned Store contains the proved constants, rows and original input points. -/
lemma prepare_post_on_support (frame : Frame ctx width) (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width)) (environment : model.Environment)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (secondOrder : addOrderOf second.toMathlib = order)
    (widthPositive : 0 < width)
    (baseFree : InputFree frame base) (targetFree : InputFree frame target)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (initial : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read base) first.toMathlib ∧
        PointRepresents curve (entry.1.read target) second.toMathlib ∧
        (entry.1.read (.storage frame.zero.toCStorageRef)).toNat = 0 ∧
        (entry.1.read (.storage frame.one.toCStorageRef)).toNat = 0)
    (value : Store ctx × (model.HiddenState × (History ×
      (prepare (model := model) frame curve.field curve.curve.a.val base target).Path)))
    (positive : 0 < (((prepare (model := model) frame curve.field curve.curve.a.val
      base target).execute environment Reference state).block value).mass) :
    Constants frame curve value.1 ∧ pairedRows curve frame first second value.1 ∧
      PointRepresents curve (value.1.read base) first.toMathlib ∧
      PointRepresents curve (value.1.read target) second.toMathlib := by
  obtain ⟨step, equation, correct⟩ := prepare_actualRecord_post frame curve base target
    environment first second order prime large firstOrder secondOrder widthPositive
    baseFree targetFree
  rw [equation] at positive
  obtain ⟨before, same, beforePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff state _ value).mp positive
  have established := initial before beforePositive
  have post := correct (before.1, before.2.1) established.1 established.2.1
    established.2.2.1 established.2.2.2
  have storeSame : (step (before.1, before.2.1)).1.1 = value.1 := congrArg Prod.fst same
  rw [← storeSame]
  refine ⟨post.1, post.2.1, ?_, ?_⟩
  · rw [post.2.2.1]
    exact established.1
  · rw [post.2.2.2]
    exact established.2.1

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

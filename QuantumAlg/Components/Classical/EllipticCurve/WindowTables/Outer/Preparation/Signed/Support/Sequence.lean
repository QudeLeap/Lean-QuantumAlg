/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Support
import all QuantumAlg.Core.Execution.Circuit.Support.Sequence

/-!
# Signed preparation after actual initialization

The arbitrary first circuit establishes the two represented points and the
initial zero words. The existing signed preparation theorem then establishes
the exact returned-Store postcondition. Sequential history reassociation is
proved before specializing either circuit to a concrete allocation program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

open QuantumAlg.Execution QuantumAlg.ClassicalAlgorithms.EllipticCurve
noncomputable section
local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Circuit.execute Circuit.pathFintype prepare Store.read

variable {model : ExecutionModel} [BitWord.Selected model]
    {start ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual initialization and signed preparation jointly establish the retained postcondition. -/
lemma prepare_after_post_on_support (initialization : Circuit model start ctx)
    (frame : Frame ctx width) (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width)) (environment : model.Environment)
    (first second : QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.AffinePoint curve.curve)
    (order : Nat) (prime : order.Prime) (large : 3 < order)
    (firstOrder : addOrderOf first.toMathlib = order)
    (secondOrder : addOrderOf second.toMathlib = order)
    (widthPositive : 0 < width)
    (baseFree : InputFree frame base) (targetFree : InputFree frame target)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State start Reference (model.HiddenState × History))
    (initial : ∀ entry,
      0 < ((initialization.execute environment Reference state).block entry).mass →
      PointRepresents curve (entry.1.read base) first.toMathlib ∧
        PointRepresents curve (entry.1.read target) second.toMathlib ∧
        (entry.1.read (.storage frame.zero.toCStorageRef)).toNat = 0 ∧
        (entry.1.read (.storage frame.one.toCStorageRef)).toNat = 0)
    (value : Store ctx × (model.HiddenState × (History ×
      (initialization.seq
        (prepare (model := model) frame curve.field curve.curve.a.val base target)).Path)))
    (positive : 0 < (((initialization.seq
      (prepare (model := model) frame curve.field curve.curve.a.val base target)).execute
        environment Reference state).block value).mass) :
    Constants frame curve value.1 ∧ pairedRows curve frame first second value.1 ∧
      PointRepresents curve (value.1.read base) first.toMathlib ∧
      PointRepresents curve (value.1.read target) second.toMathlib := by
  have prepared := prepare_post_on_support (History := History × initialization.Path)
    frame curve base target environment first second order prime large firstOrder secondOrder
    widthPositive baseFree targetFree Reference
    (initialization.execute environment Reference state) initial
  exact Circuit.supported_store_seq environment initialization
    (prepare (model := model) frame curve.field curve.curve.a.val base target) Reference state
    (fun store => Constants frame curve store ∧ pairedRows curve frame first second store ∧
      PointRepresents curve (store.read base) first.toMathlib ∧
      PointRepresents curve (store.read target) second.toMathlib) prepared value positive

end
end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation.Signed

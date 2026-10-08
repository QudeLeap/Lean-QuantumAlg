/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual constant-word loader traces and durations

Original MSB-first shifts and selected increments produce the actual loader
trace. Every actual path has exactly that trace and its native duration sum.
These generic facts are shared by all internally loaded modulus routines.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

noncomputable section

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual compiled-bit events preserve the original shift and selected increment order. -/
def loaderTrace (model : ExecutionModel) [BitWord.Selected model] (width : Nat) (bits : List Bool) :
    List (Resource.Event model) :=
  bits.flatMap fun bit => [ConstantWord.shiftEvent model width] ++
    if bit then [ConstantWord.incrementEvent model width] else []

/-- The actual bit fold emits every original shift and selected increment in order. -/
theorem constantFold_eventTrace (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (path : (ConstantWord.fold (model := model) output bits).Path) :
    (ConstantWord.fold (model := model) output bits).eventTrace path =
      loaderTrace model width bits := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
    change (ConstantWord.append (model := model) output bit).eventTrace path.1 ++
      (ConstantWord.fold (model := model) output remaining).eventTrace path.2 = _
    rw [ConstantWord.constantWord_append_eventTrace, ih]
    rfl

/-- Every actual bit-fold duration is exactly the sum of its original native events. -/
theorem constantFold_depth (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (duration : Resource.Event model → Nat)
    (path : (ConstantWord.fold (model := model) output bits).Path) :
    (ConstantWord.fold (model := model) output bits).depth duration path =
      ((loaderTrace model width bits).map duration).sum := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
    change (ConstantWord.append (model := model) output bit).depth duration path.1 +
      (ConstantWord.fold (model := model) output remaining).depth duration path.2 = _
    rw [ConstantWord.constantWord_append_depth, ih]
    cases bit <;> simp [loaderTrace, Nat.add_assoc]

end

end QuantumAlg.ClassicalRoutines.ConstantWord

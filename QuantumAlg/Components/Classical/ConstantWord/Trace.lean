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

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual compiled-bit events preserve the original shift and selected increment order. -/
def loaderTrace (kind : ProblemKind) (width : Nat) (bits : List Bool) :
    List (Resource.Event kind) :=
  bits.flatMap fun bit => [ConstantWord.shiftEvent kind width] ++
    if bit then [ConstantWord.incrementEvent kind width] else []

/-- The actual bit fold emits every original shift and selected increment in order. -/
theorem constantFold_eventTrace (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (path : (ConstantWord.fold output bits).Path) :
    (ConstantWord.fold output bits).eventTrace path = loaderTrace kind width bits := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
    change (ConstantWord.append output bit).eventTrace path.1 ++
      (ConstantWord.fold output remaining).eventTrace path.2 = _
    rw [ConstantWord.constantWord_append_eventTrace, ih]
    rfl

/-- Every actual bit-fold duration is exactly the sum of its original native events. -/
theorem constantFold_depth (output : CWriteRef ctx (.unsignedWord width))
    (bits : List Bool) (duration : Resource.Event kind → Nat)
    (path : (ConstantWord.fold output bits).Path) :
    (ConstantWord.fold output bits).depth duration path =
      ((loaderTrace kind width bits).map duration).sum := by
  induction bits with
  | nil => rfl
  | cons bit remaining ih =>
    change (ConstantWord.append output bit).depth duration path.1 +
      (ConstantWord.fold output remaining).depth duration path.2 = _
    rw [ConstantWord.constantWord_append_depth, ih]
    cases bit <;> simp [loaderTrace, Nat.add_assoc]

end QuantumAlg.ClassicalRoutines.ConstantWord

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Symbolic max-plus depth algebra

`TropicalDepth U` denotes a symbolic depth quantity by its value under every
future assignment of natural-number weights to units.  Sequential composition
uses addition and parallel composition uses maximum, so algebraic laws can be
proved before choosing a concrete gate model.  `ofDepthExpr` embeds the existing
circuit-history syntax, and `evalAt_ofDepthExpr` proves that specializing the
symbolic value agrees exactly with the fixed-model depth evaluator.
-/

section

namespace QuantumAlg

/-- A symbolic max-plus depth value over resource labels `U`, represented by its
interpretation under every natural-number unit assignment. -/
structure TropicalDepth (U : Type) where
  /-- Interpret the symbolic value under one fixed unit assignment. -/
  eval : (U → Nat) → Nat

namespace TropicalDepth

variable {U : Type}

@[ext] theorem ext {left right : TropicalDepth U}
    (h : ∀ assign, left.eval assign = right.eval assign) : left = right := by
  cases left
  cases right
  simp only [mk.injEq]
  funext assign
  exact h assign

/-- Empty depth, the identity for both sequential addition and parallel max. -/
def zero : TropicalDepth U := ⟨fun _ => 0⟩

/-- One symbolic unit occurrence. -/
def atom (unit : U) : TropicalDepth U := ⟨fun assign => assign unit⟩

/-- Sequential composition, interpreted by natural-number addition. -/
def seq (left right : TropicalDepth U) : TropicalDepth U :=
  ⟨fun assign => left.eval assign + right.eval assign⟩

/-- Parallel composition, interpreted by natural-number maximum. -/
def parallel (left right : TropicalDepth U) : TropicalDepth U :=
  ⟨fun assign => max (left.eval assign) (right.eval assign)⟩

/-- Fixed sequential repetition of a symbolic depth value. -/
def scale (count : Nat) (value : TropicalDepth U) : TropicalDepth U :=
  ⟨fun assign => count * value.eval assign⟩

/-- Specialize a symbolic depth value to one fixed gate/resource model. -/
def evalAt (assign : U → Nat) (value : TropicalDepth U) : Nat :=
  value.eval assign

theorem seq_assoc (left middle right : TropicalDepth U) :
    seq (seq left middle) right = seq left (seq middle right) := by
  apply ext
  intro assign
  exact Nat.add_assoc _ _ _

theorem seq_comm (left right : TropicalDepth U) : seq left right = seq right left := by
  apply ext
  intro assign
  exact Nat.add_comm _ _

@[simp] theorem seq_zero_left (value : TropicalDepth U) : seq zero value = value := by
  apply ext
  intro assign
  exact Nat.zero_add _

@[simp] theorem seq_zero_right (value : TropicalDepth U) : seq value zero = value := by
  apply ext
  intro assign
  exact Nat.add_zero _

theorem parallel_assoc (left middle right : TropicalDepth U) :
    parallel (parallel left middle) right = parallel left (parallel middle right) := by
  apply ext
  intro assign
  exact Nat.max_assoc _ _ _

theorem parallel_comm (left right : TropicalDepth U) :
    parallel left right = parallel right left := by
  apply ext
  intro assign
  exact Nat.max_comm _ _

@[simp] theorem parallel_idem (value : TropicalDepth U) : parallel value value = value := by
  apply ext
  intro assign
  exact Nat.max_self _

@[simp] theorem parallel_zero_left (value : TropicalDepth U) : parallel zero value = value := by
  apply ext
  intro assign
  exact Nat.max_eq_right (Nat.zero_le _)

@[simp] theorem parallel_zero_right (value : TropicalDepth U) : parallel value zero = value := by
  apply ext
  intro assign
  exact Nat.max_eq_left (Nat.zero_le _)

/-- Sequential addition distributes over a parallel maximum on the right. -/
theorem seq_parallel_distrib_left (left middle right : TropicalDepth U) :
    seq left (parallel middle right) = parallel (seq left middle) (seq left right) := by
  apply ext
  intro assign
  exact add_max _ _ _

/-- Sequential addition distributes over a parallel maximum on the left. -/
theorem seq_parallel_distrib_right (left middle right : TropicalDepth U) :
    seq (parallel left middle) right = parallel (seq left right) (seq middle right) := by
  apply ext
  intro assign
  exact max_add _ _ _

/-- Embed a circuit-history depth expression into the symbolic max-plus algebra. -/
def ofDepthExpr (expression : DepthExpr U) : TropicalDepth U :=
  ⟨fun assign => DepthExpr.depthEval assign expression⟩

@[simp] theorem ofDepthExpr_id : ofDepthExpr (DepthExpr.id : DepthExpr U) = zero := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_atom (unit : U) : ofDepthExpr (.atom unit) = atom unit := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_seq (left right : DepthExpr U) :
    ofDepthExpr (.seq left right) = seq (ofDepthExpr left) (ofDepthExpr right) := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_tensor (left right : DepthExpr U) :
    ofDepthExpr (.tensor left right) = parallel (ofDepthExpr left) (ofDepthExpr right) := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_inverse (body : DepthExpr U) :
    ofDepthExpr (.inverse body) = ofDepthExpr body := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_controlled (label : String) (body : DepthExpr U) :
    ofDepthExpr (.controlled label body) = ofDepthExpr body := by
  apply ext
  intro _
  rfl

@[simp] theorem ofDepthExpr_iterate (count : Nat) (body : DepthExpr U) :
    ofDepthExpr (.iterate count body) = scale count (ofDepthExpr body) := by
  apply ext
  intro _
  rfl

@[simp] theorem evalAt_zero (assign : U → Nat) : evalAt assign zero = 0 := rfl

@[simp] theorem evalAt_atom (assign : U → Nat) (unit : U) :
    evalAt assign (atom unit) = assign unit := rfl

@[simp] theorem evalAt_seq (assign : U → Nat) (left right : TropicalDepth U) :
    evalAt assign (seq left right) = evalAt assign left + evalAt assign right := rfl

@[simp] theorem evalAt_parallel (assign : U → Nat) (left right : TropicalDepth U) :
    evalAt assign (parallel left right) = max (evalAt assign left) (evalAt assign right) := rfl

/-- Embedding and then specializing is exactly the existing fixed-model depth
evaluation, so `evalAt` is the required homomorphism to a chosen model. -/
theorem evalAt_ofDepthExpr (assign : U → Nat) (expression : DepthExpr U) :
    evalAt assign (ofDepthExpr expression) = DepthExpr.depthEval assign expression := rfl

end TropicalDepth
end QuantumAlg

end

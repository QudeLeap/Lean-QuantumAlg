/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.State.Density

/-!
# State promises on probability-bearing density blocks

A promise specifies a pure state, a normalized mixed state, or no state
information. It is evaluated on an actual subnormalized density block by
retaining that block's probability weight. Pure targets use their density
outer products [dW19, qcnotes.tex:5381]; mixed targets have trace one
[dW19, qcnotes.tex:5394].

The predicates perform no state update. Forgetting a promise does not free
storage, and an impossible block is never assigned a normalized conditional
state by division by its probability.
-/

namespace QuantumAlg

/-- Closed state information that a specification can require on an observed register. -/
public inductive StatePromise (R : Register) where
  /-- No state information is promised about this still-live register. -/
  | dirty
  /-- The normalized target is pure, with global phase ignored by its density operator. -/
  | pure (target : NormalizedVector R)
  /-- The target is a normalized density operator. -/
  | mixed (target : DensityOperator R) (normalized : target.IsNormalized)

namespace StatePromise

noncomputable section

variable {R : Register}

/-- The actual block equals its own probability weight times the promised target. -/
public def Holds : StatePromise R → DensityOperator R → Prop
  | .dirty, _ => True
  | .pure target, state =>
      state.matrix = (state.mass : ℝ) • (DensityOperator.ofPure target).matrix
  | .mixed target _, state =>
      state.matrix = (state.mass : ℝ) • target.matrix

/-- A dirty promise imposes no state equality. -/
@[simp] lemma holds_dirty (state : DensityOperator R) :
    (StatePromise.dirty : StatePromise R).Holds state := True.intro

/-- The pure promise retains the original block probability. -/
lemma holds_pure_iff (target : NormalizedVector R) (state : DensityOperator R) :
    (StatePromise.pure target).Holds state ↔
      state.matrix = (state.mass : ℝ) • (DensityOperator.ofPure target).matrix := Iff.rfl

/-- The mixed promise retains the original block probability. -/
lemma holds_mixed_iff (target : DensityOperator R) (normalized : target.IsNormalized)
    (state : DensityOperator R) :
    (StatePromise.mixed target normalized).Holds state ↔
      state.matrix = (state.mass : ℝ) • target.matrix := Iff.rfl

/-- An impossible block satisfies every stated promise without normalization or division. -/
@[simp] lemma holds_zero (promise : StatePromise R) :
    promise.Holds (DensityOperator.zero R) := by
  cases promise <;> simp [Holds]

/-- Zero probability forces the actual density block to be zero, so every promise holds. -/
lemma holds_of_mass_eq_zero (promise : StatePromise R) (state : DensityOperator R)
    (zeroMass : state.mass = 0) : promise.Holds state := by
  rw [state.eq_zero_of_mass_eq_zero zeroMass]
  exact holds_zero promise

/-- A proved state promise can be forgotten while keeping the very same density block. -/
lemma forget_to_dirty (promise : StatePromise R) (state : DensityOperator R)
    (_holds : promise.Holds state) : (StatePromise.dirty : StatePromise R).Holds state :=
  holds_dirty state

end

end StatePromise

end QuantumAlg

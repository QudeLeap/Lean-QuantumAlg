/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module


import QuantumAlg.Init
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Simon's original promise and linear equations

The source problem has an arbitrary oracle codomain and a nonzero hidden
bit vector. Complete equations determine that vector among the nonzero
solutions [dW19, qcnotes.tex:1407, 1409-1410].
-/

namespace QuantumAlg.Simon

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u

noncomputable section

/-- The two-element field used for Simon bit strings. -/
public abbrev F₂ : Type := ZMod 2

/-- An `n`-bit vector, represented as a vector space over `𝔽₂`. -/
public abbrev BitVec (n : ℕ) : Type := Fin n → F₂

variable {n : ℕ} {α : Type u}

/-- A Simon oracle maps bit vectors to arbitrary classical values. The promise,
not the codomain representation, carries the algorithmic content. -/
public abbrev Oracle (n : ℕ) (α : Type u) : Type u := BitVec n → α

/-- Dot product over `𝔽₂`. -/
def dot (x y : BitVec n) : F₂ :=
  ∑ i, x i * y i

/-- Two bit vectors are orthogonal when their `𝔽₂` dot product vanishes. -/
def Orthogonal (x y : BitVec n) : Prop := dot x y = 0

/-- The two-element fiber relation induced by a Simon mask: `x` and `y` are
equal modulo the hidden period `s`. -/
public def SameFiber (s x y : BitVec n) : Prop := y = x ∨ y = x + s

/-- The explicit Simon promise: `s` is nonzero, and oracle fibers are exactly
pairs of equal inputs or inputs separated by `s`. -/
public structure Promise (f : Oracle n α) (s : BitVec n) : Prop where
  nonzero : s ≠ 0
  fiber_iff : ∀ x y, f x = f y ↔ SameFiber s x y

/-- A sampled Simon equation says that the sampled vector is orthogonal to a
candidate mask. -/
def SatisfiesEquation (y t : BitVec n) : Prop := Orthogonal y t

/-- A candidate mask satisfies every collected linear equation. -/
def SatisfiesEquations (samples : Finset (BitVec n)) (t : BitVec n) : Prop :=
  ∀ y ∈ samples, SatisfiesEquation y t

/-- The collected equations are complete when their common solution set is
exactly `{0, s}`. This is the linear-algebraic post-processing condition
implemented by Gaussian elimination over `𝔽₂`. -/
def CompleteEquations (samples : Finset (BitVec n)) (s : BitVec n) : Prop :=
  ∀ t, SatisfiesEquations samples t ↔ t = 0 ∨ t = s

/-- A nonzero candidate returned by the classical post-processing step. -/
def Candidate (samples : Finset (BitVec n)) (t : BitVec n) : Prop :=
  t ≠ 0 ∧ SatisfiesEquations samples t

@[simp]
lemma dot_zero_left (x : BitVec n) : dot (0 : BitVec n) x = 0 := by
  simp [dot]

@[simp]
lemma dot_zero_right (x : BitVec n) : dot x (0 : BitVec n) = 0 := by
  simp [dot]

/-- The `𝔽₂` dot product is symmetric. -/
lemma dot_comm (x y : BitVec n) : dot x y = dot y x := by
  unfold dot
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mul_comm]

/-- Right additivity of the `𝔽₂` dot product. -/
lemma dot_add_right (x y z : BitVec n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

/-- Left additivity of the `𝔽₂` dot product. -/
lemma dot_add_left (x y z : BitVec n) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

/-- The zero vector satisfies every collected Simon equation. -/
lemma satisfiesEquations_zero (samples : Finset (BitVec n)) :
    SatisfiesEquations samples (0 : BitVec n) := by
  intro y _
  simp [SatisfiesEquation, Orthogonal]

/-- Sums of solutions to the collected equations are again solutions; the
solution set is a linear subspace over `𝔽₂`. -/
lemma satisfiesEquations_add {samples : Finset (BitVec n)} {a b : BitVec n}
    (ha : SatisfiesEquations samples a) (hb : SatisfiesEquations samples b) :
    SatisfiesEquations samples (a + b) := by
  intro y hy
  rw [SatisfiesEquation, Orthogonal, dot_add_right, ha y hy, hb y hy]
  simp

/-- If the equations are complete, the unknown nonzero string itself satisfies all of
them. -/
lemma hiddenMask_satisfiesEquations {samples : Finset (BitVec n)}
    {s : BitVec n} (hcomplete : CompleteEquations samples s) :
    SatisfiesEquations samples s := by
  exact (hcomplete s).2 (Or.inr rfl)

/-- Complete Simon equations identify the unknown nonzero string among nonzero
candidates. -/
lemma recover_from_complete_equations {samples : Finset (BitVec n)}
    {s t : BitVec n} (hcomplete : CompleteEquations samples s)
    (hcandidate : Candidate samples t) :
    t = s := by
  rcases hcandidate with ⟨ht_ne_zero, ht_eqs⟩
  rcases (hcomplete t).1 ht_eqs with ht_zero | ht_s
  · exact False.elim (ht_ne_zero ht_zero)
  · exact ht_s

/-- The Simon promise determines a unique nonzero mask for an oracle. -/
lemma promise_mask_unique {f : Oracle n α} {s t : BitVec n}
    (hs : Promise f s) (ht : Promise f t) :
    s = t := by
  have hf0t : f 0 = f t := by
    exact (ht.fiber_iff 0 t).2 (Or.inr (by simp))
  rcases (hs.fiber_iff 0 t).1 hf0t with ht_zero | ht_s
  · exact False.elim (ht.nonzero ht_zero)
  · simpa using ht_s.symm

end


end QuantumAlg.Simon

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Formal circuit-history expressions with cost and depth evaluators

`DepthExpr U` is a syntactic construction tree for a circuit whose atoms carry a
symbolic *resource unit* drawn from a label type `U` (units are symbolic labels,
never matrices).  It mirrors the shape of a circuit construction history:
identity, a unit-labelled atom, sequential and parallel (tensor) composition,
inverse, a controlled block, a fixed repetition (`iterate`), and an indexed
finite product of blocks.

The indexed product keeps its step blocks as a genuine index family
`step : Fin count → DepthExpr U` rather than as a list.  With this shape each
`step j` is a structural subterm, so both evaluators below are accepted by
Lean's structural recursion with no auxiliary termination measure, every
defining equation holds by `rfl` (hence the constructor `simp` lemmas and closed
`decide`/`rfl` computations), and the default `induction` principle exposes the
per-index hypothesis `∀ j, motive (step j)` directly.

Two evaluators interpret the *same* tree, differing only in how parallel
composition combines its branches:

* `costEval` is **linear**: it aggregates a per-unit weight `assign : U → M`
  into any additive commutative monoid `M`.  Sequential and parallel
  composition both add, `iterate n` scales by `n`, an indexed product sums its
  start block and all of its step blocks, and `inverse`/`controlled` pass their
  body through unchanged.  This is the total-work reading.
* `depthEval` is **max-plus** over `ℕ`: sequential composition adds, but
  parallel composition takes the `max`; `iterate n` multiplies by `n`; an
  indexed product — a sequential composition of its steps — adds; `inverse` and
  `controlled` pass through.  This is the critical-path reading.

The pass-through readings of `inverse` and `controlled` are the neutral
baseline; a genuine control-cost transform is a separate refinement.

`queryDepthEval focus` reads the **query depth** relative to a distinguished unit
`focus`: it is `depthEval` under the indicator weight sending `focus` to `1` and
every other unit to `0`, so it counts the longest sequential chain of focus-unit
occurrences and discounts everything else.
-/

section

namespace QuantumAlg

open scoped BigOperators

/-- Syntactic construction tree whose atoms carry a symbolic resource unit of
type `U`.  It mirrors a circuit construction history: identity, a unit-labelled
atom, sequential/parallel composition, inverse, a controlled block, a fixed
repetition, and an indexed finite product with a `Fin count`-indexed step
family. -/
public inductive DepthExpr (U : Type) where
  /-- The empty (identity) circuit; contributes no resources. -/
  | id
  /-- A primitive operation labelled by the resource unit `unit`. -/
  | atom (unit : U)
  /-- Sequential composition: `left` followed by `right`. -/
  | seq (left right : DepthExpr U)
  /-- Parallel/tensor composition of `left` and `right`. -/
  | tensor (left right : DepthExpr U)
  /-- The inverse of `body`. -/
  | inverse (body : DepthExpr U)
  /-- `body` conditioned on a control register labelled `controlLabel`. -/
  | controlled (controlLabel : String) (body : DepthExpr U)
  /-- `count`-fold repetition of `body`. -/
  | iterate (count : Nat) (body : DepthExpr U)
  /-- Indexed finite product: `start` followed by the blocks
  `step 0, …, step (count - 1)` composed in sequence, tagged by `label`. -/
  | indexedProduct (label : String) (count : Nat) (start : DepthExpr U)
      (step : Fin count → DepthExpr U)

namespace DepthExpr

variable {U : Type} {M : Type} [AddCommMonoid M]

/-- Linear total-work cost of a depth expression under the per-unit weight
`assign` valued in an additive commutative monoid.  Every composition adds;
`iterate n` scales by `n`; an indexed product sums its start and step blocks;
`inverse`/`controlled` pass through. -/
public def costEval (assign : U → M) : DepthExpr U → M
  | .id => 0
  | .atom u => assign u
  | .seq l r => costEval assign l + costEval assign r
  | .tensor l r => costEval assign l + costEval assign r
  | .inverse b => costEval assign b
  | .controlled _ b => costEval assign b
  | .iterate c b => c • costEval assign b
  | .indexedProduct _ _ start step =>
      costEval assign start + ∑ j, costEval assign (step j)

/-- Max-plus critical-path depth of a depth expression under the per-unit weight
`assign`.  Sequential composition adds and parallel composition takes the `max`;
`iterate n` multiplies by `n`; an indexed product (a sequential composition of
its steps) adds; `inverse`/`controlled` pass through. -/
public def depthEval (assign : U → ℕ) : DepthExpr U → ℕ
  | .id => 0
  | .atom u => assign u
  | .seq l r => depthEval assign l + depthEval assign r
  | .tensor l r => max (depthEval assign l) (depthEval assign r)
  | .inverse b => depthEval assign b
  | .controlled _ b => depthEval assign b
  | .iterate c b => c * depthEval assign b
  | .indexedProduct _ _ start step =>
      depthEval assign start + ∑ j, depthEval assign (step j)

@[simp] theorem costEval_id (assign : U → M) : costEval assign .id = 0 := rfl

@[simp] theorem costEval_atom (assign : U → M) (u : U) :
    costEval assign (.atom u) = assign u := rfl

@[simp] theorem costEval_seq (assign : U → M) (l r : DepthExpr U) :
    costEval assign (.seq l r) = costEval assign l + costEval assign r := rfl

@[simp] theorem costEval_tensor (assign : U → M) (l r : DepthExpr U) :
    costEval assign (.tensor l r) = costEval assign l + costEval assign r := rfl

@[simp] theorem costEval_inverse (assign : U → M) (b : DepthExpr U) :
    costEval assign (.inverse b) = costEval assign b := rfl

@[simp] theorem costEval_controlled (assign : U → M) (controlLabel : String)
    (b : DepthExpr U) :
    costEval assign (.controlled controlLabel b) = costEval assign b := rfl

@[simp] theorem costEval_iterate (assign : U → M) (count : Nat) (b : DepthExpr U) :
    costEval assign (.iterate count b) = count • costEval assign b := rfl

@[simp] theorem costEval_indexedProduct (assign : U → M) (label : String)
    (count : Nat) (start : DepthExpr U) (step : Fin count → DepthExpr U) :
    costEval assign (.indexedProduct label count start step) =
      costEval assign start + ∑ j, costEval assign (step j) := rfl

@[simp] theorem depthEval_id (assign : U → ℕ) : depthEval assign .id = 0 := rfl

@[simp] theorem depthEval_atom (assign : U → ℕ) (u : U) :
    depthEval assign (.atom u) = assign u := rfl

@[simp] theorem depthEval_seq (assign : U → ℕ) (l r : DepthExpr U) :
    depthEval assign (.seq l r) = depthEval assign l + depthEval assign r := rfl

@[simp] theorem depthEval_tensor (assign : U → ℕ) (l r : DepthExpr U) :
    depthEval assign (.tensor l r) = max (depthEval assign l) (depthEval assign r) := rfl

@[simp] theorem depthEval_inverse (assign : U → ℕ) (b : DepthExpr U) :
    depthEval assign (.inverse b) = depthEval assign b := rfl

@[simp] theorem depthEval_controlled (assign : U → ℕ) (controlLabel : String)
    (b : DepthExpr U) :
    depthEval assign (.controlled controlLabel b) = depthEval assign b := rfl

@[simp] theorem depthEval_iterate (assign : U → ℕ) (count : Nat) (b : DepthExpr U) :
    depthEval assign (.iterate count b) = count * depthEval assign b := rfl

@[simp] theorem depthEval_indexedProduct (assign : U → ℕ) (label : String)
    (count : Nat) (start : DepthExpr U) (step : Fin count → DepthExpr U) :
    depthEval assign (.indexedProduct label count start step) =
      depthEval assign start + ∑ j, depthEval assign (step j) := rfl

/-- Max-plus depth is monotone in every atomic-unit assignment. -/
theorem depthEval_mono {assign₁ assign₂ : U → ℕ}
    (assignmentLe : ∀ unit, assign₁ unit ≤ assign₂ unit)
    (expression : DepthExpr U) :
    depthEval assign₁ expression ≤ depthEval assign₂ expression := by
  induction expression with
  | id => simp
  | atom unit => exact assignmentLe unit
  | seq left right leftLe rightLe =>
      simpa only [depthEval_seq] using Nat.add_le_add leftLe rightLe
  | tensor left right leftLe rightLe =>
      simpa only [depthEval_tensor] using max_le_max leftLe rightLe
  | inverse body bodyLe =>
      simpa only [depthEval_inverse] using bodyLe
  | controlled _ body bodyLe =>
      simpa only [depthEval_controlled] using bodyLe
  | iterate count body bodyLe =>
      simpa only [depthEval_iterate] using Nat.mul_le_mul_left count bodyLe
  | indexedProduct _ _ start step startLe stepLe =>
      simp only [depthEval_indexedProduct]
      exact Nat.add_le_add startLe (Finset.sum_le_sum fun index _ => stepLe index)

/-- The query-depth indicator weight for a distinguished unit: the focus unit has
weight `1` and every other unit weight `0`. -/
def indicator [DecidableEq U] (focus : U) : U → ℕ :=
  fun u => if u = focus then 1 else 0

@[simp] theorem indicator_self [DecidableEq U] (focus : U) :
    indicator focus focus = 1 := by
  simp [indicator]

theorem indicator_of_ne [DecidableEq U] {u focus : U} (h : u ≠ focus) :
    indicator focus u = 0 := by
  simp [indicator, h]

/-- Query depth relative to a distinguished unit `focus`: the max-plus depth under
the indicator weight, i.e. the longest sequential chain of focus-unit atoms with
all other units discounted. -/
def queryDepthEval [DecidableEq U] (focus : U) (e : DepthExpr U) : ℕ :=
  depthEval (indicator focus) e

@[simp] theorem queryDepthEval_atom_self [DecidableEq U] (focus : U) :
    queryDepthEval focus (.atom focus) = 1 := by
  simp [queryDepthEval]

theorem queryDepthEval_atom_of_ne [DecidableEq U] {u focus : U} (h : u ≠ focus) :
    queryDepthEval focus (.atom u) = 0 := by
  simp [queryDepthEval, indicator, h]

/-- The max-plus depth never exceeds the linear cost under the same weight:
parallel composition can only shorten the critical path relative to the total
work. -/
theorem depthEval_le_costEval (assign : U → ℕ) (e : DepthExpr U) :
    depthEval assign e ≤ costEval assign e := by
  induction e with
  | id => simp
  | atom u => simp
  | seq l r ihl ihr =>
      simp only [depthEval_seq, costEval_seq]
      exact Nat.add_le_add ihl ihr
  | tensor l r ihl ihr =>
      simp only [depthEval_tensor, costEval_tensor]
      exact max_le (ihl.trans (Nat.le_add_right _ _)) (ihr.trans (Nat.le_add_left _ _))
  | inverse b ih =>
      simpa only [depthEval_inverse, costEval_inverse] using ih
  | controlled _ b ih =>
      simpa only [depthEval_controlled, costEval_controlled] using ih
  | iterate count b ih =>
      simp only [depthEval_iterate, costEval_iterate, smul_eq_mul]
      exact Nat.mul_le_mul_left count ih
  | indexedProduct _ _ start step ihs ihf =>
      simp only [depthEval_indexedProduct, costEval_indexedProduct]
      exact Nat.add_le_add ihs (Finset.sum_le_sum fun j _ => ihf j)

/-- A two-layer circuit of parallel pairs.  Two `H`/`H` tensor layers composed in
sequence have linear cost `4` (every atom counts) but max-plus depth `2` (each
parallel branch shares a layer), so the critical path is strictly shorter than
the total work. -/
example :
    costEval (fun _ : String => (1 : ℕ))
      (.seq (.tensor (.atom "H") (.atom "H")) (.tensor (.atom "H") (.atom "H"))) = 4 := by
  decide

example :
    depthEval (fun _ : String => 1)
      (.seq (.tensor (.atom "H") (.atom "H")) (.tensor (.atom "H") (.atom "H"))) = 2 := by
  decide

/-- Query-depth projection reads the number of sequential focus-unit occurrences.
With unit `0` the queried unit and unit `1` any other, running one hundred
sequential queries in parallel with a seven-fold non-queried repetition has query
depth `100`: the parallel branch is discounted by the `max`. -/
example : queryDepthEval (0 : ℕ)
    (.tensor (.iterate 100 (.atom 0)) (.iterate 7 (.atom 1))) = 100 := by
  decide

/-- A worked indexed-product cost: a start identity followed by three unit-`0`
atoms, each of weight `1`, has linear cost `3`. -/
example : costEval (fun _ : ℕ => (1 : ℕ))
    (.indexedProduct "product" 3 .id (fun _ => .atom 0)) = 3 := by
  simp

end DepthExpr

end QuantumAlg

end

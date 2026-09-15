/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.Kind
public import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.UnionInter

/-!
# Strict event resource pools

`ResourcePool kind` is a finite multiset over execution-event coordinates.
Run-derived pools record occurrences, while problem-owned pools state bounds
over the same coordinates.  Equality, addition, repetition, and order are
literal coordinate operations on identical event labels.  This module contains
no live-capacity axis and performs no compilation, expansion, pooling, or model
conversion; the type alone is not execution-provenance evidence.
-/

section

namespace QuantumAlg

/-- A finite event ledger whose coordinates are pruned by problem kind. -/
public abbrev ResourcePool (kind : ProblemKind) := Multiset (Resource.Event kind)

namespace ResourcePool

/-- A pool containing `multiplicity` copies of one event coordinate. -/
def singleton {kind : ProblemKind} (event : Resource.Event kind)
    (multiplicity : Nat := 1) : ResourcePool kind :=
  Multiset.replicate multiplicity event

/-- The exact multiplicity of one event coordinate. -/
public def count {kind : ProblemKind} (event : Resource.Event kind)
    (pool : ResourcePool kind) : Nat :=
  Multiset.count event pool

/-- Repeat every event in a pool `multiplicity` times. -/
def scale {kind : ProblemKind} (multiplicity : Nat)
    (pool : ResourcePool kind) : ResourcePool kind :=
  multiplicity • pool

/-- Convert an actual event list into its literal multiplicity ledger. -/
def ofList {kind : ProblemKind}
    (events : List (Resource.Event kind)) : ResourcePool kind :=
  events

/-- Build a literal ledger from native event multiplicities.

Repeated coordinates add their multiplicities, a zero multiplicity is inert,
and list order has no semantic effect. -/
def ofCounts {kind : ProblemKind} :
    List (Resource.Event kind × Nat) → ResourcePool kind
  | [] => 0
  | entry :: entries =>
      singleton entry.1 entry.2 + ofCounts entries

/-- Coordinatewise maximum of two event ledgers.

Multiset union retains the larger multiplicity of each identical event rather
than adding alternative paths together. -/
def max {kind : ProblemKind}
    (left right : ResourcePool kind) : ResourcePool kind :=
  left ∪ right

/-- Embed every classical coordinate structurally into a quantum pool. -/
def liftClassical (pool : ResourcePool .classical) : ResourcePool .quantum :=
  pool.map Resource.Event.liftClassical

@[simp] theorem count_zero {kind : ProblemKind} (event : Resource.Event kind) :
    count event (0 : ResourcePool kind) = 0 := by
  simp [count]

/-- A zero-multiplicity native event contributes no ledger entry. -/
@[simp] theorem singleton_zero {kind : ProblemKind} (event : Resource.Event kind) :
    singleton event 0 = 0 := rfl

/-- Count one native coordinate in an arbitrary singleton ledger. -/
@[simp] theorem count_singleton {kind : ProblemKind}
    (target event : Resource.Event kind) (multiplicity : Nat) :
    count target (singleton event multiplicity) =
      if event = target then multiplicity else 0 := by
  simp [count, singleton, Multiset.count_replicate]

theorem count_singleton_self {kind : ProblemKind}
    (event : Resource.Event kind) (multiplicity : Nat) :
    count event (singleton event multiplicity) = multiplicity := by
  simp

theorem count_singleton_of_ne {kind : ProblemKind}
    {left right : Resource.Event kind} (hne : left ≠ right)
    (multiplicity : Nat) :
    count left (singleton right multiplicity) = 0 := by
  rw [count, singleton, Multiset.count_replicate, if_neg (Ne.symm hne)]

@[simp] theorem count_add {kind : ProblemKind} (event : Resource.Event kind)
    (left right : ResourcePool kind) :
    count event (left + right) = count event left + count event right := by
  simp [count]

@[simp] theorem count_scale {kind : ProblemKind} (event : Resource.Event kind)
    (multiplicity : Nat) (pool : ResourcePool kind) :
    count event (scale multiplicity pool) = multiplicity * count event pool := by
  simp [count, scale]

@[simp] theorem count_nsmul {kind : ProblemKind} (event : Resource.Event kind)
    (multiplicity : Nat) (pool : ResourcePool kind) :
    count event (multiplicity • pool) = multiplicity * count event pool := by
  simpa only [scale] using count_scale event multiplicity pool

@[simp] theorem count_ofList {kind : ProblemKind} (event : Resource.Event kind)
    (events : List (Resource.Event kind)) :
    count event (ofList events) = List.count event events := by
  change Multiset.count event (Multiset.ofList events) = List.count event events
  exact Multiset.coe_count event events

@[simp] theorem ofList_nil {kind : ProblemKind} :
    ofList ([] : List (Resource.Event kind)) = 0 :=
  rfl

@[simp] theorem ofList_cons {kind : ProblemKind} (event : Resource.Event kind)
    (events : List (Resource.Event kind)) :
    ofList (event :: events) = singleton event + ofList events := by
  simp [ofList, singleton]

@[simp] theorem ofList_append {kind : ProblemKind}
    (first second : List (Resource.Event kind)) :
    ofList (first ++ second) = ofList first + ofList second := by
  simp [ofList]

@[simp] theorem ofCounts_nil {kind : ProblemKind} :
    ofCounts ([] : List (Resource.Event kind × Nat)) = 0 := rfl

@[simp] theorem ofCounts_cons {kind : ProblemKind} (entry : Resource.Event kind × Nat)
    (entries : List (Resource.Event kind × Nat)) :
    ofCounts (entry :: entries) =
      singleton entry.1 entry.2 + ofCounts entries := rfl

theorem count_ofCounts_nil {kind : ProblemKind}
    (event : Resource.Event kind) :
    count event (ofCounts ([] : List (Resource.Event kind × Nat))) = 0 := by
  simp

theorem count_ofCounts_cons {kind : ProblemKind}
    (target : Resource.Event kind) (entry : Resource.Event kind × Nat)
    (entries : List (Resource.Event kind × Nat)) :
    count target (ofCounts (entry :: entries)) =
      (if entry.1 = target then entry.2 else 0) +
        count target (ofCounts entries) := by
  simp

/-- A literal entry with zero multiplicity contributes no event coordinate. -/
theorem ofCounts_cons_zero {kind : ProblemKind}
    (event : Resource.Event kind) (entries : List (Resource.Event kind × Nat)) :
    ofCounts ((event, 0) :: entries) = ofCounts entries := by
  simp

/-- Adjacent repeated coordinates combine by adding their multiplicities. -/
theorem ofCounts_merge_same {kind : ProblemKind} (event : Resource.Event kind)
    (first second : Nat) (entries : List (Resource.Event kind × Nat)) :
    ofCounts ((event, first) :: (event, second) :: entries) =
      ofCounts ((event, first + second) :: entries) := by
  change
    Multiset.replicate first event +
        (Multiset.replicate second event + ofCounts entries) =
      Multiset.replicate (first + second) event + ofCounts entries
  rw [← add_assoc, ← Multiset.replicate_add]

/-- Permuting literal entries does not change their resource ledger. -/
theorem ofCounts_perm {kind : ProblemKind}
    {left right : List (Resource.Event kind × Nat)}
    (permutation : List.Perm left right) :
    ofCounts left = ofCounts right := by
  induction permutation with
  | nil => rfl
  | cons entry _ ih =>
      simp only [ofCounts_cons, ih]
  | swap first second entries =>
      simp only [ofCounts_cons]
      ac_rfl
  | trans _ _ ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

@[simp] theorem count_max {kind : ProblemKind} (event : Resource.Event kind)
    (left right : ResourcePool kind) :
    count event (max left right) = Nat.max (count event left) (count event right) := by
  simp [count, max]

@[simp] theorem scale_zero {kind : ProblemKind} (pool : ResourcePool kind) :
    scale 0 pool = 0 := by
  simp [scale]

@[simp] theorem scale_succ {kind : ProblemKind} (count : Nat)
    (pool : ResourcePool kind) :
    scale (count + 1) pool = pool + scale count pool := by
  unfold scale
  rw [succ_nsmul, add_comm]

/-- A repeated event list is the corresponding scaled singleton pool. -/
theorem ofList_replicate {kind : ProblemKind} (count : Nat)
    (event : Resource.Event kind) :
    ofList (List.replicate count event) = scale count (singleton event) := by
  induction count with
  | zero => rw [List.replicate_zero, ofList_nil, scale_zero]
  | succ count countIH =>
      rw [List.replicate_succ, ofList_cons, countIH, scale_succ]

/-- Pool order is exactly natural-number order at every identical coordinate. -/
theorem le_iff_count {kind : ProblemKind} {left right : ResourcePool kind} :
    left ≤ right ↔ ∀ event, count event left ≤ count event right := by
  simpa [count] using (Multiset.le_iff_count (s := left) (t := right))

/-- Adding coordinatewise bounds preserves the bound. -/
theorem add_mono {kind : ProblemKind}
    {left₁ right₁ left₂ right₂ : ResourcePool kind}
    (first : left₁ ≤ right₁) (second : left₂ ≤ right₂) :
    left₁ + left₂ ≤ right₁ + right₂ :=
  add_le_add first second

/-- Either event ledger is bounded by their coordinatewise maximum. -/
theorem le_max_left {kind : ProblemKind}
    (left right : ResourcePool kind) : left ≤ max left right := by
  rw [le_iff_count]
  intro event
  simp

/-- Either event ledger is bounded by their coordinatewise maximum. -/
theorem le_max_right {kind : ProblemKind}
    (left right : ResourcePool kind) : right ≤ max left right := by
  rw [le_iff_count]
  intro event
  simp

/-- Coordinatewise maximum is the least common event-ledger upper bound. -/
theorem max_le {kind : ProblemKind} {left right upper : ResourcePool kind}
    (leftBound : left ≤ upper) (rightBound : right ≤ upper) :
    max left right ≤ upper := by
  rw [le_iff_count]
  intro event
  rw [count_max]
  exact Nat.max_le.mpr
    ⟨(le_iff_count.mp leftBound) event, (le_iff_count.mp rightBound) event⟩

/-- A strict excess at one literal coordinate refutes a pool bound. -/
theorem not_le_of_count_gt {kind : ProblemKind}
    {left right : ResourcePool kind} (event : Resource.Event kind)
    (excess : count event right < count event left) : ¬left ≤ right := by
  intro bound
  exact (Nat.not_le_of_lt excess) ((le_iff_count.mp bound) event)

@[simp] theorem liftClassical_zero :
    liftClassical (0 : ResourcePool .classical) = 0 :=
  rfl

@[simp] theorem liftClassical_add
    (left right : ResourcePool .classical) :
    liftClassical (left + right) = liftClassical left + liftClassical right := by
  simp [liftClassical]

@[simp] theorem liftClassical_scale (multiplicity : Nat)
    (pool : ResourcePool .classical) :
    liftClassical (scale multiplicity pool) =
      scale multiplicity (liftClassical pool) := by
  simpa [liftClassical, scale] using
    Multiset.map_nsmul Resource.Event.liftClassical multiplicity pool

@[simp] theorem liftClassical_singleton (event : Resource.Event .classical)
    (multiplicity : Nat) :
    liftClassical (singleton event multiplicity) =
      singleton (Resource.Event.liftClassical event) multiplicity := by
  simp [liftClassical, singleton]

/-- Structural lifting preserves each classical multiplicity exactly. -/
@[simp] theorem count_liftClassical (event : Resource.Event .classical)
    (pool : ResourcePool .classical) :
    count (Resource.Event.liftClassical event) (liftClassical pool) =
      count event pool := by
  unfold count
  rw [liftClassical, Multiset.count_map]
  simpa [Resource.Event.liftClassical_injective.eq_iff] using
    (Multiset.count_eq_card_filter_eq pool event).symm

/-- No two classical pools are identified by structural lifting. -/
theorem liftClassical_injective : Function.Injective liftClassical :=
  Multiset.map_injective Resource.Event.liftClassical_injective

/-- Structural lifting is an order embedding, not a coordinate conversion. -/
@[simp] theorem liftClassical_le_liftClassical_iff
    {left right : ResourcePool .classical} :
    liftClassical left ≤ liftClassical right ↔ left ≤ right := by
  exact Multiset.map_le_map_iff Resource.Event.liftClassical_injective

@[simp] theorem count_gate_liftClassical (label : Resource.GateLabel)
    (pool : ResourcePool .classical) :
    count (.gate label) (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> cases equality

@[simp] theorem count_preparation_liftClassical
    (label : Resource.PreparationLabel) (pool : ResourcePool .classical) :
    count (.preparation label) (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> cases equality

@[simp] theorem count_measurement_liftClassical
    (label : Resource.MeasurementLabel) (pool : ResourcePool .classical) :
    count (.measurement label) (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> cases equality

@[simp] theorem count_quantumSubroutine_liftClassical
    (label : Resource.QuantumSubroutineLabel)
    (pool : ResourcePool .classical) :
    count (.quantumSubroutine label) (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> cases equality

namespace StrictOrderFixtures

private def cnot : Resource.Event .quantum :=
  .gate { family := "builtin", name := "cnot" }

private def modularMultiplication : Resource.Event .quantum :=
  .classicalOperation (.residue .mul 2048)

private def opaqueModularMultiplication : Resource.Event .quantum :=
  .quantumSubroutine
    { base :=
        { family := "arithmetic", name := "modular-multiplication",
          parameters := [2048] } }

private def opaqueModularSquare : Resource.Event .quantum :=
  .quantumSubroutine
    { base :=
        { family := "arithmetic", name := "modular-square",
          parameters := [2048] } }

private theorem not_singleton_le_singleton_of_ne
    {left right : Resource.Event .quantum} (different : left ≠ right)
    {leftMultiplicity rightMultiplicity : Nat}
    (positive : 0 < leftMultiplicity) :
    ¬singleton left leftMultiplicity ≤ singleton right rightMultiplicity := by
  intro bound
  have coefficientBound := (le_iff_count.mp bound) left
  rw [count_singleton_self,
    count_singleton_of_ne different rightMultiplicity] at coefficientBound
  exact (Nat.not_le_of_lt positive) coefficientBound

/-- Heterogeneous coordinates do not pay for one another. -/
example : ¬singleton cnot 3000 ≤ singleton modularMultiplication := by
  exact not_singleton_le_singleton_of_ne (by decide) (by decide)

/-- Heterogeneous comparison is incomparable in the other direction too. -/
example : ¬singleton modularMultiplication ≤ singleton cnot 3000 := by
  exact not_singleton_le_singleton_of_ne (by decide) (by decide)

/-- Distinct opaque labels remain distinct strict coordinates. -/
example : ¬singleton opaqueModularMultiplication ≤ singleton opaqueModularSquare := by
  exact not_singleton_le_singleton_of_ne (by decide) (by decide)

/-- An opaque call does not cover its independently represented gate ledger. -/
example : ¬singleton opaqueModularMultiplication ≤ singleton cnot 3000 := by
  exact not_singleton_le_singleton_of_ne (by decide) (by decide)

/-- An expanded gate ledger does not cover an opaque call either. -/
example : ¬singleton cnot 3000 ≤ singleton opaqueModularMultiplication := by
  exact not_singleton_le_singleton_of_ne (by decide) (by decide)

/-- Addition is monotone only through literal coordinatewise bounds. -/
example (pool : ResourcePool .quantum) :
    singleton cnot + pool ≤ singleton cnot 2 + pool := by
  exact add_mono (by decide) le_rfl

end StrictOrderFixtures

end ResourcePool
end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Core.Base.Accounting.Event
public import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Multiset.UnionInter

/-!
# Strict event resource pools

`ResourcePool model` is a finite multiset over execution-event coordinates.
Run-derived pools record occurrences, while problem-owned pools state bounds
over the same coordinates.  Equality, addition, repetition, and order are
literal coordinate operations on identical event labels.  This module contains
no live-capacity axis and performs no compilation, expansion, pooling, or model
conversion; the type alone is not execution-provenance evidence.
-/

section

namespace QuantumAlg

/-- A finite event ledger whose coordinates are fixed by the selected execution model. -/
public abbrev ResourcePool (model : ExecutionModel) := Multiset (Resource.Event model)

namespace ResourcePool

/-- A pool containing `multiplicity` copies of one event coordinate. -/
@[expose]
public def singleton {model : ExecutionModel} (event : Resource.Event model)
    (multiplicity : Nat := 1) : ResourcePool model :=
  Multiset.replicate multiplicity event

/-- The exact multiplicity of one event coordinate. -/
public def count {model : ExecutionModel} (event : Resource.Event model)
    (pool : ResourcePool model) : Nat :=
  Multiset.count event pool

/-- Repeat every event in a pool `multiplicity` times. -/
@[expose] public def scale {model : ExecutionModel} (multiplicity : Nat)
    (pool : ResourcePool model) : ResourcePool model :=
  multiplicity • pool

/-- Convert an actual event list into its literal multiplicity ledger. -/
@[expose]
public def ofList {model : ExecutionModel}
    (events : List (Resource.Event model)) : ResourcePool model :=
  events

/-- Build a literal ledger from native event multiplicities.

Repeated coordinates add their multiplicities, a zero multiplicity is inert,
and list order has no semantic effect. -/
def ofCounts {model : ExecutionModel} :
    List (Resource.Event model × Nat) → ResourcePool model
  | [] => 0
  | entry :: entries =>
      singleton entry.1 entry.2 + ofCounts entries

/-- Coordinatewise maximum of two event ledgers.

Multiset union retains the larger multiplicity of each identical event rather
than adding alternative paths together. -/
def max {model : ExecutionModel}
    (left right : ResourcePool model) : ResourcePool model :=
  left ∪ right

/-- Embed every classical coordinate structurally into a quantum pool. -/
def liftClassical {model : ExecutionModel}
    (pool : ResourcePool (.classical model.classicalOperations model.classicalOracles)) :
    ResourcePool model :=
  pool.map Resource.Event.liftClassical

@[simp] lemma count_zero {model : ExecutionModel} (event : Resource.Event model) :
    count event (0 : ResourcePool model) = 0 := by
  simp [count]

/-- A zero-multiplicity native event contributes no ledger entry. -/
@[simp] lemma singleton_zero {model : ExecutionModel} (event : Resource.Event model) :
    singleton event 0 = 0 := rfl

/-- Count one native coordinate in an arbitrary singleton ledger. -/
@[simp] lemma count_singleton {model : ExecutionModel}
    (target event : Resource.Event model) (multiplicity : Nat) :
    count target (singleton event multiplicity) =
      if event = target then multiplicity else 0 := by
  simp [count, singleton, Multiset.count_replicate]

lemma count_singleton_self {model : ExecutionModel}
    (event : Resource.Event model) (multiplicity : Nat) :
    count event (singleton event multiplicity) = multiplicity := by
  simp

lemma count_singleton_of_ne {model : ExecutionModel}
    {left right : Resource.Event model} (hne : left ≠ right)
    (multiplicity : Nat) :
    count left (singleton right multiplicity) = 0 := by
  rw [count, singleton, Multiset.count_replicate, if_neg (Ne.symm hne)]

@[simp] lemma count_add {model : ExecutionModel} (event : Resource.Event model)
    (left right : ResourcePool model) :
    count event (left + right) = count event left + count event right := by
  simp [count]

/-- Counting one coordinate commutes with a finite sum of literal ledgers. -/
public lemma count_finset_sum {model : ExecutionModel} {Index : Type} [Fintype Index]
    (event : Resource.Event model) (pool : Index → ResourcePool model) :
    count event (∑ index, pool index) = ∑ index, count event (pool index) := by
  classical
  have aux : ∀ indices : Finset Index,
      count event (∑ index ∈ indices, pool index) =
        ∑ index ∈ indices, count event (pool index) := by
    intro indices
    induction indices using Finset.induction with
    | empty => simp
    | @insert index rest fresh induction =>
        simp [Finset.sum_insert, fresh, induction]
  simpa using aux Finset.univ

@[simp] lemma count_scale {model : ExecutionModel} (event : Resource.Event model)
    (multiplicity : Nat) (pool : ResourcePool model) :
    count event (scale multiplicity pool) = multiplicity * count event pool := by
  simp [count, scale]

@[simp] lemma count_nsmul {model : ExecutionModel} (event : Resource.Event model)
    (multiplicity : Nat) (pool : ResourcePool model) :
    count event (multiplicity • pool) = multiplicity * count event pool := by
  simpa only [scale] using count_scale event multiplicity pool

@[simp] public lemma count_ofList {model : ExecutionModel} (event : Resource.Event model)
    (events : List (Resource.Event model)) :
    count event (ofList events) = List.count event events := by
  change Multiset.count event (Multiset.ofList events) = List.count event events
  exact Multiset.coe_count event events

@[simp] lemma ofList_nil {model : ExecutionModel} :
    ofList ([] : List (Resource.Event model)) = 0 :=
  rfl

@[simp] lemma ofList_cons {model : ExecutionModel} (event : Resource.Event model)
    (events : List (Resource.Event model)) :
    ofList (event :: events) = singleton event + ofList events := by
  simp [ofList, singleton]

@[simp] lemma ofList_append {model : ExecutionModel}
    (first second : List (Resource.Event model)) :
    ofList (first ++ second) = ofList first + ofList second := by
  simp [ofList]

@[simp] lemma ofCounts_nil {model : ExecutionModel} :
    ofCounts ([] : List (Resource.Event model × Nat)) = 0 := rfl

@[simp] lemma ofCounts_cons {model : ExecutionModel} (entry : Resource.Event model × Nat)
    (entries : List (Resource.Event model × Nat)) :
    ofCounts (entry :: entries) =
      singleton entry.1 entry.2 + ofCounts entries := rfl

lemma count_ofCounts_nil {model : ExecutionModel}
    (event : Resource.Event model) :
    count event (ofCounts ([] : List (Resource.Event model × Nat))) = 0 := by
  simp

lemma count_ofCounts_cons {model : ExecutionModel}
    (target : Resource.Event model) (entry : Resource.Event model × Nat)
    (entries : List (Resource.Event model × Nat)) :
    count target (ofCounts (entry :: entries)) =
      (if entry.1 = target then entry.2 else 0) +
        count target (ofCounts entries) := by
  simp

/-- A literal entry with zero multiplicity contributes no event coordinate. -/
lemma ofCounts_cons_zero {model : ExecutionModel}
    (event : Resource.Event model) (entries : List (Resource.Event model × Nat)) :
    ofCounts ((event, 0) :: entries) = ofCounts entries := by
  simp

/-- Adjacent repeated coordinates combine by adding their multiplicities. -/
lemma ofCounts_merge_same {model : ExecutionModel} (event : Resource.Event model)
    (first second : Nat) (entries : List (Resource.Event model × Nat)) :
    ofCounts ((event, first) :: (event, second) :: entries) =
      ofCounts ((event, first + second) :: entries) := by
  change
    Multiset.replicate first event +
        (Multiset.replicate second event + ofCounts entries) =
      Multiset.replicate (first + second) event + ofCounts entries
  rw [← add_assoc, ← Multiset.replicate_add]

/-- Permuting literal entries does not change their resource ledger. -/
lemma ofCounts_perm {model : ExecutionModel}
    {left right : List (Resource.Event model × Nat)}
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

@[simp] lemma count_max {model : ExecutionModel} (event : Resource.Event model)
    (left right : ResourcePool model) :
    count event (max left right) = Nat.max (count event left) (count event right) := by
  simp [count, max]

@[simp] lemma scale_zero {model : ExecutionModel} (pool : ResourcePool model) :
    scale 0 pool = 0 := by
  simp [scale]

@[simp] lemma scale_succ {model : ExecutionModel} (count : Nat)
    (pool : ResourcePool model) :
    scale (count + 1) pool = pool + scale count pool := by
  unfold scale
  rw [succ_nsmul, add_comm]

/-- A repeated event list is the corresponding scaled singleton pool. -/
lemma ofList_replicate {model : ExecutionModel} (count : Nat)
    (event : Resource.Event model) :
    ofList (List.replicate count event) = scale count (singleton event) := by
  induction count with
  | zero => rw [List.replicate_zero, ofList_nil, scale_zero]
  | succ count countIH =>
      rw [List.replicate_succ, ofList_cons, countIH, scale_succ]

/-- Pool order is exactly natural-number order at every identical coordinate. -/
lemma le_iff_count {model : ExecutionModel} {left right : ResourcePool model} :
    left ≤ right ↔ ∀ event, count event left ≤ count event right := by
  simpa [count] using (Multiset.le_iff_count (s := left) (t := right))

/-- Adding coordinatewise bounds preserves the bound. -/
lemma add_mono {model : ExecutionModel}
    {left₁ right₁ left₂ right₂ : ResourcePool model}
    (first : left₁ ≤ right₁) (second : left₂ ≤ right₂) :
    left₁ + left₂ ≤ right₁ + right₂ :=
  add_le_add first second

/-- Either event ledger is bounded by their coordinatewise maximum. -/
lemma le_max_left {model : ExecutionModel}
    (left right : ResourcePool model) : left ≤ max left right := by
  rw [le_iff_count]
  intro event
  simp

/-- Either event ledger is bounded by their coordinatewise maximum. -/
lemma le_max_right {model : ExecutionModel}
    (left right : ResourcePool model) : right ≤ max left right := by
  rw [le_iff_count]
  intro event
  simp

/-- Coordinatewise maximum is the least common event-ledger upper bound. -/
lemma max_le {model : ExecutionModel} {left right upper : ResourcePool model}
    (leftBound : left ≤ upper) (rightBound : right ≤ upper) :
    max left right ≤ upper := by
  rw [le_iff_count]
  intro event
  rw [count_max]
  exact Nat.max_le.mpr
    ⟨(le_iff_count.mp leftBound) event, (le_iff_count.mp rightBound) event⟩

/-- A strict excess at one literal coordinate refutes a pool bound. -/
lemma not_le_of_count_gt {model : ExecutionModel}
    {left right : ResourcePool model} (event : Resource.Event model)
    (excess : count event right < count event left) : ¬left ≤ right := by
  intro bound
  exact (Nat.not_le_of_lt excess) ((le_iff_count.mp bound) event)

@[simp] lemma liftClassical_zero (model : ExecutionModel) :
    liftClassical (model := model)
      (0 : ResourcePool (.classical model.classicalOperations model.classicalOracles)) = 0 := rfl

@[simp] lemma liftClassical_add (model : ExecutionModel)
    (left right : ResourcePool (.classical model.classicalOperations model.classicalOracles)) :
    liftClassical (model := model) (left + right) =
      liftClassical left + liftClassical right := by
  simp [liftClassical]

@[simp] lemma liftClassical_scale (model : ExecutionModel) (multiplicity : Nat)
    (pool : ResourcePool (.classical model.classicalOperations model.classicalOracles)) :
    liftClassical (model := model) (scale multiplicity pool) =
      scale multiplicity (liftClassical pool) := by
  simpa [liftClassical, scale] using
    Multiset.map_nsmul (Resource.Event.liftClassical (model := model)) multiplicity pool

@[simp] lemma liftClassical_singleton (model : ExecutionModel)
    (event : Resource.Event (.classical model.classicalOperations model.classicalOracles))
    (multiplicity : Nat) :
    liftClassical (model := model) (singleton event multiplicity) =
      singleton (Resource.Event.liftClassical event) multiplicity := by
  simp [liftClassical, singleton]

/-- Structural lifting preserves each classical multiplicity exactly. -/
@[simp] lemma count_liftClassical (model : ExecutionModel)
    (event : Resource.Event (.classical model.classicalOperations model.classicalOracles))
    (pool : ResourcePool (.classical model.classicalOperations model.classicalOracles)) :
    count (Resource.Event.liftClassical event) (liftClassical (model := model) pool) =
      count event pool := by
  unfold count
  rw [liftClassical, Multiset.count_map]
  simpa [(Resource.Event.liftClassical_injective model).eq_iff] using
    (Multiset.count_eq_card_filter_eq pool event).symm

/-- No two classical pools are identified by structural lifting. -/
lemma liftClassical_injective (model : ExecutionModel) :
    Function.Injective (liftClassical (model := model)) :=
  Multiset.map_injective (Resource.Event.liftClassical_injective model)

/-- Structural lifting is an order embedding, not a coordinate conversion. -/
@[simp] lemma liftClassical_le_liftClassical_iff (model : ExecutionModel)
    {left right : ResourcePool (.classical model.classicalOperations model.classicalOracles)} :
    liftClassical (model := model) left ≤ liftClassical right ↔ left ≤ right := by
  exact Multiset.map_le_map_iff (Resource.Event.liftClassical_injective model)

@[simp] lemma count_gate_liftClassical (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel)
    (coordinate : gates.Coordinate) (pool : ResourcePool (.classical operations classicalOracles)) :
    count (model := .quantum gates oracles operations classicalOracles) (.gate coordinate)
      (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> first | (cases ‹Empty›) | (cases equality)

@[simp] lemma count_preparation_liftClassical (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel)
    (dimension : ℕ+) (pool : ResourcePool (.classical operations classicalOracles)) :
    count (model := .quantum gates oracles operations classicalOracles) (.preparation dimension)
      (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> first | (cases ‹Empty›) | (cases equality)

@[simp] lemma count_measurement_liftClassical (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel)
    (dimension : ℕ+) (pool : ResourcePool (.classical operations classicalOracles)) :
    count (model := .quantum gates oracles operations classicalOracles) (.measurement dimension)
      (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> first | (cases ‹Empty›) | (cases equality)

@[simp] lemma count_oracle_liftClassical (gates : GateModel) (oracles : OracleModel)
    (operations : ClassicalOpModel) (classicalOracles : ClassicalOracleModel)
    (coordinate : oracles.Coordinate)
    (pool : ResourcePool (.classical operations classicalOracles)) :
    count (model := .quantum gates oracles operations classicalOracles) (.oracle coordinate)
      (liftClassical pool) = 0 := by
  unfold count
  apply Multiset.count_eq_zero.mpr
  intro membership
  obtain ⟨event, _, equality⟩ := Multiset.mem_map.mp membership
  cases event <;> first | (cases ‹Empty›) | (cases equality)

/-- Distinct native coordinates cannot pay for one another, even with a larger count. -/
lemma not_singleton_le_singleton_of_ne {model : ExecutionModel}
    {left right : Resource.Event model} (different : left ≠ right)
    {leftMultiplicity rightMultiplicity : Nat} (positive : 0 < leftMultiplicity) :
    ¬singleton left leftMultiplicity ≤ singleton right rightMultiplicity := by
  intro bound
  have coefficientBound := (le_iff_count.mp bound) left
  rw [count_singleton_self,
    count_singleton_of_ne different rightMultiplicity] at coefficientBound
  exact (Nat.not_le_of_lt positive) coefficientBound

end ResourcePool
end QuantumAlg

end

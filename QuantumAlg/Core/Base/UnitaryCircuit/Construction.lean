/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Register
import all QuantumAlg.Core.Base.Register
import all QuantumAlg.Core.Base.UnitaryCircuit.Sequence
import Mathlib.Data.List.Nodup

/-!
# Safe typed circuit construction

This module is the sole owner of the opaque `UnitaryCircuit` representation and all
smart constructors that may use its raw constructor. A circuit stores one
duplicate-free physical layout, one typed construction sequence, and erased
proof that every sealed leaf is contained in that layout.

Sequential constructors merge overlapping footprints by stable union.
Relabeling, control, and tensor construction consume their physical-layout
certificates here, before the semantic facade exposes the resulting circuit.
Control callers provide only the finite register and activation value; strict
controlled event coordinates are derived from that register dimension.
-/

section

namespace QuantumAlg

namespace PhysicalLayout

/-- A positional relabeling from one duplicate-free physical layout to
another. The supplied function is also used to rewrite every gate placement. -/
structure Relabeling (oldLayout newLayout : List Nat) where
  /-- Physical-index map applied to the layout and every sealed leaf. -/
  toFun : Nat → Nat
  map_layout : oldLayout.map toFun = newLayout
  old_nodup : oldLayout.Nodup
  new_nodup : newLayout.Nodup

namespace Relabeling

/-- A relabeling is injective on the advertised old layout. Otherwise its
mapped layout would contradict the new layout's duplicate-freedom. -/
theorem toFun_injective_on_old {oldLayout newLayout : List Nat}
    (relabeling : Relabeling oldLayout newLayout) :
    ∀ ⦃left⦄, left ∈ oldLayout → ∀ ⦃right⦄, right ∈ oldLayout →
      relabeling.toFun left = relabeling.toFun right → left = right := by
  apply List.inj_on_of_nodup_map
  rw [relabeling.map_layout]
  exact relabeling.new_nodup

/-- Identity relabeling of a valid physical layout. -/
def identity (layout : List Nat) (hvalid : layout.Nodup) :
    Relabeling layout layout where
  toFun := id
  map_layout := by simp
  old_nodup := hvalid
  new_nodup := hvalid

/-- Compose two positional relabelings. -/
def trans {first second third : List Nat}
    (left : Relabeling first second) (right : Relabeling second third) :
    Relabeling first third where
  toFun := right.toFun ∘ left.toFun
  map_layout := by
    rw [← List.map_map]
    rw [left.map_layout, right.map_layout]
  old_nodup := left.old_nodup
  new_nodup := right.new_nodup

end Relabeling

/-- Evidence that two valid physical layouts can be merged in parallel. -/
structure DisjointMerge (left right : List Nat) where
  left_nodup : left.Nodup
  right_nodup : right.Nodup
  disjoint : List.Disjoint left right

namespace DisjointMerge

/-- Stable merged layout: left positions first, then right positions. -/
@[nolint unusedArguments]
def merged {left right : List Nat} (_layout : DisjointMerge left right) : List Nat :=
  left ++ right

@[simp]
theorem merged_eq_append {left right : List Nat}
    (layout : DisjointMerge left right) : layout.merged = left ++ right :=
  rfl

theorem merged_nodup {left right : List Nat}
    (layout : DisjointMerge left right) : layout.merged.Nodup :=
  layout.left_nodup.append layout.right_nodup layout.disjoint

end DisjointMerge

end PhysicalLayout

namespace UnitarySequence

/-- Recursively rewrite every gate atom's physical placement. -/
def rewriteSystemIdx (mapping : Nat → Nat) :
    {R : Register} → UnitarySequence R → UnitarySequence R
  | _, .id R => .id R
  | _, .leaf atom => .leaf (atom.rewriteSystemIdx mapping)
  | _, .seq left right =>
      .seq (left.rewriteSystemIdx mapping) (right.rewriteSystemIdx mapping)
  | _, .tensor left right =>
      .tensor (left.rewriteSystemIdx mapping) (right.rewriteSystemIdx mapping)
  | _, .reindex equiv body =>
      .reindex equiv (body.rewriteSystemIdx mapping)
  | _, .dagger body => .dagger (body.rewriteSystemIdx mapping)
  | _, .controlled control activationValue body =>
      .controlled control activationValue (body.rewriteSystemIdx mapping)
  | _, .iterate count body => .iterate count (body.rewriteSystemIdx mapping)
  | _, .indexedProduct label count start step =>
      .indexedProduct label count (start.rewriteSystemIdx mapping)
        (fun j => (step j).rewriteSystemIdx mapping)

@[simp]
theorem rewriteSystemIdx_leaf {R : Register} (mapping : Nat → Nat)
    (leaf : UnitaryLeaf R) :
    (UnitarySequence.leaf leaf).rewriteSystemIdx mapping =
      .leaf (leaf.rewriteSystemIdx mapping) :=
  rfl

/-- Rewriting every atom placement along the same certified layout map
preserves atom containment in the mapped physical layout. -/
theorem atomsContainedIn_rewriteSystemIdx {oldPhysicalIdx newPhysicalIdx : List Nat}
    (mapping : Nat → Nat) {R : Register} (sequence : UnitarySequence R)
    (hcontained : sequence.AtomsContainedIn oldPhysicalIdx)
    (hinjective_on_old :
      ∀ ⦃left⦄, left ∈ oldPhysicalIdx → ∀ ⦃right⦄, right ∈ oldPhysicalIdx →
        mapping left = mapping right → left = right)
    (map_layout : oldPhysicalIdx.map mapping = newPhysicalIdx) :
    (sequence.rewriteSystemIdx mapping).AtomsContainedIn newPhysicalIdx := by
  induction sequence with
  | id => trivial
  | leaf atom =>
      constructor
      · exact hcontained.1.map_on (fun left hleft right hright hequal =>
          hinjective_on_old
            (hcontained.2 hleft) (hcontained.2 hright) hequal)
      · change atom.systemIdx.map mapping ⊆ newPhysicalIdx
        rw [← map_layout]
        intro mappedIndex hmapped
        obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hmapped
        exact List.mem_map.mpr ⟨index, hcontained.2 hindex, rfl⟩
  | seq left right ihLeft ihRight =>
      exact ⟨ihLeft hcontained.1, ihRight hcontained.2⟩
  | tensor left right ihLeft ihRight =>
      exact ⟨ihLeft hcontained.1, ihRight hcontained.2⟩
  | reindex equiv body ih => exact ih hcontained
  | dagger body ih => exact ih hcontained
  | controlled control activationValue body ih => exact ih hcontained
  | iterate count body ih => exact ih hcontained
  | indexedProduct label count start step ihStart ihStep =>
      exact ⟨ihStart hcontained.1, fun j => ihStep j (hcontained.2 j)⟩

end UnitarySequence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- A typed circuit with a certified duplicate-free physical layout containing
every sealed leaf in its construction sequence. Raw construction is private to
this module; clients use the smart constructors in namespace `UnitaryCircuit`. -/
public structure UnitaryCircuit (R : Register) where
  private mk ::
  /-- Physical system indices touched by the circuit, in stable layout order. -/
  physical_idx : List Nat
  /-- The single source of matrix, resource, and depth semantics. -/
  private sequence : UnitarySequence R
  /-- The advertised physical layout contains no duplicate system indices. -/
  physical_idx_nodup : physical_idx.Nodup
  /-- Every sequence leaf is placed inside the advertised physical layout. -/
  private sequence_atoms_contained : sequence.AtomsContainedIn physical_idx

attribute [nolint defsWithUnderscore] UnitaryCircuit.physical_idx

namespace UnitaryCircuit

noncomputable section

/-- Stable union of possibly overlapping physical footprints used by
sequential composition. -/
def unionPhysicalIdx (left right : List Nat) : List Nat :=
  left.union right

/-- A stable union is duplicate-free whenever its right input is
duplicate-free. -/
theorem unionPhysicalIdx_nodup (left : List Nat) {right : List Nat}
    (hright : right.Nodup) : (unionPhysicalIdx left right).Nodup :=
  hright.union left

/-- The left input is contained in its stable physical-layout union. -/
theorem subset_unionPhysicalIdx_left (left right : List Nat) :
    left ⊆ unionPhysicalIdx left right :=
  fun _ hmem => List.mem_union_left hmem right

/-- The right input is contained in its stable physical-layout union. -/
theorem subset_unionPhysicalIdx_right (left right : List Nat) :
    right ⊆ unionPhysicalIdx left right :=
  fun _ hmem => List.mem_union_right left hmem

/-- A stable union adds no entries when its left footprint is already contained
in its right footprint. This theorem uses the same native `List.union`
instance as `unionPhysicalIdx`. -/
theorem unionPhysicalIdx_eq_right_of_subset (left right : List Nat)
    (hsubset : left ⊆ right) : unionPhysicalIdx left right = right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      change (tail.union right).insert head = right
      have hhead : head ∈ tail.union right := by
        change head ∈ unionPhysicalIdx tail right
        exact subset_unionPhysicalIdx_right tail right
          (hsubset List.mem_cons_self)
      rw [List.insert_of_mem hhead]
      change unionPhysicalIdx tail right = right
      exact ih (fun value hvalue =>
        hsubset (List.mem_cons_of_mem head hvalue))

@[simp]
theorem unionPhysicalIdx_self (layout : List Nat) :
    unionPhysicalIdx layout layout = layout :=
  unionPhysicalIdx_eq_right_of_subset layout layout (fun _ hmem => hmem)

/-- Folding stable physical-layout union preserves duplicate-freedom when the
initial layout and every added layout are duplicate-free. -/
theorem foldl_unionPhysicalIdx_nodup
    (layouts : List (List Nat)) (initial : List Nat)
    (hinitial : initial.Nodup)
    (hlayouts : ∀ layout ∈ layouts, layout.Nodup) :
    (layouts.foldl unionPhysicalIdx initial).Nodup := by
  induction layouts generalizing initial with
  | nil => exact hinitial
  | cons layout layouts ih =>
      exact ih (unionPhysicalIdx initial layout)
        (unionPhysicalIdx_nodup initial (hlayouts layout (by simp))) (by
          intro next hnext
          exact hlayouts next (by simp [hnext]))

/-- The initial physical layout is contained in any fold of stable layout
unions starting from it. -/
theorem subset_foldl_unionPhysicalIdx_initial
    (layouts : List (List Nat)) (initial : List Nat) :
    initial ⊆ layouts.foldl unionPhysicalIdx initial := by
  induction layouts generalizing initial with
  | nil => exact fun _ hmem => hmem
  | cons layout layouts ih =>
      exact fun _ hmem =>
        ih (unionPhysicalIdx initial layout)
          (subset_unionPhysicalIdx_left initial layout hmem)

/-- Every member layout is contained in the stable union fold that adds it. -/
theorem subset_foldl_unionPhysicalIdx_of_mem
    (layouts : List (List Nat)) (initial layout : List Nat)
    (hlayout : layout ∈ layouts) :
    layout ⊆ layouts.foldl unionPhysicalIdx initial := by
  induction layouts generalizing initial with
  | nil => simp at hlayout
  | cons head tail ih =>
      simp only [List.mem_cons] at hlayout
      simp only [List.foldl_cons]
      rcases hlayout with hhead | hlayout
      · subst layout
        exact fun _ hmem =>
          subset_foldl_unionPhysicalIdx_initial tail
            (unionPhysicalIdx initial head)
            (subset_unionPhysicalIdx_right initial head hmem)
      · exact ih (unionPhysicalIdx initial head) hlayout

/-- Identity circuit on an explicit duplicate-free physical footprint. -/
@[implicit_reducible]
def identity (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) : UnitaryCircuit R where
  physical_idx := physical_idx
  sequence := .id R
  physical_idx_nodup := physical_idx_nodup
  sequence_atoms_contained := trivial

/-- Lift the one sealed execution leaf into a circuit.  Matrix, strict event
projection, transitional legacy account, and both depth views all recurse over
this same leaf. -/
def ofLeaf {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) : UnitaryCircuit R where
  physical_idx := leaf.systemIdx
  sequence := .leaf leaf
  physical_idx_nodup := systemIdxNodup
  sequence_atoms_contained := ⟨systemIdxNodup, fun _ hmem => hmem⟩

/-- Lift one sealed execution leaf into a certified larger circuit footprint. -/
def ofLeafAt {R : Register} (physical_idx : List Nat) (leaf : UnitaryLeaf R)
    (physical_idx_nodup : physical_idx.Nodup)
    (leaf_systemIdx_nodup : leaf.systemIdx.Nodup)
    (leaf_systemIdx_subset : leaf.systemIdx ⊆ physical_idx) : UnitaryCircuit R where
  physical_idx := physical_idx
  sequence := .leaf leaf
  physical_idx_nodup := physical_idx_nodup
  sequence_atoms_contained :=
    ⟨leaf_systemIdx_nodup, leaf_systemIdx_subset⟩

/-- Execute `left` first and `right` second, merging their physical footprints
in stable order. -/
def seq {R : Register} (left right : UnitaryCircuit R) : UnitaryCircuit R where
  physical_idx := unionPhysicalIdx left.physical_idx right.physical_idx
  sequence := .seq left.sequence right.sequence
  physical_idx_nodup :=
    unionPhysicalIdx_nodup left.physical_idx right.physical_idx_nodup
  sequence_atoms_contained :=
    ⟨left.sequence_atoms_contained.mono
        (subset_unionPhysicalIdx_left left.physical_idx right.physical_idx),
      right.sequence_atoms_contained.mono
        (subset_unionPhysicalIdx_right left.physical_idx right.physical_idx)⟩

/-- Adjoint a circuit while preserving its physical footprint. -/
def dagger {R : Register} (body : UnitaryCircuit R) : UnitaryCircuit R where
  physical_idx := body.physical_idx
  sequence := .dagger body.sequence
  physical_idx_nodup := body.physical_idx_nodup
  sequence_atoms_contained := body.sequence_atoms_contained

instance {R : Register} : Inv (UnitaryCircuit R) := ⟨dagger⟩

/-- Symbolic fixed repetition. -/
def iterate {R : Register} (count : Nat) (body : UnitaryCircuit R) : UnitaryCircuit R where
  physical_idx := body.physical_idx
  sequence := .iterate count body.sequence
  physical_idx_nodup := body.physical_idx_nodup
  sequence_atoms_contained := body.sequence_atoms_contained

/-- Sequential product of an explicit list of circuit blocks. -/
def sequenceList {R : Register} (start : UnitaryCircuit R)
    (steps : List (UnitaryCircuit R)) : UnitaryCircuit R :=
  steps.foldl seq start

/-- Indexed finite product retaining the `Fin count` family in the stored
sequence instead of expanding it to a list. -/
def indexedProductNamed {R : Register} (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) : UnitaryCircuit R :=
  let layouts := List.ofFn (fun j => (step j).physical_idx)
  { physical_idx := layouts.foldl unionPhysicalIdx start.physical_idx
    sequence := .indexedProduct label count start.sequence (fun j => (step j).sequence)
    physical_idx_nodup :=
      foldl_unionPhysicalIdx_nodup layouts start.physical_idx
        start.physical_idx_nodup (by
          intro layout hlayout
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hlayout
          exact (step j).physical_idx_nodup)
    sequence_atoms_contained :=
      ⟨start.sequence_atoms_contained.mono
          (subset_foldl_unionPhysicalIdx_initial layouts start.physical_idx),
        fun j =>
          (step j).sequence_atoms_contained.mono
            (subset_foldl_unionPhysicalIdx_of_mem layouts start.physical_idx
              (step j).physical_idx (List.mem_ofFn.mpr ⟨j, rfl⟩))⟩ }

/-- Unlabelled convenience form of `indexedProductNamed`. -/
def indexedProduct {R : Register} (count : Nat) (start : UnitaryCircuit R)
    (step : Fin count → UnitaryCircuit R) : UnitaryCircuit R :=
  indexedProductNamed "indexed-product" count start step

/-- Indexed product over an explicit schedule. -/
def indexedProductList {R : Register} {α : Type} (label : String)
    (start : UnitaryCircuit R) (schedule : List α) (step : α → UnitaryCircuit R) :
    UnitaryCircuit R :=
  indexedProductNamed label schedule.length start (fun j => step (schedule.get j))

/-- Change a circuit's physical layout and recursively rewrite every gate
placement through the certified positional map. -/
def relabel {R : Register} (circuit : UnitaryCircuit R) {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    UnitaryCircuit R where
  physical_idx := newPhysicalIdx
  sequence := circuit.sequence.rewriteSystemIdx relabeling.toFun
  physical_idx_nodup := relabeling.new_nodup
  sequence_atoms_contained :=
    UnitarySequence.atomsContainedIn_rewriteSystemIdx relabeling.toFun
      circuit.sequence circuit.sequence_atoms_contained
      relabeling.toFun_injective_on_old relabeling.map_layout

/-- Change only the logical basis index of a circuit.  The construction tree,
physical placement, cost, and depth remain intact under the equivalence. -/
def reindex {R S : Register} (equiv : R.Index ≃ S.Index)
    (circuit : UnitaryCircuit R) : UnitaryCircuit S where
  physical_idx := circuit.physical_idx
  sequence := .reindex equiv circuit.sequence
  physical_idx_nodup := circuit.physical_idx_nodup
  sequence_atoms_contained := circuit.sequence_atoms_contained

/-- Control a circuit at an explicit finite-register activation value using a
certificate that the control layout and body layout are duplicate-free and
disjoint. Controlled gate and subroutine coordinates are derived internally;
the caller cannot provide an event label or resource pool. -/
def controlAt {R : Register} (control : Register) (controlSystemIdx : List Nat)
    (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) : UnitaryCircuit (Register.prod control R) where
  physical_idx := layout.merged
  sequence := .controlled control activationValue body.sequence
  physical_idx_nodup := layout.merged_nodup
  sequence_atoms_contained :=
    body.sequence_atoms_contained.mono (by
      intro index hindex
      exact List.mem_append_right controlSystemIdx hindex)

/-- Control a circuit at the greatest basis value of a finite control register
using a certified disjoint physical merge. Controlled event coordinates are
derived from the register dimension. Use `controlAt` for an explicit
activation value. -/
def control {R : Register} (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) : UnitaryCircuit (Register.prod control R) :=
  controlAt control controlSystemIdx body layout activationValue

/-- Checked parallel composition with a certified duplicate-free, disjoint
merged physical layout. -/
def tensor {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    UnitaryCircuit (Register.prod R S) where
  physical_idx := layout.merged
  sequence := .tensor left.sequence right.sequence
  physical_idx_nodup := layout.merged_nodup
  sequence_atoms_contained :=
    ⟨left.sequence_atoms_contained.mono (by
        intro index hindex
        exact List.mem_append_left right.physical_idx hindex),
      right.sequence_atoms_contained.mono (by
        intro index hindex
        exact List.mem_append_right left.physical_idx hindex)⟩

/-- Relabel two circuits first, then merge their new layouts in parallel. -/
def tensorRelabeled {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    UnitaryCircuit (Register.prod R S) :=
  tensor (left.relabel leftRelabeling) (right.relabel rightRelabeling) layout

end


end UnitaryCircuit

end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Register
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count

/-!
# Finite-dimensional quantum layouts

A wire has one physical identity and one positive dimension. A layout is an
ordered collection of wires with distinct identities, even when dimensions
differ. Its register basis is the dependent product of the individual wire
bases. Space counts retain the dimension of each physical system; the Hilbert
dimension does not determine a qubit count.
-/

section

namespace QuantumAlg

open scoped BigOperators

/-- One physical quantum system and its finite computational-basis dimension. -/
public structure QuantumWire where
  /-- Physical identity, independent of the system's dimension. -/
  identity : Nat
  /-- A system has a nonempty finite computational basis. -/
  dimension : ℕ+
deriving DecidableEq

/-- Two physical wire records are equal when both recorded fields agree. -/
@[ext] public theorem QuantumWire.ext {left right : QuantumWire}
    (identity : left.identity = right.identity)
    (dimension : left.dimension = right.dimension) : left = right := by
  cases left
  cases right
  simp_all

/-- Ordered finite quantum systems with an injective physical placement. -/
public structure QuantumLayout (systemCount : Nat) where
  /-- The actual physical system at each logical position. -/
  wire : Fin systemCount → QuantumWire
  /-- One physical identity cannot occupy two logical positions. -/
  identityInjective : Function.Injective (fun index => (wire index).identity)

namespace QuantumLayout

/-- Two layouts with the same ordered physical wires are equal; the
injectivity certificates are propositions and carry no additional data. -/
public theorem eq_of_wire_eq {systemCount : Nat}
    {left right : QuantumLayout systemCount}
    (same : left.wire = right.wire) : left = right := by
  cases left with
  | mk leftWire leftInjective =>
      cases right with
      | mk rightWire rightInjective =>
          change leftWire = rightWire at same
          subst rightWire
          rfl

/-- Ordered physical wire records. -/
@[expose]
public def wires {systemCount : Nat} (layout : QuantumLayout systemCount) :
    List QuantumWire :=
  List.ofFn layout.wire

/-- Ordered physical identities, used for allocation and disjointness. -/
@[expose]
public def identities {systemCount : Nat} (layout : QuantumLayout systemCount) :
    List Nat :=
  List.ofFn fun index => (layout.wire index).identity

/-- Ordered positive dimensions of the physical systems. -/
@[expose]
public def dimensions {systemCount : Nat} (layout : QuantumLayout systemCount) :
    List ℕ+ :=
  List.ofFn fun index => (layout.wire index).dimension

@[simp] public theorem wires_length {systemCount : Nat}
    (layout : QuantumLayout systemCount) : layout.wires.length = systemCount := by
  simp [wires]

@[simp] public theorem identities_length {systemCount : Nat}
    (layout : QuantumLayout systemCount) : layout.identities.length = systemCount := by
  simp [identities]

@[simp] public theorem dimensions_length {systemCount : Nat}
    (layout : QuantumLayout systemCount) : layout.dimensions.length = systemCount := by
  simp [dimensions]

public theorem identities_nodup {systemCount : Nat} (layout : QuantumLayout systemCount) :
    layout.identities.Nodup :=
  List.nodup_ofFn.mpr layout.identityInjective

/-- Equality of physical identities forces equality of logical positions,
without any assumption on their dimensions. -/
public theorem position_eq_of_identity_eq {systemCount : Nat}
    (layout : QuantumLayout systemCount) {left right : Fin systemCount}
    (sameIdentity : (layout.wire left).identity = (layout.wire right).identity) :
    left = right :=
  layout.identityInjective sameIdentity

/-- Construct the layout from exactly the supplied duplicate-free wire records. -/
@[expose]
public def ofWires (wireList : List QuantumWire)
    (distinct : (wireList.map QuantumWire.identity).Nodup) :
    QuantumLayout wireList.length where
  wire := wireList.get
  identityInjective := by
    apply List.nodup_ofFn.mp
    rw [List.ofFn_comp', List.ofFn_get]
    exact distinct

@[simp] public theorem wires_ofWires (wireList : List QuantumWire)
    (distinct : (wireList.map QuantumWire.identity).Nodup) :
    (ofWires wireList distinct).wires = wireList :=
  List.ofFn_get wireList

/-- Check identity uniqueness before constructing a finite-dimensional layout. -/
@[expose]
public def tryOfWires (wireList : List QuantumWire) : Option (QuantumLayout wireList.length) :=
  if distinct : (wireList.map QuantumWire.identity).Nodup then
    some (ofWires wireList distinct)
  else none

/-- The checked constructor rejects exactly lists with duplicate identities. -/
public theorem tryOfWires_eq_none_iff (wireList : List QuantumWire) :
    tryOfWires wireList = none ↔ ¬(wireList.map QuantumWire.identity).Nodup := by
  by_cases distinct : (wireList.map QuantumWire.identity).Nodup <;>
    simp [tryOfWires, distinct]

/-- Assigning two dimensions to one identity does not create two physical wires. -/
public theorem duplicateIdentity_rejected (identity : Nat) (leftDimension rightDimension : ℕ+) :
    tryOfWires [⟨identity, leftDimension⟩, ⟨identity, rightDimension⟩] = none := by
  simp [tryOfWires]

/-- Computational-basis labels record one finite value for every physical wire. -/
public abbrev Basis {systemCount : Nat} (layout : QuantumLayout systemCount) :=
  (index : Fin systemCount) → Fin (layout.wire index).dimension

/-- The register is derived from the physical systems and their dimensions. -/
@[expose, implicit_reducible]
public def register {systemCount : Nat} (layout : QuantumLayout systemCount) : Register where
  Index := layout.Basis
  fintype := inferInstance
  decEq := inferInstance

/-- The all-zero basis label exists because every wire has positive dimension. -/
@[expose]
public def zeroLabel {systemCount : Nat} (layout : QuantumLayout systemCount) : layout.Basis :=
  fun index => ⟨0, (layout.wire index).dimension.pos⟩

/-- Dimension of the joint basis, derived as the product of wire dimensions. -/
@[expose]
public def basisCardinality {systemCount : Nat} (layout : QuantumLayout systemCount) : Nat :=
  ∏ index, ((layout.wire index).dimension : Nat)

/-- The register's actual finite basis has the dimension derived from its wires. -/
@[simp] public theorem register_card {systemCount : Nat}
    (layout : QuantumLayout systemCount) :
    Fintype.card layout.register.Index = layout.basisCardinality := by
  calc
    Fintype.card layout.register.Index =
        Fintype.card ((index : Fin systemCount) → Fin (layout.wire index).dimension) :=
      Fintype.card_congr (Equiv.refl _)
    _ = layout.basisCardinality := by
      simp only [Fintype.card_pi, Fintype.card_fin, basisCardinality]

/-- Exact number of physical systems with one prescribed positive dimension. -/
@[expose]
public def dimensionCount {systemCount : Nat} (layout : QuantumLayout systemCount)
    (dimension : ℕ+) : Nat :=
  layout.dimensions.count dimension

/-- Uniform dimensions still retain the separately certified physical placement. -/
@[expose]
public def uniform (systemCount : Nat) (dimension : ℕ+)
    (identity : Fin systemCount → Nat) (distinct : Function.Injective identity) :
    QuantumLayout systemCount where
  wire := fun index => ⟨identity index, dimension⟩
  identityInjective := distinct

/-- A uniform register's basis size is the appropriate power of its local dimension. -/
@[simp] public theorem basisCardinality_uniform (systemCount : Nat) (dimension : ℕ+)
    (identity : Fin systemCount → Nat) (distinct : Function.Injective identity) :
    (uniform systemCount dimension identity distinct).basisCardinality =
      (dimension : Nat) ^ systemCount := by
  simp [basisCardinality, uniform]

/-- Uniform layouts count their actual systems only at their declared dimension. -/
public theorem dimensionCount_uniform (systemCount : Nat) (dimension query : ℕ+)
    (identity : Fin systemCount → Nat) (distinct : Function.Injective identity) :
    (uniform systemCount dimension identity distinct).dimensionCount query =
      if dimension = query then systemCount else 0 := by
  by_cases equal : dimension = query <;>
    simp [dimensionCount, dimensions, uniform, List.ofFn_const, List.count_replicate, equal]

/-- Append layouts only when their physical identities are disjoint. -/
@[expose]
public def append {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    QuantumLayout (leftCount + rightCount) where
  wire := Fin.append left.wire right.wire
  identityInjective := by
    apply List.nodup_ofFn.mp
    rw [List.ofFn_comp', List.ofFn_fin_append, List.map_append]
    simpa only [identities, List.map_ofFn, Function.comp_def] using
      left.identities_nodup.append right.identities_nodup disjoint

@[simp] public theorem wires_append {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    (append left right disjoint).wires = left.wires ++ right.wires := by
  simp [wires, append, List.ofFn_fin_append]

@[simp] public theorem dimensions_append {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) :
    (append left right disjoint).dimensions = left.dimensions ++ right.dimensions := by
  change List.ofFn (fun index => (Fin.append left.wire right.wire index).dimension) = _
  rw [List.ofFn_comp', List.ofFn_fin_append, List.map_append, List.map_ofFn, List.map_ofFn]
  rfl

/-- Each dimension's live-system count adds across disjoint layouts. -/
@[simp] public theorem dimensionCount_append {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (disjoint : List.Disjoint left.identities right.identities) (dimension : ℕ+) :
    (append left right disjoint).dimensionCount dimension =
      left.dimensionCount dimension + right.dimensionCount dimension := by
  simp [dimensionCount, dimensions_append]

end QuantumLayout

end QuantumAlg

end

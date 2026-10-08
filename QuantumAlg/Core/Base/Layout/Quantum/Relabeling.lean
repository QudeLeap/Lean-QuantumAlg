/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
public import Mathlib.Logic.Embedding.Basic

/-!
# Injective placement of existing finite-dimensional systems

A physical embedding changes the addresses at which the same systems are
placed. Every dimension, logical position and finite basis value is retained,
and distinct physical identities remain distinct. Native circuit placement
must use the same embedding; this descriptor performs no runtime operation.
-/

namespace QuantumAlg

namespace QuantumWire

/-- Place the same finite-dimensional system at its prescribed injective physical address. -/
@[expose] public def relabel (physical : Nat ↪ Nat) (wire : QuantumWire) : QuantumWire where
  identity := physical wire.identity
  dimension := wire.dimension

/-- Injective physical placement retains complete wire-record distinguishability. -/
public theorem relabel_injective (physical : Nat ↪ Nat) :
    Function.Injective (relabel physical) := by
  intro left right same
  have identities := physical.injective (congrArg QuantumWire.identity same)
  have dimensions := congrArg QuantumWire.dimension same
  cases left with
  | mk leftIdentity leftDimension =>
    cases right with
    | mk rightIdentity rightDimension =>
      cases identities
      cases dimensions
      rfl

end QuantumWire

namespace QuantumLayout

variable {count : Nat}

/-- Every existing logical position receives its own injectively mapped physical identity. -/
@[expose] public def relabel (layout : QuantumLayout count)
    (physical : Nat ↪ Nat) : QuantumLayout count where
  wire index := QuantumWire.relabel physical (layout.wire index)
  identityInjective := fun _ _ equal => layout.identityInjective (physical.injective equal)

/-- The ordered wire list uses exactly the same physical map as its per-position definition. -/
public theorem relabel_wires (layout : QuantumLayout count) (physical : Nat ↪ Nat) :
    (layout.relabel physical).wires = layout.wires.map (QuantumWire.relabel physical) := by
  simp only [wires, List.map_ofFn]
  rfl

/-- The complete physical identity list is precisely the injective image of the original list. -/
public theorem relabel_identities (layout : QuantumLayout count) (physical : Nat ↪ Nat) :
    (layout.relabel physical).identities = layout.identities.map physical := by
  simp only [identities, List.map_ofFn]
  rfl

/-- Placement preserves every positive native dimension in its original logical order. -/
public theorem relabel_dimensions (layout : QuantumLayout count) (physical : Nat ↪ Nat) :
    (layout.relabel physical).dimensions = layout.dimensions := rfl

/-- Every dimension-indexed resident quantum count remains unchanged by placement. -/
public theorem relabel_dimensionCount (layout : QuantumLayout count) (physical : Nat ↪ Nat)
    (dimension : ℕ+) :
    (layout.relabel physical).dimensionCount dimension = layout.dimensionCount dimension := rfl

/-- Logical basis values retain the same finite dimension at every original position. -/
@[expose] public def relabelBasis (layout : QuantumLayout count) (physical : Nat ↪ Nat) :
    layout.register.Index ≃ (layout.relabel physical).register.Index := Equiv.refl _

/-- The finite value at each mapped physical system is unchanged, including nonbinary systems. -/
public theorem relabelBasis_value (layout : QuantumLayout count) (physical : Nat ↪ Nat)
    (value : layout.register.Index) (index : Fin count) :
    (relabelBasis layout physical value index).val = (value index).val := rfl

end QuantumLayout

end QuantumAlg

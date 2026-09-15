/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.SourceLayout

/-!
# A selected modular offset placed on the original two words

The actual controlled pivot-flip offset borrows two source coordinates
different from its selector and returns them exactly. Its explicit basis
and physical placements share the source-selector wire permutation and
the helper block rotation. No gate is introduced by this placement, and
the target update covers every label with the established identity extension.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth

/-- The unchanged source selects an exact modular offset of the target. -/
def selectedOutput {width : Nat} (selected : Fin width) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (state : Registers width) : Registers width :=
  (state.1, if state.1.val.testBit selected.val then
    modularWordOutput modulus constant state.2 else state.2)

theorem gidneySelectedWords_output (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (state : CanonicalRegisters extra) :
    selectedWordsEquiv extra selected (canonicalOutput modulus constant state) =
      selectedOutput selected modulus constant (selectedWordsEquiv extra selected state) := by
  unfold selectedOutput
  rw [gidneySelectedWords_selector]
  rcases state with ⟨control, unused, flag, target, helper⟩
  cases control <;> rfl

/-- Place the actual stage, mapping both its binary coordinates and its physical identifiers. -/
def placedStageProgram (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit (Qubits (encoding (extra + 3)).width) :=
  let transported := UnitaryCircuit.reindex (stagePlacementIndex extra selected)
    (canonicalProgram extra modulus constant)
  transported.relabel
    { toFun := stagePlacementWire extra selected
      map_layout := rfl
      old_nodup := transported.physical_idx_nodup
      new_nodup := transported.physical_idx_nodup.map
        (gidneyStagePlacementWire_injective extra selected) }

/-- Every source bit, including both arbitrarily initialized borrowed bits, is returned exactly. -/
theorem gidneyPlacedStage_realizes (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding (extra + 3))
      (placedStageProgram extra selected modulus constant)
      (selectedOutput selected modulus constant) where
  apply_encoded_ket := by
    intro state
    obtain ⟨source, rfl⟩ := (selectedWordsEquiv extra selected).surjective state
    have hrun := (gidneyCanonicalStage_realizes extra modulus constant).apply_encoded_ket source
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (canonicalEncoding extra).width)
      (S := Qubits (encoding (extra + 3)).width)
      (stagePlacementIndex extra selected) (canonicalProgram extra modulus constant)
      _ _ hrun
    change (UnitaryCircuit.reindex (stagePlacementIndex extra selected)
        (canonicalProgram extra modulus constant)).applyNormalized
          (NormalizedVector.ket (R := Qubits (encoding (extra + 3)).width)
            (stagePlacementIndex extra selected ((canonicalEncoding extra).encode source))) =
      NormalizedVector.ket (R := Qubits (encoding (extra + 3)).width)
        (stagePlacementIndex extra selected
          ((canonicalEncoding extra).encode (canonicalOutput modulus constant source))) at hplaced
    rw [gidneyStagePlacementIndex_encode, gidneyStagePlacementIndex_encode,
      gidneySelectedWords_output] at hplaced
    unfold placedStageProgram
    dsimp only
    exact (UnitaryCircuit.Realizes.applyNormalized_relabel
      (R := Qubits (encoding (extra + 3)).width)
      (UnitaryCircuit.reindex
        (R := Qubits (canonicalEncoding extra).width)
        (S := Qubits (encoding (extra + 3)).width)
        (stagePlacementIndex extra selected) (canonicalProgram extra modulus constant))
      _ _).trans hplaced

/-- The placed stage accesses only the original source and target coordinates. -/
theorem gidneyPlacedStage_physical_range (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (placedStageProgram extra selected modulus constant).physical_idx ⊆
      List.range (2 * (extra + 3)) := by
  intro wire hwire
  change wire ∈ List.map (stagePlacementWire extra selected)
    (canonicalProgram extra modulus constant).physical_idx at hwire
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hwire
  have hinside := List.mem_range.mp
    (gidneyCanonicalStage_physical_range extra modulus constant hsource)
  exact List.mem_range.mpr (gidneyStagePlacementWire_range extra selected source hinside)

/-- The literal native events and their schedule are preserved by exact wire placement. -/
theorem gidneyPlacedStage_resources (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (assign : Resource.Event .quantum → Nat) :
    (placedStageProgram extra selected modulus constant).eventCost =
        (canonicalProgram extra modulus constant).eventCost ∧
      (placedStageProgram extra selected modulus constant).evaluatedEventDepth assign =
        (canonicalProgram extra modulus constant).evaluatedEventDepth assign := by
  constructor
  · unfold placedStageProgram
    exact UnitaryCircuit.relabel_eventCost _ _
  · unfold placedStageProgram
    exact UnitaryCircuit.evaluatedEventDepth_relabel _ _ assign

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney

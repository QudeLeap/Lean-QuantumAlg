/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Layout.Quantum
public import Mathlib.Logic.Equiv.Basic

/-!
# Embedding the same physical systems in an ambient layout

An embedding selects distinct positions containing exactly the original wires.
Its basis maps only restrict and reassemble those coordinates. They cannot
change a local basis value or implement a permutation of quantum states.
-/

namespace QuantumAlg.QuantumLayout

/-- An ordered subsystem consists of the same physical wires in a larger layout. -/
public structure Embedding {small large : Nat}
    (source : QuantumLayout small) (target : QuantumLayout large) where
  /-- Distinct source positions select distinct ambient positions. -/
  position : Fin small ↪ Fin large
  /-- Selection preserves both physical identity and local dimension. -/
  wire_eq : ∀ index, target.wire (position index) = source.wire index

namespace Embedding

variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- The ambient positions occupied by the ordered subsystem. -/
@[expose]
public def selection (embedding : Embedding source target) : Finset (Fin large) :=
  Finset.univ.map embedding.position

/-- Source order identifies the selected ambient positions without changing their values. -/
@[expose]
public noncomputable def positionEquiv (embedding : Embedding source target) :
    Fin small ≃ SelectedPosition embedding.selection :=
  Equiv.ofBijective
    (fun index => ⟨embedding.position index, Finset.mem_map_of_mem _ (Finset.mem_univ _)⟩)
    ⟨fun _ _ equality => embedding.position.injective (congrArg Subtype.val equality), by
      intro index
      obtain ⟨original, _, same⟩ := Finset.mem_map.mp index.property
      exact ⟨original, Subtype.ext same⟩⟩

/-- The selected position is exactly the supplied wire position. -/
public theorem embedding_positionEquiv_val (embedding : Embedding source target)
    (index : Fin small) :
    (embedding.positionEquiv index).val = embedding.position index := rfl

/-- Dimension equality casts a local value without permuting the computational basis. -/
@[expose]
public noncomputable def valueEquiv (embedding : Embedding source target) (index : Fin small) :
    Fin (source.wire index).dimension ≃
      Fin (target.wire (embedding.positionEquiv index).val).dimension where
  toFun value := Fin.cast (congrArg (fun wire => wire.dimension.val)
    (embedding.wire_eq index).symm) value
  invFun value := Fin.cast (congrArg (fun wire => wire.dimension.val)
    (embedding.wire_eq index)) value
  left_inv value := by
    apply Fin.ext
    rfl
  right_inv value := by
    apply Fin.ext
    rfl

/-- Reading a source value at its selected position preserves its full finite value. -/
public theorem embedding_valueEquiv_val (embedding : Embedding source target)
    (index : Fin small) (value : Fin (source.wire index).dimension) :
    (embedding.valueEquiv index value).val = value.val := rfl

/-- The selected subsystem basis in source order; every coordinate map is a dimension cast. -/
@[expose]
public noncomputable def selectedBasisEquiv (embedding : Embedding source target) :
    source.Basis ≃ target.SelectedBasis embedding.selection :=
  embedding.positionEquiv.piCongr embedding.valueEquiv

/-- The ordered-subsystem basis keeps each original local value. -/
public theorem embedding_selectedBasisEquiv_val (embedding : Embedding source target)
    (basis : source.Basis) (index : Fin small) :
    (embedding.selectedBasisEquiv basis (embedding.positionEquiv index)).val =
      (basis index).val := by
  rw [selectedBasisEquiv, Equiv.piCongr_apply_apply]
  rfl

/-- Split an ambient basis into the ordered subsystem and every untouched wire. -/
@[expose]
public noncomputable def splitBasis (embedding : Embedding source target) :
    target.Basis ≃ source.Basis × target.ComplementBasis embedding.selection :=
  (target.selectionBasisEquiv embedding.selection).trans
    (Equiv.prodCongr embedding.selectedBasisEquiv.symm (Equiv.refl _))

/-- Splitting reads precisely the original basis value at each selected physical wire. -/
public theorem embedding_splitBasis_selected_value (embedding : Embedding source target)
    (basis : target.Basis) (index : Fin small) :
    ((embedding.splitBasis basis).1 index).val =
      (basis (embedding.position index)).val := rfl

/-- Splitting retains the exact joint basis of all unselected systems. -/
public theorem embedding_splitBasis_complement_value (embedding : Embedding source target)
    (basis : target.Basis) (index : SelectedPosition embedding.selectionᶜ) :
    (embedding.splitBasis basis).2 index = basis index.val := rfl

end Embedding

end QuantumAlg.QuantumLayout

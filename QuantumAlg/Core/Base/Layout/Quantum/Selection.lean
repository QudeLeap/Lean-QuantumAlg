/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Layout.Quantum
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Pi

/-!
# Exact basis coordinates for selected quantum wires

A selection names positions in an existing layout. Its basis retains the
dimension at each selected physical wire; the complementary basis retains
every remaining wire. Restriction and reassembly use those positions directly,
without choosing a bijection from Hilbert-space cardinalities. This is the
concrete subsystem decomposition of the tensor basis [dW19, qcnotes.tex:389].
-/

section

namespace QuantumAlg.QuantumLayout

variable {systemCount : Nat}

/-- The original positions of the selected physical wires. -/
public abbrev SelectedPosition (selection : Finset (Fin systemCount)) :=
  {index : Fin systemCount // index ∈ selection}

/-- Selection retains the exact original physical wire record. -/
@[expose]
public def selectedWire (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (index : SelectedPosition selection) :
    QuantumWire :=
  layout.wire index.val

/-- A selected wire has the same physical identity as its original position. -/
public theorem selectedWire_identity (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (index : SelectedPosition selection) :
    (layout.selectedWire selection index).identity = (layout.wire index.val).identity := rfl

/-- A selected wire keeps its actual local dimension. -/
public theorem selectedWire_dimension (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (index : SelectedPosition selection) :
    (layout.selectedWire selection index).dimension = (layout.wire index.val).dimension := rfl

/-- Restriction cannot introduce repeated physical identities. -/
public theorem selectedWire_identity_injective (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :
    Function.Injective (fun index => (layout.selectedWire selection index).identity) := by
  intro left right sameIdentity
  exact Subtype.ext (layout.identityInjective sameIdentity)

/-- One local finite value at each selected original position. -/
public abbrev SelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :=
  (index : SelectedPosition selection) → Fin (layout.wire index.val).dimension

/-- One local finite value at every position outside the selection. -/
public abbrev ComplementBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :=
  layout.SelectedBasis selectionᶜ

/-- The selected register uses the exact dependent product of local bases. -/
@[expose, implicit_reducible]
public def selectedRegister (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) : Register where
  Index := layout.SelectedBasis selection
  fintype := inferInstance
  decEq := inferInstance

/-- The complementary register contains all unselected original positions. -/
@[expose, implicit_reducible]
public def complementRegister (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) : Register :=
  layout.selectedRegister selectionᶜ

/-- Read the original basis value at each selected position. -/
@[expose]
public def restrictSelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (basis : layout.Basis) :
    layout.SelectedBasis selection :=
  fun index => basis index.val

/-- Read the original basis value at every complementary position. -/
@[expose]
public def restrictComplementBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (basis : layout.Basis) :
    layout.ComplementBasis selection :=
  layout.restrictSelectedBasis selectionᶜ basis

/-- Reassemble a label by membership of each original physical position. -/
@[expose]
public def joinSelectedBasis (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection) : layout.Basis :=
  fun index => if member : index ∈ selection then selected ⟨index, member⟩
    else complement ⟨index, Finset.mem_compl.mpr member⟩

/-- Reassembly restores the full finite value at every selected physical wire. -/
public theorem joinSelectedBasis_selected_value (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection) (index : SelectedPosition selection) :
    layout.joinSelectedBasis selection selected complement index.val = selected index := by
  simp only [joinSelectedBasis, dif_pos index.property]

/-- Reassembly restores the full finite value at every complementary wire. -/
public theorem joinSelectedBasis_complement_value (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection)
    (index : SelectedPosition selectionᶜ) :
    layout.joinSelectedBasis selection selected complement index.val = complement index := by
  simp only [joinSelectedBasis, dif_neg (Finset.mem_compl.mp index.property)]

/-- Selection and complement give an exact basis equivalence by restriction. -/
@[expose]
public def selectionBasisEquiv (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) :
    layout.Basis ≃ layout.SelectedBasis selection × layout.ComplementBasis selection where
  toFun basis :=
    (layout.restrictSelectedBasis selection basis, layout.restrictComplementBasis selection basis)
  invFun basis := layout.joinSelectedBasis selection basis.1 basis.2
  left_inv basis := by
    funext index
    by_cases member : index ∈ selection <;>
      simp [joinSelectedBasis, restrictSelectedBasis, restrictComplementBasis, member]
  right_inv basis := by
    apply Prod.ext
    · funext index
      exact layout.joinSelectedBasis_selected_value selection basis.1 basis.2 index
    · funext index
      exact layout.joinSelectedBasis_complement_value selection basis.1 basis.2 index

/-- Splitting reassembled coordinates recovers both subsystem labels exactly. -/
public theorem selectionBasisEquiv_join (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (selected : layout.SelectedBasis selection)
    (complement : layout.ComplementBasis selection) :
    layout.selectionBasisEquiv selection
      (layout.joinSelectedBasis selection selected complement) = (selected, complement) :=
  (layout.selectionBasisEquiv selection).apply_symm_apply (selected, complement)

/-- Restricting and reassembling retains every coordinate of the original label. -/
public theorem joinSelectedBasis_restrict (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (basis : layout.Basis) :
    layout.joinSelectedBasis selection (layout.restrictSelectedBasis selection basis)
      (layout.restrictComplementBasis selection basis) = basis :=
  (layout.selectionBasisEquiv selection).symm_apply_apply basis

end QuantumAlg.QuantumLayout

end

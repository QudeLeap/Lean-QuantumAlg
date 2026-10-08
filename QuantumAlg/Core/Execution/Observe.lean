/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Selection
public import QuantumAlg.Core.Base.Register
public import QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Execution.Reindex
import Mathlib.Logic.Equiv.Prod

/-!
# Density observations of actual selected wires

An observation reads a subsystem of the one complete density operator. The
selected positions determine its basis; tracing the complement preserves all
matrix entries between the retained positions. A joint observation also keeps
an arbitrary external reference, including its off-diagonal correlations.

These are mathematical projections of the density matrix
[dW19, qcnotes.tex:5381]. They do not execute gates, remove physical wires, or
change a live context or its space account.
-/

section

namespace QuantumAlg

noncomputable section

variable {systemCount : Nat}

/-- Reorder only the exact selected, complementary, and reference coordinates. -/
private def selectionReferenceBasisEquiv (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register) :
    (Register.prod layout.register Reference).Index ≃
      (Register.prod (Register.prod (layout.selectedRegister selection) Reference)
        (layout.complementRegister selection)).Index :=
  ((layout.selectionBasisEquiv selection).prodCongr (Equiv.refl Reference.Index)).trans
    ((Equiv.prodAssoc (layout.SelectedBasis selection) (layout.ComplementBasis selection)
      Reference.Index).trans
      ((Equiv.prodCongr (Equiv.refl (layout.SelectedBasis selection))
        (Equiv.prodComm (layout.ComplementBasis selection) Reference.Index)).trans
        (Equiv.prodAssoc (layout.SelectedBasis selection) Reference.Index
          (layout.ComplementBasis selection)).symm))

namespace DensityOperator

/-- Observe the selected actual systems jointly with the entire external reference. -/
def observeSelectionWithReference (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference)) :
    DensityOperator (Register.prod (layout.selectedRegister selection) Reference) :=
  (state.reindex
    (S := Register.prod (Register.prod (layout.selectedRegister selection) Reference)
      (layout.complementRegister selection))
    (selectionReferenceBasisEquiv layout selection Reference)).marginalLeft

/-- Only complementary coordinates are summed; both selected and reference
row/column coordinates remain independent, preserving their coherences. -/
theorem observeSelectionWithReference_entry (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference))
    (row column : layout.SelectedBasis selection) (refRow refColumn : Reference.Index) :
    (observeSelectionWithReference layout selection Reference state).matrix
      (row, refRow) (column, refColumn) =
      ∑ complement : layout.ComplementBasis selection,
        state.matrix (layout.joinSelectedBasis selection row complement, refRow)
          (layout.joinSelectedBasis selection column complement, refColumn) := by
  rw [observeSelectionWithReference, marginalLeft_matrix]
  rfl

/-- Keeping selected systems and the reference preserves the complete branch mass. -/
theorem observeSelectionWithReference_mass (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference)) :
    (observeSelectionWithReference layout selection Reference state).mass = state.mass := by
  rw [observeSelectionWithReference, marginalLeft_mass, reindex_mass]

/-- Observe the selected actual systems while summing their complement and the reference. -/
public def observeSelection (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference)) :
    DensityOperator (layout.selectedRegister selection) :=
  (observeSelectionWithReference layout selection Reference state).marginalLeft

/-- The selected density matrix retains off-diagonal selected entries and
sums exactly equal row/column coordinates of the discarded subsystems. -/
theorem observeSelection_entry (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference))
    (row column : layout.SelectedBasis selection) :
    (observeSelection layout selection Reference state).matrix row column =
      ∑ reference : Reference.Index, ∑ complement : layout.ComplementBasis selection,
        state.matrix (layout.joinSelectedBasis selection row complement, reference)
          (layout.joinSelectedBasis selection column complement, reference) := by
  exact (marginalLeft_matrix (R := layout.selectedRegister selection) (S := Reference)
    (observeSelectionWithReference layout selection Reference state) row column).trans
      (Finset.sum_congr rfl fun reference _ =>
        observeSelectionWithReference_entry layout selection Reference state
          row column reference reference)

/-- Discarding only state information preserves branch probability. -/
theorem observeSelection_mass (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference)) :
    (observeSelection layout selection Reference state).mass = state.mass := by
  rw [observeSelection, marginalLeft_mass, observeSelectionWithReference_mass]

/-- The local observation is precisely the reference marginal of the joint observation. -/
theorem observeSelection_eq_referenceMarginal (layout : QuantumLayout systemCount)
    (selection : Finset (Fin systemCount)) (Reference : Register)
    (state : DensityOperator (Register.prod layout.register Reference)) :
    observeSelection layout selection Reference state =
      (observeSelectionWithReference layout selection Reference state).marginalLeft := rfl

end DensityOperator

end

end QuantumAlg

end

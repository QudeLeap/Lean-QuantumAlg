/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target.Basis
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Basis
import all QuantumAlg.Core.Execution.Context.Permutation.Preparation
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Coordinates

/-!
# Actual input and initialized point-addition basis assembly

Only the original coordinate words and coherent control appear in the input
label. The two fixed preparations and the actual original result-cell retains
establish the internal arithmetic frame and selector. Their physical basis
assembly is exactly the one used by the accepted measured body.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- A supplied label contains only the two original arbitrary words and arbitrary control. -/
def inputLabel (width : Nat) (control : Fin 2) (x y : Fin (2 ^ width)) :
    (before width).register.Index :=
  (unionBasisEquiv (InversePreparation.before width) (InPlaceControlled.controlContext width)
    (input_disjoint_control width)).symm
      ((InversePreparation.inputBasisEquiv width).symm (x, y),
        (InPlaceControlled.controlBasis width).symm control)

/-- Every supplied basis has exactly those original word and control coordinates. -/
theorem inputLabel_surjective (width : Nat) (original : (before width).register.Index) :
    ∃ (control : Fin 2) (x y : Fin (2 ^ width)), original = inputLabel width control x y := by
  obtain ⟨⟨old, control⟩, rfl⟩ :=
    (unionBasisEquiv (InversePreparation.before width) (InPlaceControlled.controlContext width)
      (input_disjoint_control width)).symm.surjective original
  obtain ⟨⟨x, y⟩, rfl⟩ := (InversePreparation.inputBasisEquiv width).symm.surjective old
  obtain ⟨control, rfl⟩ := (InPlaceControlled.controlBasis width).symm.surjective control
  exact ⟨control, x, y, rfl⟩

/-- Actual auxiliary preparation coordinates keep the full supplied control context. -/
def auxiliaryAssembly (modulus : Nat) :
    ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (before modulus.size).register.Index) ≃
      ((InversePreparation.after modulus.size).disjointUnion
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)).register.Index :=
  preparedFramedBasisEquiv InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) (auxiliary_disjoint_control modulus.size)

/-- Actual cell allocation keeps the original quantum coordinates beside the supplied control. -/
def cellsAssembly (width : Nat) :
    ((InversePreparation.after width).disjointUnion (InPlaceControlled.controlContext width)
      (auxiliary_disjoint_control width)).register.Index ≃
        (InPlaceControlled.context width).register.Index :=
  MeasurementCells.framedBasisEquiv (InversePreparation.after width)
    (InPlaceControlled.controlContext width) 2 width (InPlaceControlled.control_disjoint width)

/-- Actual selector preparation uses its original owned physical wire. -/
def selectorAssembly (width : Nat) :
    ((selectorLayout width).register.Index × (InPlaceControlled.context width).register.Index) ≃
      (after width).register.Index :=
  preparedLocalBasisEquiv (InPlaceControlled.context width) (selectorKey width)
    (selectorLayout width) (InPlaceControlled.context width).canonicalFreshKey_fresh
    (selector_physical_disjoint width)

/-- All fresh and original basis coordinates assemble through the three actual allocation steps. -/
def initializedAssembly (modulus : Nat) :
    ((selectorLayout modulus.size).register.Index ×
      ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
        (before modulus.size).register.Index)) ≃ (after modulus.size).register.Index :=
  (Equiv.prodCongr (Equiv.refl _) ((auxiliaryAssembly modulus).trans
    (cellsAssembly modulus.size))).trans (selectorAssembly modulus.size)

/-- Actual work preparation retains both original words and the supplied control coordinates. -/
theorem auxiliaryAssembly_input (modulus : Nat) (control : Fin 2)
    (x y : Fin (2 ^ modulus.size)) :
    auxiliaryAssembly modulus ((InPlacePreparation.preparation modulus).value,
      inputLabel modulus.size control x y) =
      (unionBasisEquiv (InversePreparation.after modulus.size)
        (InPlaceControlled.controlContext modulus.size)
        (auxiliary_disjoint_control modulus.size)).symm
        (InversePreparation.assembly modulus.size ((InPlacePreparation.preparation modulus).value,
          (InversePreparation.inputBasisEquiv modulus.size).symm (x, y)),
          (InPlaceControlled.controlBasis modulus.size).symm control) :=
  preparedFramedBasis_join InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size)
    (auxiliary_disjoint_control modulus.size) _ _ _

/-- Retaining the original cells keeps all arithmetic and coherent-control basis values. -/
theorem cellsAssembly_input (width : Nat) (control : Fin 2)
    (original : (InversePreparation.after width).register.Index) :
    cellsAssembly width
      ((unionBasisEquiv (InversePreparation.after width) (InPlaceControlled.controlContext width)
        (auxiliary_disjoint_control width)).symm
          (original, (InPlaceControlled.controlBasis width).symm control)) =
      InPlaceControlled.label width control
        (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width original) :=
  MeasurementCells.framedBasisEquiv_join (InversePreparation.after width)
    (InPlaceControlled.controlContext width) 2 width
    (InPlaceControlled.control_disjoint width) original
    ((InPlaceControlled.controlBasis width).symm control)

/-- Fixed preparation and retained cells establish the original complete A=0 arithmetic frame. -/
theorem auxiliary_cells_input (modulus : Nat) (control : Fin 2)
    (x y : Fin (2 ^ modulus.size)) :
    cellsAssembly modulus.size
      (auxiliaryAssembly modulus ((InPlacePreparation.preparation modulus).value,
        inputLabel modulus.size control x y)) =
      InPlaceControlled.label modulus.size control (InPlaceTarget.preparedBasis modulus x y) := by
  rw [auxiliaryAssembly_input]
  exact cellsAssembly_input modulus.size control
    (InversePreparation.assembly modulus.size ((InPlacePreparation.preparation modulus).value,
      (InversePreparation.inputBasisEquiv modulus.size).symm (x, y)))

private theorem selector_zero_coordinates (width : Nat) :
    basisOfEqualWires (selectorLayout width) (selectorContext width).quantumLayout
      (selector_wires width) (BasisPreparation.zero (selectorLayout width)).value =
        (selectorBasis width).symm 0 := by
  apply (selectorBasis width).injective
  rw [Equiv.apply_symm_apply]
  change (selectorQubitLayout width).binaryIndexEquiv
    ((basisOfEqualWires _ _ (selector_wires width)).symm
      (basisOfEqualWires _ _ (selector_wires width)
        (BasisPreparation.zero (selectorLayout width)).value)) = 0
  rw [Equiv.symm_apply_apply]
  have zero : (BasisPreparation.zero (selectorLayout width)).value =
      (selectorQubitLayout width).binaryIndexEquiv.symm 0 := by
    funext index
    change (0 : Fin 2) = finTwoEquiv.symm ((0 : Fin 2).val.testBit index.rev.val)
    simp only [Fin.val_zero, Nat.zero_testBit]
    rfl
  exact (congrArg (selectorQubitLayout width).binaryIndexEquiv zero).trans
    ((selectorQubitLayout width).binaryIndexEquiv.apply_symm_apply 0)

/-- The actual zero preparation is the body's same physical internal zero selector. -/
theorem selector_zero_input (width : Nat)
    (original : (InPlaceControlled.context width).register.Index) :
    selectorAssembly width ((BasisPreparation.zero (selectorLayout width)).value, original) =
      ContextPermutation.basis (body_entries width)
        ((unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
          (selector_disjoint width)).symm (original, (selectorBasis width).symm 0)) := by
  have actual := ContextPermutation.preparation_basis_union (selectorKey width)
    (selectorLayout width) (InPlaceControlled.context width).canonicalFreshKey_fresh
    (selector_physical_disjoint width) (selector_wires width) (selector_disjoint width)
    (body_entries width) (BasisPreparation.zero (selectorLayout width)).value original
  rw [selector_zero_coordinates] at actual
  exact actual.symm

/-- Both actual fixed preparations establish exactly the prepared support used by the body. -/
theorem initializedAssembly_input (modulus : Nat) (control : Fin 2)
    (x y : Fin (2 ^ modulus.size)) :
    initializedAssembly modulus
      ((BasisPreparation.zero (selectorLayout modulus.size)).value,
        (InPlacePreparation.preparation modulus).value, inputLabel modulus.size control x y) =
      ContextPermutation.basis (body_entries modulus.size)
        (label modulus.size control 0 (InPlaceTarget.preparedBasis modulus x y)) := by
  change selectorAssembly modulus.size (_, cellsAssembly modulus.size
    (auxiliaryAssembly modulus (_, inputLabel modulus.size control x y))) = _
  rw [auxiliary_cells_input]
  exact selector_zero_input modulus.size
    (InPlaceControlled.label modulus.size control (InPlaceTarget.preparedBasis modulus x y))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

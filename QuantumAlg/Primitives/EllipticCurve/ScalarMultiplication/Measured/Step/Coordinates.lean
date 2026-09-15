/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Correctness
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Basis

/-!
# Actual selected point coordinates inside the complete scalar workspace

The point and ambient coordinates come from the same physical placement and
entry permutation as the actual indexed step. Each original point-system
value is read on its prescribed real physical system, including the shared
arithmetic frame, selected exponent and common selector.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

/-- Split the actual ready context into original point values and the complete resident frame. -/
def pointBasis (width : Nat) {count : Nat} (active : Fin count) :
    (readyContext width count).register.Index ≃
      (MeasuredPointAddition.context width).register.Index ×
        (ambientContext width active).register.Index :=
  (ContextPermutation.basis (framed_entries width active)).symm.trans
    ((ContextUnion.unionBasisEquiv
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active)
        (ambient_disjoint width active)).trans
      (Equiv.prodCongr (ContextRelabeling.basis (MeasuredPointAddition.context width)
        (storageMap width active) (physicalMap width active)).symm (Equiv.refl _)))

/-- Each original point-system position names the physical system used by the actual step. -/
def pointPosition (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (MeasuredPointAddition.context width).systemCount) :
    Fin (readyContext width count).systemCount :=
  ContextPermutation.positions (framed_entries width active)
    (ContextUnion.leftPosition
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
      (ContextRelabeling.positions (MeasuredPointAddition.context width)
        (storageMap width active) (physicalMap width active) index))

/-- Actual common-context placement has exactly the original mapped physical identity and shape. -/
theorem pointPosition_wire (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (MeasuredPointAddition.context width).systemCount) :
    (readyContext width count).quantumLayout.wire (pointPosition width active index) =
      QuantumWire.relabel (physicalMap width active)
        ((MeasuredPointAddition.context width).quantumLayout.wire index) := by
  rw [pointPosition, ContextPermutation.positions_wire, ContextUnion.contextUnion_left_wire,
    ContextRelabeling.positions_wire]

/-- Point-coordinate extraction reads the exact value on each actual step physical system. -/
theorem pointBasis_value (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index)
    (index : Fin (MeasuredPointAddition.context width).systemCount) :
    ((pointBasis width active value).1 index).val =
      (value (pointPosition width active index)).val := by
  let permuted := (ContextPermutation.basis (framed_entries width active)).symm value
  let split := ContextUnion.unionBasisEquiv
    (MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
    permuted
  let relabeled := ContextRelabeling.basis (MeasuredPointAddition.context width)
    (storageMap width active) (physicalMap width active)
  let moved := ContextRelabeling.positions (MeasuredPointAddition.context width)
    (storageMap width active) (physicalMap width active) index
  have originalValue := ContextRelabeling.basis_value (MeasuredPointAddition.context width)
    (storageMap width active) (physicalMap width active) (relabeled.symm split.1) index
  change (relabeled (relabeled.symm split.1) moved).val =
    (relabeled.symm split.1 index).val at originalValue
  rw [Equiv.apply_symm_apply] at originalValue
  have framedValue := ContextUnion.contextUnion_split_left_value
    (MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
    permuted moved
  have readyValue := ContextPermutation.basis_value (framed_entries width active) permuted
    (ContextUnion.leftPosition
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
      moved)
  change ((ContextPermutation.basis (framed_entries width active))
    ((ContextPermutation.basis (framed_entries width active)).symm value)
      (pointPosition width active index)).val = _ at readyValue
  rw [Equiv.apply_symm_apply] at readyValue
  exact originalValue.symm.trans (framedValue.symm.trans readyValue.symm)

/-- The step's domain is precisely the original point domain on its extracted physical values. -/
theorem stepAdmissible_pointBasis {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    stepAdmissible E Q active value ↔
      MeasuredPointAddition.admissible E Q (pointBasis p.size active value).1 := Iff.rfl

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

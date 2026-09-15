/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Target

/-!
# Actual ambient values retained by the independent indexed point target

The resident ambient coordinates use the same context union and entry
permutation as the actual step. Each coordinate reads its original physical
system in the complete ready context. The independent step permutation leaves
every such finite value unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

/-- Each resident ambient position names its actual system in the complete step context. -/
def ambientPosition (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (ambientContext width active).systemCount) :
    Fin (readyContext width count).systemCount :=
  ContextPermutation.positions (framed_entries width active)
    (ContextUnion.rightPosition
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
      index)

/-- Ambient placement retains each original physical identity and local dimension. -/
theorem ambientPosition_wire (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (ambientContext width active).systemCount) :
    (readyContext width count).quantumLayout.wire (ambientPosition width active index) =
      (ambientContext width active).quantumLayout.wire index := by
  rw [ambientPosition, ContextPermutation.positions_wire, ContextUnion.contextUnion_right_wire]

/-- The ambient component reads exactly the finite value on its actual resident system. -/
theorem pointBasis_ambient_value (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index)
    (index : Fin (ambientContext width active).systemCount) :
    ((pointBasis width active value).2 index).val =
      (value (ambientPosition width active index)).val := by
  let permuted := (ContextPermutation.basis (framed_entries width active)).symm value
  have framedValue := ContextUnion.contextUnion_split_right_value
    (MeasuredPointAddition.Placement.context width (storageMap width active)
      (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
    permuted index
  have readyValue := ContextPermutation.basis_value (framed_entries width active) permuted
    (ContextUnion.rightPosition
      (MeasuredPointAddition.Placement.context width (storageMap width active)
        (physicalMap width active)) (ambientContext width active) (ambient_disjoint width active)
      index)
  change ((ContextPermutation.basis (framed_entries width active))
    ((ContextPermutation.basis (framed_entries width active)).symm value)
      (ambientPosition width active index)).val = _ at readyValue
  rw [Equiv.apply_symm_apply] at readyValue
  exact framedValue.symm.trans readyValue.symm

/-- The independent step retains every finite value on the actual ambient physical systems. -/
theorem stepPermutation_ambient_value {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index)
    (index : Fin (ambientContext p.size active).systemCount) :
    stepPermutation E Q active value (ambientPosition p.size active index) =
      value (ambientPosition p.size active index) := by
  apply Fin.ext
  rw [← pointBasis_ambient_value p.size active (stepPermutation E Q active value) index,
    ← pointBasis_ambient_value p.size active value index, pointBasis_stepPermutation]

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

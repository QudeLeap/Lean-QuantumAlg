/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Ambient
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Target.Coordinates

/-!
# Complete exponent retention by the independent indexed point target

Every original exponent retains its exact finite value. The selected exponent
is the point control; every other exponent is an actual resident ambient
system. The shared selector is retained by the same point target. These facts
hold on every complete basis value without a preparation premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

private lemma unselected_ambientPosition (width : Nat) {count : Nat} (active : Fin count)
    (index : Fin (count + 1)) (before : index.val < count) (different : index.val ≠ active.val) :
    ∃ position : Fin (ambientContext width active).systemCount,
      ambientPosition width active position = indexedPosition width count index := by
  have member : index.val ∈ (List.range count).erase active.val :=
    (List.mem_erase_of_ne different).mpr (List.mem_range.mpr before)
  have present : QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 ∈
      (ambientContext width active).quantumLayout.wires := by
    rw [RuntimeCtx.quantumLayout_wires]
    change QuantumWire.mk (InPlaceControlled.frameWidth width + index.val) 2 ∈
      (((List.range count).erase active.val).map (indexedEntry width)).flatMap
        RuntimeEntry.quantumWires
    rw [indexed_wires]
    exact List.mem_map.mpr ⟨index.val, member, rfl⟩
  rw [QuantumLayout.wires, List.mem_ofFn] at present
  obtain ⟨position, wire⟩ := present
  refine ⟨position, ?_⟩
  apply (readyContext width count).quantumLayout.position_eq_of_identity_eq
  apply congrArg QuantumWire.identity
  rw [ambientPosition_wire, wire, indexedPosition, ContextUnion.contextUnion_right_wire,
    rangePosition_wire]

/-- Every exponent and the shared selector retain their exact finite values after a point step. -/
lemma stepPermutation_indexedValue {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) (index : Fin (count + 1)) :
    indexedValue p.size count (stepPermutation E Q active value) index =
      indexedValue p.size count value index := by
  by_cases selected : index = active.castSucc
  · subst index
    exact stepPermutation_control E Q active value
  by_cases selector : index = Fin.last count
  · subst index
    exact stepPermutation_selector E Q active value
  have before : index.val < count := by
    have notLast : index.val ≠ count := by
      intro equal
      exact selector (Fin.ext equal)
    omega
  have different : index.val ≠ active.val := by
    intro equal
    exact selected (Fin.ext equal)
  obtain ⟨position, samePosition⟩ := unselected_ambientPosition p.size active index before different
  apply Fin.ext
  rw [indexedValue_value, indexedValue_value, ← samePosition, stepPermutation_ambient_value]

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

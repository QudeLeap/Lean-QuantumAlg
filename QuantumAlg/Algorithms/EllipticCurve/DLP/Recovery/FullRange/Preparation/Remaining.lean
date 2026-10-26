/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Preparation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Remaining

/-!
# Remaining-source preparation starts in the original full-range source state

At consumed offset zero, the mathematical preparation on the existing pair
has exactly the original complete source-square column. Its external
Reference factor is unchanged. All widths remain symbolic, with no physical
preparation, additional bank or change to the original input domain.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open NormalizedVector QuantumFourierTransform.Semiclassical.Window.Source Geometry

/-- The recycled comparison's initial column is the original full-range paired source. -/
lemma fullRange_pairedRemainingPreparation_zero (width : Nat) :
    (pairedRemainingPreparation width 0 (width + width) (Nat.zero_add _)).apply
        (NormalizedVector.ket (R := branchRegister width) (0, 0)) = bareState width := by
  apply NormalizedVector.ext
  intro row
  change (pairedRemainingPreparation width 0 (width + width) (Nat.zero_add _)).applyVec
    (NormalizedVector.ket (R := branchRegister width) (0, 0) :
      HilbertVector (branchRegister width)) row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    window_sourcePaired_remaining_start_column, fullRange_uniformPreparation_zero_column,
    fullRange_uniformPreparation_zero_column]
  rfl

/-- The same original full-q source retains all coherent external-reference amplitudes. -/
lemma fullRange_remainingPreparation_sourceState (width : Nat) {Reference : Register}
    (reference : NormalizedVector Reference) :
    (UnitaryOperator.prodTensor
      (pairedRemainingPreparation width 0 (width + width) (Nat.zero_add _))
      (1 : UnitaryOperator Reference)).applyVec
        (HilbertVector.prodTensor
          (NormalizedVector.ket (R := branchRegister width) (0, 0)).vec reference.vec) =
      (sourceState width reference).vec := by
  rw [UnitaryOperator.prodTensor_applyVec_prodTensor, UnitaryOperator.one_applyVec]
  have prepared :
      (pairedRemainingPreparation width 0 (width + width) (Nat.zero_add _)).applyVec
          (NormalizedVector.ket (R := branchRegister width) (0, 0)).vec =
        (bareState width).vec :=
    congrArg NormalizedVector.vec (fullRange_pairedRemainingPreparation_zero width)
  rw [prepared]
  rfl

end

end QuantumAlg.EllipticCurve.FullRange

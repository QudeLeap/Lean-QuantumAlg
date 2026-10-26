/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation
import all QuantumAlg.Primitives.QFT.Mathematics

/-!
# The complete source square is the same mathematical uniform H column

The arbitrary-width H tensor on zero has exactly the existing full-range
exponent state and its paired source state. The latter retains every external
reference amplitude. These are operator/state identities in the mathematical
observation space; no physical source bank, preparation circuit or free
resource is introduced, and the original sampler is unchanged.
-/

namespace QuantumAlg.EllipticCurve.FullRange

noncomputable section

open NormalizedVector QuantumFourierTransform.Semiclassical.Window.Source
open Geometry

/-- The structural H normalization equals the original full-range normalization. -/
lemma fullRange_uniformPreparation_normalization (width : Nat) :
    invSqrt2 ^ width = FiniteCyclicDLP.invSqrtOrder (2 ^ width) := by
  have factor : invSqrt2 ^ width = invSqrtN width := by
    induction width with
    | zero => simp only [pow_zero, invSqrtN, Real.sqrt_one, Complex.ofReal_one, inv_one]
    | succ width ih => rw [pow_succ', ih, invSqrtN_succ]
  exact factor.trans (by
    simp only [FiniteCyclicDLP.invSqrtOrder, invSqrtN, Nat.cast_pow, Nat.cast_ofNat])

/-- Every original full exponent label has the same exact H zero-column amplitude. -/
lemma fullRange_uniformPreparation_zero_column (width : Nat) (row : (Qubits width).Index) :
    uniformPreparation width row 0 = exponentState width row := by
  rw [window_source_uniformPreparation_zero_column, exponentState_apply,
    fullRange_uniformPreparation_normalization]

/-- The normalized H zero column is the unchanged existing full-range exponent state. -/
lemma fullRange_uniformPreparation_zero (width : Nat) :
    (uniformPreparation width).apply (NormalizedVector.ket 0) = exponentState width := by
  apply NormalizedVector.ext
  intro row
  change (uniformPreparation width).applyVec
    (NormalizedVector.ket (R := Qubits width) 0 : HilbertVector (Qubits width)) row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  exact fullRange_uniformPreparation_zero_column width row

/-- Mathematical uniform preparation on the original pair of full exponent coordinates. -/
def pairedUniformPreparation (width : Nat) : UnitaryOperator (branchRegister width) :=
  UnitaryOperator.prodTensor (uniformPreparation width) (uniformPreparation width)

/-- The paired H column has exactly the existing source-square amplitudes. -/
lemma fullRange_pairedUniformPreparation_zero_column (width : Nat)
    (row : (branchRegister width).Index) :
    pairedUniformPreparation width row (0, 0) = bareState width row := by
  rw [pairedUniformPreparation, UnitaryOperator.prodTensor_apply, bareState,
    NormalizedVector.prodTensor_apply, fullRange_uniformPreparation_zero_column,
    fullRange_uniformPreparation_zero_column]

/-- The normalized paired H column is the unchanged complete source-square state. -/
lemma fullRange_pairedUniformPreparation_zero (width : Nat) :
    (pairedUniformPreparation width).apply (NormalizedVector.ket (0, 0)) =
      bareState width := by
  apply NormalizedVector.ext
  intro row
  change (pairedUniformPreparation width).applyVec
    (NormalizedVector.ket (R := branchRegister width) (0, 0) :
      HilbertVector (branchRegister width)) row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  exact fullRange_pairedUniformPreparation_zero_column width row

/-- The same complete source state retains every arbitrary external-reference amplitude. -/
lemma fullRange_uniformPreparation_sourceState (width : Nat) {Reference : Register}
    (reference : NormalizedVector Reference) :
    (UnitaryOperator.prodTensor (pairedUniformPreparation width)
      (1 : UnitaryOperator Reference)).applyVec
        (HilbertVector.prodTensor
          (NormalizedVector.ket (R := branchRegister width) (0, 0)).vec reference.vec) =
      (sourceState width reference).vec := by
  rw [UnitaryOperator.prodTensor_applyVec_prodTensor, UnitaryOperator.one_applyVec]
  have prepared : (pairedUniformPreparation width).applyVec
      (NormalizedVector.ket (R := branchRegister width) (0, 0)).vec =
        (bareState width).vec :=
    congrArg NormalizedVector.vec (fullRange_pairedUniformPreparation_zero width)
  rw [prepared]
  rfl

end

end QuantumAlg.EllipticCurve.FullRange

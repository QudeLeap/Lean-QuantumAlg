/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Selection
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation.Vector

/-!
# Selected uniform source blocks equal the actual H preparation

One fixed mathematical source may contain all exponent coordinates. Its
selected block is uniform; every other source coordinate and every physical
complement or external-reference amplitude remains arbitrary. Feeding this
block into the actual zero bank is exactly its real H preparation, with the
consumed mathematical block zero. No source bank or permutation is executed.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

private abbrev Saved (ports : Ports ctx totalBits active) (Rest Reference : Register) :=
  ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
    (Rest.Index × Reference.Index)

/-- Uniformity only on the selected source block; all other amplitudes remain unrestricted. -/
def selectedUniformSourceInput (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : Saved ports Rest Reference → Complex) :
    HilbertVector (ctx.register.prod (S.prod Reference)) :=
  WithLp.toLp 2 fun row =>
    if (bankCoordinates ports.wires ports.qubits row.1).1 = Partner.zeroBits active then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2,
        ((partition row.2.1).2, row.2.2))
    else 0

/-- The consumed mathematical block is zero and the same real bank has uniform amplitudes. -/
def selectedUniformBankOutput (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : Saved ports Rest Reference → Complex) :
    HilbertVector (ctx.register.prod (S.prod Reference)) :=
  WithLp.toLp 2 fun row =>
    if (partition row.2.1).1 = binaryEquiv active (Partner.zeroBits active) then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2,
        ((partition row.2.1).2, row.2.2))
    else 0

/-- Exact selected-feed vector identity on the entire original source and physical complement. -/
lemma window_selectedSourceFeed_uniform (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : Saved ports Rest Reference → Complex) :
    (selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference).applyVec
        (selectedUniformSourceInput ports partition Reference saved) =
      selectedUniformBankOutput ports partition Reference saved := by
  ext row
  rw [selectedFeedOperator, UnitaryOperator.ofPerm_applyVec]
  change (if (bankCoordinates ports.wires ports.qubits
      (selectedFeedBasis ports partition Reference row).1).1 = Partner.zeroBits active then
    invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits
      (selectedFeedBasis ports partition Reference row).1).2,
        ((partition (selectedFeedBasis ports partition Reference row).2.1).2,
          (selectedFeedBasis ports partition Reference row).2.2)) else 0) = _
  have bank : bankCoordinates ports.wires ports.qubits
      (selectedFeedBasis ports partition Reference row).1 =
        ((binaryEquiv active).symm (partition row.2.1).1,
          (bankCoordinates ports.wires ports.qubits row.1).2) :=
    (bankCoordinates ports.wires ports.qubits).apply_symm_apply _
  have source : partition (selectedFeedBasis ports partition Reference row).2.1 =
      (binaryEquiv active (bankCoordinates ports.wires ports.qubits row.1).1,
        (partition row.2.1).2) := partition.apply_symm_apply _
  rw [bank, source]
  change (if ((binaryEquiv active).symm (partition row.2.1).1) =
      Partner.zeroBits active then
    invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2,
      ((partition row.2.1).2, row.2.2)) else 0) = _
  have same : (binaryEquiv active).symm (partition row.2.1).1 = Partner.zeroBits active ↔
      (partition row.2.1).1 = binaryEquiv active (Partner.zeroBits active) := by
    constructor
    · intro equal
      exact ((binaryEquiv active).apply_symm_apply _).symm.trans
        (congrArg (binaryEquiv active) equal)
    · intro equal
      exact (congrArg (binaryEquiv active).symm equal).trans
        ((binaryEquiv active).symm_apply_apply (Partner.zeroBits active))
  by_cases zero : (partition row.2.1).1 = binaryEquiv active (Partner.zeroBits active)
  · simp only [selectedUniformBankOutput, if_pos zero, if_pos (same.mpr zero)]
  · simp only [selectedUniformBankOutput, if_neg zero,
      if_neg (fun equal => zero (same.mp equal))]

/-- Real H on the same bank equals selected uniform feeding, with all other amplitudes retained. -/
lemma window_preparation_selected_uniform_source (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (saved : Saved ports Rest Reference → Complex) :
    (selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference).applyVec
        (selectedUniformSourceInput ports partition Reference saved) =
      (preparationOperator ports environment (S.prod Reference)).applyVec
        (zeroBankInput ports (S.prod Reference)
          (fun coordinate =>
            if (partition coordinate.2.1).1 = binaryEquiv active (Partner.zeroBits active) then
              saved (coordinate.1, ((partition coordinate.2.1).2, coordinate.2.2)) else 0)) := by
  rw [window_selectedSourceFeed_uniform, window_preparation_zero_vector]
  ext row
  change (if (partition row.2.1).1 = binaryEquiv active (Partner.zeroBits active) then
      invSqrt2 ^ active * saved ((bankCoordinates ports.wires ports.qubits row.1).2,
        ((partition row.2.1).2, row.2.2)) else 0) =
    invSqrt2 ^ active *
      (if (partition row.2.1).1 = binaryEquiv active (Partner.zeroBits active) then
        saved ((bankCoordinates ports.wires ports.qubits row.1).2,
          ((partition row.2.1).2, row.2.2)) else 0)
  rw [mul_ite, mul_zero]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

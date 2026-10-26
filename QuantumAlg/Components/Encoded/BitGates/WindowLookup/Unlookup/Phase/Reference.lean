/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Phase.Restoration
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reset

/-!
# Exact restored unlookup feedback beside arbitrary coherent references

The operator is the actual unary preparation, paid two-half feedback and
native inverse on the supplied existing physical systems. Every coherent
label satisfies its explicit initial zero and clean-prefix promises; its
reference coordinate and complete original quantum label are preserved.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)

/-- Original-address measured character retained by the actual restored paid feedback. -/
def restoredCharacter
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (value : CShape.Value (.bits resultWidth)) (state : Data) : ℂ :=
  if MaskParity.maskValue value
    (table ((frame.high.stack ⟨0, by omega⟩).get state)
      (frame.high.addressLabelAt highRemaining 0 (by omega) 0 (by omega) state)
      (frame.low.prefixLabel lowWidth (Nat.le_refl _) state)) then -1 else 1

/-- The actual restored feedback preserves every external reference label
with its exact character. -/
lemma restorationOperator_reference_ket (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx) (state : Data)
    (zero : ∀ index, (frame.low.target index).get state = false)
    (clean : frame.high.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor (frame.restorationOperator (services := services)
      physical sameWires measured parity table environment store)
        (1 : UnitaryOperator Reference)).applyVec
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires state, reference)).vec =
      frame.restoredCharacter table (store.read measured) state •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires state, reference)).vec := by
  have actual := frame.restorationOperator_applyVec (services := services)
    physical sameWires measured parity table separate environment store state zero clean
  change UnitaryOperator.applyVec _
    (NormalizedVector.ket (R := ctx.register) (measuredEncodedBasis physical sameWires state)).vec =
      frame.restoredCharacter table (store.read measured) state •
        (NormalizedVector.ket (R := ctx.register)
          (measuredEncodedBasis physical sameWires state)).vec at actual
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec]
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

/-- Arbitrary coherent reference families retain the exact measured character without phase loss. -/
lemma restorationOperator_coherent_reference (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (measured : CInputRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (zero : ∀ label index, (frame.low.target index).get (state label) = false)
    (clean : ∀ label, frame.high.CleanFrom 0 (state label))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (UnitaryOperator.prodTensor (frame.restorationOperator (services := services)
      physical sameWires measured parity table environment store)
        (1 : UnitaryOperator Reference)).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec) =
      ∑ index, (amplitude index *
        frame.restoredCharacter table (store.read measured) (state index)) •
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis physical sameWires (state index), reference index)).vec := by
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor (frame.restorationOperator (services := services)
      physical sameWires measured parity table environment store)
        (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference))
          _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := frame.restorationOperator_reference_ket (services := services)
    physical sameWires measured parity table separate environment store (state index)
    (zero index) (clean index) (reference index)
  change HilbertOperator.applyVec _ _ = _ at actual
  rw [actual, smul_smul]

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Uniform
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Preparation.Vector
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.SourceRows

/-!
# Selected mathematical preparation and the actual physical H bank

Preparing one mathematical source block and then feeding it into the real
zero bank equals the real H preparation. The source is an observation-space
coordinate only. Every unselected physical and mathematical coordinate and
every external-reference amplitude is retained, with symbolic block width.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat} {S Rest : Register}

private abbrev PreparationSaved (ports : Ports ctx totalBits active) (Rest Reference : Register) :=
  ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
    (Rest.Index × Reference.Index)

/-- The recursively represented zero tuple has the ordinary zero binary label. -/
lemma window_source_binary_zero (count : Nat) :
    binaryEquiv count (Partner.zeroBits count) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change qftPairEquiv count (0, binaryEquiv count (Partner.zeroBits count)) = 0
      rw [ih]
      apply Fin.ext
      simp only [qftPairEquiv_apply_val, Fin.val_zero, Nat.mul_zero, Nat.zero_add]

/-- Source-only mathematical preparation, with literal identity on all actual physical wires. -/
def referencePreparation (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (Reference : Register) : UnitaryOperator (ctx.register.prod (S.prod Reference)) :=
  UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
    (UnitaryOperator.prodTensor (selectedUniformPreparation partition)
      (1 : UnitaryOperator Reference))

/-- Both the real active bank and the selected mathematical source block start at zero. -/
def selectedZeroInput (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : PreparationSaved ports Rest Reference → Complex) :
    HilbertVector (ctx.register.prod (S.prod Reference)) :=
  zeroBankInput ports (S.prod Reference) (fun coordinate =>
    if (partition coordinate.2.1).1 = 0 then
      saved (coordinate.1, ((partition coordinate.2.1).2, coordinate.2.2)) else 0)

private lemma selectedZeroInput_apply (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : PreparationSaved ports Rest Reference → Complex)
    (row : (ctx.register.prod (S.prod Reference)).Index) :
    selectedZeroInput ports partition Reference saved row =
      if (bankCoordinates ports.wires ports.qubits row.1).1 = Partner.zeroBits active then
        (if (partition row.2.1).1 = 0 then
          saved ((bankCoordinates ports.wires ports.qubits row.1).2,
            ((partition row.2.1).2, row.2.2)) else 0) else 0 := rfl

private lemma selectedZeroInput_ket (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (basis : (ctx.register.prod (S.prod Reference)).Index)
    (physicalZero : (bankCoordinates ports.wires ports.qubits basis.1).1 =
      Partner.zeroBits active)
    (sourceZero : (partition basis.2.1).1 = 0) :
    selectedZeroInput ports partition Reference
        (fun coordinate => if coordinate =
          ((bankCoordinates ports.wires ports.qubits basis.1).2,
            ((partition basis.2.1).2, basis.2.2)) then 1 else 0) =
      (NormalizedVector.ket basis : HilbertVector (ctx.register.prod (S.prod Reference))) := by
  ext row
  rw [selectedZeroInput_apply, NormalizedVector.ket_apply]
  by_cases same : row = basis
  · subst row
    simp only [physicalZero, sourceZero, if_true]
  · rw [if_neg same]
    by_cases bank : (bankCoordinates ports.wires ports.qubits row.1).1 =
        Partner.zeroBits active
    · rw [if_pos bank]
      by_cases source : (partition row.2.1).1 = 0
      · rw [if_pos source]
        apply if_neg
        intro saved
        apply same
        apply Prod.ext
        · apply (bankCoordinates ports.wires ports.qubits).injective
          exact Prod.ext (bank.trans physicalZero.symm) (congrArg Prod.fst saved)
        · apply Prod.ext
          · apply partition.injective
            exact Prod.ext (source.trans sourceZero.symm)
              (congrArg (fun value => value.2.1) saved)
          · exact congrArg (fun value => value.2.2) saved
      · rw [if_neg source]
    · rw [if_neg bank]

private lemma referencePreparation_entry
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (row column : (ctx.register.prod (S.prod Reference)).Index) :
    referencePreparation (ctx := ctx) partition Reference row column =
      (if row.1 = column.1 then (1 : Complex) else 0) *
        ((uniformPreparation active (partition row.2.1).1 (partition column.2.1).1 *
          (if (partition row.2.1).2 = (partition column.2.1).2 then 1 else 0)) *
            (if row.2.2 = column.2.2 then 1 else 0)) := by
  rw [referencePreparation, UnitaryOperator.prodTensor_apply,
    UnitaryOperator.prodTensor_apply, window_source_selectedPreparation_entry]
  rfl

/-- Source-only H creates exactly the selected uniform input with arbitrary saved amplitudes. -/
lemma window_source_referencePreparation_zero (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (saved : PreparationSaved ports Rest Reference → Complex) :
    (referencePreparation (ctx := ctx) partition Reference).applyVec
        (selectedZeroInput ports partition Reference saved) =
      selectedUniformSourceInput ports partition Reference saved := by
  ext row
  rw [UnitaryOperator.applyVec_apply]
  let target : (ctx.register.prod (S.prod Reference)).Index :=
    (row.1, (partition.symm (0, (partition row.2.1).2), row.2.2))
  have targetSource : partition target.2.1 = (0, (partition row.2.1).2) :=
    partition.apply_symm_apply _
  calc
    _ = referencePreparation (ctx := ctx) partition Reference row target *
        selectedZeroInput ports partition Reference saved target := by
      apply Finset.sum_eq_single target
      · intro column _ different
        rw [referencePreparation_entry]
        by_cases physical : row.1 = column.1
        · by_cases remainder : (partition row.2.1).2 = (partition column.2.1).2
          · by_cases reference : row.2.2 = column.2.2
            · by_cases zero : (partition column.2.1).1 = 0
              · exfalso
                apply different
                apply Prod.ext
                · exact physical.symm
                · apply Prod.ext
                  · apply partition.injective
                    have paired : partition column.2.1 = (0, (partition row.2.1).2) :=
                      Prod.ext zero remainder.symm
                    exact paired.trans targetSource.symm
                  · exact reference.symm
              · rw [selectedZeroInput_apply]
                by_cases bank : (bankCoordinates ports.wires ports.qubits column.1).1 =
                    Partner.zeroBits active
                · rw [if_pos bank, if_neg zero, mul_zero]
                · rw [if_neg bank, mul_zero]
            · simp only [if_neg reference, mul_zero, zero_mul]
          · simp only [if_neg remainder, mul_zero, zero_mul]
        · simp only [if_neg physical, zero_mul]
      · simp
    _ = _ := by
      rw [referencePreparation_entry, targetSource,
        window_source_uniformPreparation_zero_column]
      change (if row.1 = row.1 then (1 : Complex) else 0) *
          ((invSqrt2 ^ active *
            (if (partition row.2.1).2 = (partition row.2.1).2 then 1 else 0)) *
              (if row.2.2 = row.2.2 then 1 else 0)) *
          (if (bankCoordinates ports.wires ports.qubits row.1).1 =
              Partner.zeroBits active then
            (if (partition target.2.1).1 = 0 then
              saved ((bankCoordinates ports.wires ports.qubits row.1).2,
                ((partition target.2.1).2, row.2.2)) else 0) else 0) = _
      rw [targetSource]
      simp only [if_true, one_mul, mul_one]
      change invSqrt2 ^ active *
          (if (bankCoordinates ports.wires ports.qubits row.1).1 =
              Partner.zeroBits active then
            saved ((bankCoordinates ports.wires ports.qubits row.1).2,
              ((partition row.2.1).2, row.2.2)) else 0) = _
      rw [mul_ite, mul_zero]
      rfl

/-- Feeding a prepared mathematical block equals real native H on the same zero-bank input. -/
lemma window_source_prepared_feed_equals_actual (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (saved : PreparationSaved ports Rest Reference → Complex) :
    (selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference).applyVec
        ((referencePreparation (ctx := ctx) partition Reference).applyVec
          (selectedZeroInput ports partition Reference saved)) =
      (preparationOperator ports environment (S.prod Reference)).applyVec
        (selectedZeroInput ports partition Reference saved) := by
  rw [window_source_referencePreparation_zero,
    window_preparation_selected_uniform_source]
  congr 1
  simp only [selectedZeroInput, window_source_binary_zero]

/-- The actual H and mathematical feed constructions have identical supported basis columns. -/
lemma window_source_prepared_feed_column (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (basis : (ctx.register.prod (S.prod Reference)).Index)
    (physicalZero : (bankCoordinates ports.wires ports.qubits basis.1).1 =
      Partner.zeroBits active)
    (sourceZero : (partition basis.2.1).1 = 0) :
    (selectedFeedOperator (S := S) (Rest := Rest) ports partition Reference).applyVec
        ((referencePreparation (ctx := ctx) partition Reference).applyVec
          (NormalizedVector.ket basis : HilbertVector (ctx.register.prod (S.prod Reference)))) =
      (preparationOperator ports environment (S.prod Reference)).applyVec
        (NormalizedVector.ket basis : HilbertVector (ctx.register.prod (S.prod Reference))) := by
  have actual := window_source_prepared_feed_equals_actual ports partition environment Reference
    (fun coordinate => if coordinate =
      ((bankCoordinates ports.wires ports.qubits basis.1).2,
        ((partition basis.2.1).2, basis.2.2)) then 1 else 0)
  rw [selectedZeroInput_ket ports partition Reference basis physicalZero sourceZero] at actual
  exact actual

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

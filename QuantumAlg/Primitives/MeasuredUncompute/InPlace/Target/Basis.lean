/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Target
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Values

/-!
# Independent target action at the original fixed frame

These are exact mathematical basis equations for the independent target.
The fixed preparation assembly identifies A=0 and the complete initial
auxiliary state beside both old words. Every reference label survives the
unitary permutation unchanged [LYL+26, sec_point_add/sec_point_add.tex:24-36,45-79].

The frame identity uses only the prescribed preparation and its actual
wire equivalence. It does not use any EEA run, native product action or
computed saved value, including in the target's finite padding extension.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceTarget

noncomputable section

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Tensoring the independent target with identity preserves each complete reference label. -/
theorem reference_ket (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (value : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size))
    {Reference : Register} (reference : Reference.Index) :
    (jointOperator operation modulus prime Reference).applyVec
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        (frameEquiv modulus.size (fresh, value), reference)).vec =
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        (frameEquiv modulus.size (fresh, words operation modulus prime value), reference)).vec := by
  ext ⟨row, other⟩
  have column : (operator operation modulus prime) row
      (frameEquiv modulus.size (fresh, value)) =
      (NormalizedVector.ket (R := (NumeratorMeasurement.context modulus.size).register)
        (frameEquiv modulus.size (fresh, words operation modulus prime value))) row := by
    have action := congrArg
      (fun vector : HilbertVector (NumeratorMeasurement.context modulus.size).register =>
        vector row) (operator_ket operation modulus prime fresh value)
    exact (HilbertOperator.applyVec_ket
      (operator operation modulus prime :
        HilbertOperator (NumeratorMeasurement.context modulus.size).register)
      (frameEquiv modulus.size (fresh, value)) row).symm.trans action
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor (operator operation modulus prime) (1 : UnitaryOperator Reference) :
      HilbertOperator
        (Register.prod (NumeratorMeasurement.context modulus.size).register Reference))
    (NormalizedVector.ket
      (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
      (frameEquiv modulus.size (fresh, value), reference)).vec (row, other) = _
  rw [HilbertOperator.applyVec_ket, UnitaryOperator.prodTensor_apply, column]
  change (NormalizedVector.ket (R := (NumeratorMeasurement.context modulus.size).register)
      (frameEquiv modulus.size (fresh, words operation modulus prime value))) row *
      (if other = reference then 1 else 0) =
    (NormalizedVector.ket
      (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
      (frameEquiv modulus.size (fresh, words operation modulus prime value), reference))
        (row, other)
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  have joint :
      ((row, other) :
        (Register.prod (NumeratorMeasurement.context modulus.size).register Reference).Index) =
      (frameEquiv modulus.size (fresh, words operation modulus prime value), reference) ↔
      row = frameEquiv modulus.size (fresh, words operation modulus prime value) ∧
        other = reference := by
    constructor
    · intro same
      exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · intro same
      exact Prod.ext same.1 same.2
  simp only [joint]
  by_cases same : row = frameEquiv modulus.size (fresh, words operation modulus prime value) <;>
    by_cases refSame : other = reference <;> simp [same, refSame]

/-- The physically assembled, fixed A=0 initial basis for two arbitrary original words. -/
def preparedBasis (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    (NumeratorMeasurement.context modulus.size).register.Index :=
  frameEquiv modulus.size ((InPlacePreparation.preparation modulus).value, (value, numerator))

/-- Actual basis coordinates identify precisely the full fixed source frame and the old Y word. -/
theorem preparedBasis_frame (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    NumeratorMeasurement.frameBasis modulus.size (preparedBasis modulus value numerator) =
      (OutputCopy.encoding modulus.size).encode
        (InitialPortProgram.inputFrame modulus value, numerator) := by
  have retained :
      (MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size).symm
        (preparedBasis modulus value numerator) =
      assembly modulus.size ((InPlacePreparation.preparation modulus).value,
        (inputBasisEquiv modulus.size).symm (value, numerator)) :=
    (MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size).symm_apply_apply _
  have assembled := InPlacePreparation.prepared_input modulus
    ((inputBasisEquiv modulus.size).symm (value, numerator))
  simp only [Equiv.apply_symm_apply] at assembled
  change InverseAssembly.basisEquiv modulus.size
    ((MeasurementCells.basisEquiv (after modulus.size) 2 modulus.size).symm
      (preparedBasis modulus value numerator)) = _
  exact (congrArg (InverseAssembly.basisEquiv modulus.size) retained).trans assembled

/-- The fixed preparation label equals the original complete frame at its real runtime wires. -/
theorem preparedBasis_eq_native (modulus : Nat) (value numerator : Fin (2 ^ modulus.size)) :
    preparedBasis modulus value numerator =
      (NumeratorMeasurement.frameBasis modulus.size).symm
        ((OutputCopy.encoding modulus.size).encode
          (InitialPortProgram.inputFrame modulus value, numerator)) := by
  apply (NumeratorMeasurement.frameBasis modulus.size).injective
  exact (preparedBasis_frame modulus value numerator).trans
    ((NumeratorMeasurement.frameBasis modulus.size).apply_symm_apply _).symm

/-- The independent target preserves the full fixed auxiliary state and X beside arbitrary Ref. -/
theorem prepared_operator_ket (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size)) {Reference : Register}
    (reference : Reference.Index) :
    (jointOperator operation modulus prime Reference).applyVec
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        (preparedBasis modulus value numerator, reference)).vec =
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        (preparedBasis modulus value (resultWord operation modulus prime value numerator),
          reference)).vec := by
  have actual := reference_ket operation modulus prime
    (InPlacePreparation.preparation modulus).value (value, numerator) reference
  have labels := congrArg
    (fun pair : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size) =>
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        (frameEquiv modulus.size ((InPlacePreparation.preparation modulus).value, pair),
          reference)).vec) (words_pair operation modulus prime value numerator)
  exact actual.trans labels

/-- In original-frame coordinates, the target has exactly the independent canonical output word. -/
theorem initialFrame_operator_ket (operation : Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (value numerator : Fin (2 ^ modulus.size))
    {Reference : Register} (reference : Reference.Index) :
    (jointOperator operation modulus prime Reference).applyVec
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        ((NumeratorMeasurement.frameBasis modulus.size).symm
          ((OutputCopy.encoding modulus.size).encode
            (InitialPortProgram.inputFrame modulus value, numerator)), reference)).vec =
      (NormalizedVector.ket
        (R := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
        ((NumeratorMeasurement.frameBasis modulus.size).symm
          ((OutputCopy.encoding modulus.size).encode
            (InitialPortProgram.inputFrame modulus value,
              resultWord operation modulus prime value numerator)), reference)).vec := by
  simpa only [preparedBasis_eq_native] using
    prepared_operator_ket operation modulus prime value numerator reference

end

end QuantumAlg.MeasuredUncompute.InPlaceTarget

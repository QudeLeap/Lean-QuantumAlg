/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.PrimeWordProduct
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Measurement
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Independent complete-state targets for in-place modular arithmetic

The mathematical two-word permutations prescribe (X,Y) -> (X,XY) and
(X,Y) -> (X,Y/X) on 0<X<p and Y<p. Their padding extension is identity,
with no implementation promise beyond that original domain
[LYL+26, sec_point_add/sec_point_add.tex:24-36].

The actual wire assembly places this independent old-word permutation
beside every auxiliary basis value. The prescribed fixed A=0 preparation
is tensored with the entire incoming quantum-reference state. The final
coordinate change follows only the retained classical cells, and the
mathematical operator preserves the complete external reference.

No target expression uses a circuit execution, a native arithmetic
product, a computed EEA result or a measured outcome. Actual saved-word
agreement belongs to separate semantic proofs. Auxiliary and reference
coherences are retained in the complete target density matrix.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceTarget

noncomputable section

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The two independently specified in-place arithmetic operations. -/
inductive Operation where
  | multiplication
  | division

/-- The original modulus fits its mathematical word without any execution assumption. -/
def modulusWord (modulus : Nat) : Fin (2 ^ modulus.size + 1) :=
  ⟨modulus, (Nat.lt_size_self modulus).trans (Nat.lt_succ_self _)⟩

/-- Independent total arithmetic on the two original finite words. -/
def words (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    Equiv.Perm (Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) :=
  match operation with
  | .multiplication => Nat.FixedWidth.PrimeWordProduct.multiplication (modulusWord modulus) prime
  | .division => Nat.FixedWidth.PrimeWordProduct.division (modulusWord modulus) prime

/-- The complete original first word is fixed, including all non-domain labels. -/
theorem words_first (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) :
    (words operation modulus prime value).1 = value.1 := by
  cases operation <;> rfl

/-- The target word is defined by independent finite modular arithmetic alone. -/
def resultWord (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  (words operation modulus prime (value, numerator)).2

/-- The target fixes X and writes only the independently prescribed second word. -/
theorem words_pair (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size)) :
    words operation modulus prime (value, numerator) =
      (value, resultWord operation modulus prime value numerator) :=
  Prod.ext (words_first operation modulus prime (value, numerator)) rfl

/-- Multiplication's original-domain word has the canonical X*Y modulo p value. -/
theorem multiplication_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (resultWord .multiplication modulus prime value numerator).val =
      (value.val * numerator.val) % modulus :=
  Nat.FixedWidth.PrimeWordProduct.multiplication_value (modulusWord modulus) prime
    value numerator positive bounded numeratorBound

/-- Division's original-domain word has the canonical inverse-X times Y modulo p value. -/
theorem division_value (modulus : Nat) (prime : Nat.Prime modulus)
    (value numerator : Fin (2 ^ modulus.size))
    (positive : 0 < value.val) (bounded : value.val < modulus)
    (numeratorBound : numerator.val < modulus) :
    (resultWord .division modulus prime value numerator).val =
      (((value.val : ZMod modulus)⁻¹).val * numerator.val) % modulus :=
  Nat.FixedWidth.PrimeWordProduct.division_value (modulusWord modulus) prime
    value numerator positive bounded numeratorBound

/-- Real preparation and retained-cell coordinates, parameterized by the original two words. -/
def frameEquiv (width : Nat) :
    ((InputPreparation.auxiliaryLayout width).register.Index ×
      (Fin (2 ^ width) × Fin (2 ^ width))) ≃
        (NumeratorMeasurement.context width).register.Index :=
  (Equiv.prodCongr (Equiv.refl _) (inputBasisEquiv width).symm).trans
    ((assembly width).trans (MeasurementCells.basisEquiv (after width) 2 width))

/-- Each mathematical coordinate is its explicit physical auxiliary/old-input assembly. -/
theorem frameEquiv_apply (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (value : Fin (2 ^ width) × Fin (2 ^ width)) :
    frameEquiv width (fresh, value) =
      MeasurementCells.basisEquiv (after width) 2 width
        (assembly width (fresh, (inputBasisEquiv width).symm value)) := rfl

/-- Extend only the independent two-word permutation, retaining every auxiliary basis value. -/
def permutation (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    Equiv.Perm (NumeratorMeasurement.context modulus.size).register.Index :=
  (frameEquiv modulus.size).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (words operation modulus prime)).trans
      (frameEquiv modulus.size))

/-- Every auxiliary coordinate survives the independent full-state target exactly. -/
theorem permutation_frame (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (value : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) :
    permutation operation modulus prime (frameEquiv modulus.size (fresh, value)) =
      frameEquiv modulus.size (fresh, words operation modulus prime value) := by
  let update : ((InputPreparation.auxiliaryLayout modulus.size).register.Index ×
      (Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size))) →
      (NumeratorMeasurement.context modulus.size).register.Index :=
    fun pair => frameEquiv modulus.size (pair.1, words operation modulus prime pair.2)
  change update ((frameEquiv modulus.size).symm
    (frameEquiv modulus.size (fresh, value))) = update (fresh, value)
  exact congrArg update ((frameEquiv modulus.size).symm_apply_apply (fresh, value))

/-- The independent mathematical unitary has no native placement, trace or cost metadata. -/
def operator (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryOperator (NumeratorMeasurement.context modulus.size).register :=
  UnitaryOperator.ofPerm (permutation operation modulus prime).symm

/-- Exact basis action of the independent target, including all auxiliary coordinates. -/
theorem operator_ket (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (fresh : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (value : Fin (2 ^ modulus.size) × Fin (2 ^ modulus.size)) :
    (operator operation modulus prime).applyVec
      (NormalizedVector.ket (R := (NumeratorMeasurement.context modulus.size).register)
        (frameEquiv modulus.size (fresh, value))).vec =
      (NormalizedVector.ket (R := (NumeratorMeasurement.context modulus.size).register)
        (frameEquiv modulus.size (fresh, words operation modulus prime value))).vec := by
  have actual := UnitaryOperator.ofPerm_applyVec_ket
    (R := (NumeratorMeasurement.context modulus.size).register)
    (permutation operation modulus prime).symm (frameEquiv modulus.size (fresh, value))
  exact actual.trans (congrArg
    (fun label => (NormalizedVector.ket
      (R := (NumeratorMeasurement.context modulus.size).register) label).vec)
    (permutation_frame operation modulus prime fresh value))

/-- Independent arithmetic on the complete live context beside an untouched reference. -/
def jointOperator (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) :
    UnitaryOperator
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference) :=
  UnitaryOperator.prodTensor (operator operation modulus prime) (1 : UnitaryOperator Reference)

/-- Prescribed A=0/fixed auxiliary preparation, followed by the actual classical-cell reindexing. -/
def inputDensity (modulus : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    DensityOperator
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference) :=
  DensityOperator.reindex
    (R := Register.prod (after modulus.size).register Reference)
    (S := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
    (preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
      (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
      (InPlacePreparation.preparation modulus).normalized Reference input)
    (MeasurementCells.jointBasisEquiv (after modulus.size) 2 modulus.size Reference)

/-- Neither the fixed tensor nor the retained-cell coordinate map loses any incoming mass. -/
theorem inputDensity_mass (modulus : Nat) (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    (inputDensity modulus Reference input).mass = input.mass := by
  have reindexed := DensityOperator.reindex_mass
    (R := Register.prod (after modulus.size).register Reference)
    (S := Register.prod (NumeratorMeasurement.context modulus.size).register Reference)
    (show DensityOperator (Register.prod (after modulus.size).register Reference) from
      preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
        (InPlacePreparation.preparation modulus).normalized Reference input)
    (MeasurementCells.jointBasisEquiv (after modulus.size) 2 modulus.size Reference)
  exact reindexed.trans (preparedDensity_mass auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (InPlacePreparation.preparation modulus).normalized
    Reference input)

/-- Independent complete quantum-reference target for every original joint density. -/
def density (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    DensityOperator
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference) :=
  DensityOperator.applyUnitary (jointOperator operation modulus prime Reference)
    (inputDensity modulus Reference input)

/-- The complete target retains the original density mass, including subnormalized blocks. -/
theorem density_mass (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register)
    (input : DensityOperator (Register.prod (before modulus.size).register Reference)) :
    (density operation modulus prime Reference input).mass = input.mass :=
  (DensityOperator.applyUnitary_mass (jointOperator operation modulus prime Reference)
    (inputDensity modulus Reference input)).trans (inputDensity_mass modulus Reference input)

/-- Certified normalized inputs give normalized full-reference mathematical targets. -/
theorem density_normalized (operation : Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (Reference : Register) (input : Input (before modulus.size) Reference) :
    (density operation modulus prime Reference input.state.quantumMarginal).IsNormalized := by
  change (density operation modulus prime Reference input.state.quantumMarginal).mass = 1
  exact (density_mass operation modulus prime Reference input.state.quantumMarginal).trans
    ((ExecutionState.quantumMarginal_mass input.state).trans input.normalized)

end

end QuantumAlg.MeasuredUncompute.InPlaceTarget

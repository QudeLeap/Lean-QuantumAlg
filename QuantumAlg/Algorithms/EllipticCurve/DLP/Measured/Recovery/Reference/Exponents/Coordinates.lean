/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Coordinates
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory.Branch
import all QuantumAlg.Core.Execution.Context.Union.Preparation.Basis
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Shared full-bank and paired-word coordinates

These equivalences regroup the arithmetic workspace, selector, paired words
and arbitrary Reference. They apply to every auxiliary basis label and do
not prescribe a prepared state or modify classical stores and histories.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Exponents

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open ContextUnion
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement ScalarMultiplication.MeasuredPlacement.Allocation
open MAU.Inversion.SharedEEA
open ECDLP.Measured
open Recovery.Reference.Measured.CommonBank

private lemma regrouped_product_apply {Auxiliary Words Original Prepared Retained : Type}
    (input : Words ≃ Original) (assembly : Auxiliary × Original ≃ Prepared)
    (cells : Prepared ≃ Retained) (auxiliary : Auxiliary) (words : Words) :
    (((Equiv.refl Auxiliary).prodCongr input).trans (assembly.trans cells))
        (auxiliary, words) = cells (assembly (auxiliary, input words)) := rfl

local instance {α : Type} : DecidableEq α := Classical.decEq α

abbrev Pair (m : Nat) := Fin (2 ^ m) × Fin (2 ^ m)

/-- The original auxiliary and two input-word factors are the full actual Numerator basis. -/
def arithmeticBasis (width : Nat) :
    ((InputPreparation.auxiliaryLayout width).register.Index ×
      (Fin (2 ^ width) × Fin (2 ^ width))) ≃ (NumeratorMeasurement.context width).register.Index :=
  ((Equiv.refl (InputPreparation.auxiliaryLayout width).register.Index).prodCongr
    (InversePreparation.inputBasisEquiv width).symm).trans
      ((InversePreparation.assembly width).trans
        (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width))

private lemma arithmeticBasis_apply (width : Nat)
    (auxiliary : (InputPreparation.auxiliaryLayout width).register.Index)
    (x y : Fin (2 ^ width)) :
    arithmeticBasis width (auxiliary, (x, y)) =
      (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width)
        (InversePreparation.assembly width
          (auxiliary, (InversePreparation.inputBasisEquiv width).symm (x, y))) := by
  unfold arithmeticBasis
  exact regrouped_product_apply
    (Auxiliary := (InputPreparation.auxiliaryLayout width).register.Index)
    (Words := Fin (2 ^ width) × Fin (2 ^ width))
    (Original := (InversePreparation.before width).register.Index)
    (Prepared := (InversePreparation.after width).register.Index)
    (Retained := (NumeratorMeasurement.context width).register.Index)
    (InversePreparation.inputBasisEquiv width).symm (InversePreparation.assembly width)
    (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width) auxiliary (x, y)

/-- The one actual selector wire has exactly the original Fin 2 basis. -/
def selectorBasis (width count : Nat) : (indexedLayout width count).register.Index ≃ Fin 2 where
  toFun selector := selector 0
  invFun bit _ := bit
  left_inv selector := by funext index; fin_cases index; rfl
  right_inv _ := rfl

/-- Complete assembly factors are only regrouped into the original dirty bank and Reference. -/
def bankAssembly (width count : Nat) (Reference : Register) :
    ((indexedLayout width count).register.Index ×
      ((InputPreparation.auxiliaryLayout width).register.Index ×
        ((Fin (2 ^ width) × Fin (2 ^ width)) × Reference.Index))) ≃ Bank width Reference where
  toFun value := (arithmeticBasis width (value.2.1, value.2.2.1),
    (selectorBasis width count value.1, value.2.2.2))
  invFun value := ((selectorBasis width count).symm value.2.1,
    ((arithmeticBasis width).symm value.1).1,
    ((arithmeticBasis width).symm value.1).2, value.2.2)
  left_inv := by
    rintro ⟨selector, auxiliary, words, reference⟩
    dsimp only
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨arithmetic, selector, reference⟩
    dsimp only
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- The production paired exponent basis, expressed as the original physical exponent function. -/
def pairBasis (modulus m : Nat) : Pair m ≃ Exponents (2 * m) :=
  (pairedExponentEquiv modulus m).trans (rangeBasis modulus.size (2 * m))

lemma pairBasis_apply (modulus m : Nat) (pair : Pair m) :
    pairBasis modulus m pair =
      rangeBasis modulus.size (2 * m) (pairedExponentInput modulus m pair) := by
  rw [pairBasis, Equiv.trans_apply, pairedExponentEquiv_apply]

end

end Exponents
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference

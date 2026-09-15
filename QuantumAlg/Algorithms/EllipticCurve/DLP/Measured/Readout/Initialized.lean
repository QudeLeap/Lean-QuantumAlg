/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Target

/-!
# Original exponent operators on the actual initialized scalar subspace

The allocated exponent operator retains the actual prepared selector and
auxiliary factors, every coordinate word, and the complete reference. Its
action on any coherently initialized input is exactly initialization of the
same original input-coordinate operator. This is a complete complex-vector
identity, with no basis probability approximation or additional gate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open GenericPointAddition.InPlace

/-- Actual allocated matrix columns retain both fixed preparation factors and the full reference. -/
theorem afterExponentOperator_initializedAssembly_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register)
    (selector : (indexedLayout modulus.size (2 * exponentWidth)).register.Index)
    (auxiliary : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (row column : (Register.prod
      (before modulus.size (2 * exponentWidth)).register Reference).Index) :
    (UnitaryOperator.prodTensor
      (afterExponentProgram modulus exponentWidth program physical).matrix
      (1 : UnitaryOperator Reference))
        (initializedJointAssembly modulus (2 * exponentWidth) Reference (selector, auxiliary, row))
        (initializedOutputEmbedding modulus (2 * exponentWidth) Reference column) =
      (if selector = (BasisPreparation.zero
        (indexedLayout modulus.size (2 * exponentWidth))).value then 1 else 0) *
        ((if auxiliary = (InPlacePreparation.preparation modulus).value then 1 else 0) *
          (beforeExponentOperator modulus exponentWidth program physical Reference)
            row column) := by
  change (afterExponentProgram modulus exponentWidth program physical).matrix
      (initializedAssembly modulus (2 * exponentWidth) (selector, auxiliary, row.1))
      (initializedAssembly modulus (2 * exponentWidth)
        ((BasisPreparation.zero (indexedLayout modulus.size (2 * exponentWidth))).value,
          (InPlacePreparation.preparation modulus).value, column.1)) *
      (if row.2 = column.2 then 1 else 0) = _
  rw [afterExponentProgram_assembly_entry]
  change _ = (if selector = (BasisPreparation.zero
      (indexedLayout modulus.size (2 * exponentWidth))).value then (1 : ℂ) else 0) *
    ((if auxiliary = (InPlacePreparation.preparation modulus).value then 1 else 0) *
      ((beforeExponentProgram modulus exponentWidth program physical).matrix row.1 column.1 *
        (if row.2 = column.2 then 1 else 0)))
  ring

/-- On the actual initialized subspace the complete original input matrix is unchanged. -/
theorem afterExponentOperator_initialized_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register)
    (row column : (Register.prod
      (before modulus.size (2 * exponentWidth)).register Reference).Index) :
    (UnitaryOperator.prodTensor
      (afterExponentProgram modulus exponentWidth program physical).matrix
      (1 : UnitaryOperator Reference))
        (initializedOutputEmbedding modulus (2 * exponentWidth) Reference row)
        (initializedOutputEmbedding modulus (2 * exponentWidth) Reference column) =
      (beforeExponentOperator modulus exponentWidth program physical Reference) row column := by
  simpa only [initializedOutputEmbedding, ite_true, one_mul] using
    afterExponentOperator_initializedAssembly_entry modulus exponentWidth program physical Reference
      (BasisPreparation.zero (indexedLayout modulus.size (2 * exponentWidth))).value
      (InPlacePreparation.preparation modulus).value row column

/-- The original exponent operator commutes with actual initialization on every coherent vector. -/
theorem afterExponentOperator_initializedVector (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register)
    (vector : HilbertVector
      (Register.prod (before modulus.size (2 * exponentWidth)).register Reference)) :
    (UnitaryOperator.prodTensor
      (afterExponentProgram modulus exponentWidth program physical).matrix
      (1 : UnitaryOperator Reference)).applyVec
        (Effect.extensionVector
          (initializedOutputEmbedding modulus (2 * exponentWidth) Reference) vector) =
      Effect.extensionVector (initializedOutputEmbedding modulus (2 * exponentWidth) Reference)
        ((beforeExponentOperator modulus exponentWidth program physical Reference).applyVec
          vector) := by
  classical
  ext output
  obtain ⟨⟨selector, auxiliary, original⟩, rfl⟩ :=
    (initializedJointAssembly modulus (2 * exponentWidth) Reference).surjective output
  rw [initializedOutputVector_entry]
  change HilbertOperator.applyVec _ (Effect.extensionVector _ vector) _ = _
  rw [Effect.extensionVector, HilbertOperator.applyVec_sum]
  simp only [HilbertOperator.applyVec_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, HilbertOperator.applyVec_ket, afterExponentOperator_initializedAssembly_entry]
  rw [UnitaryOperator.applyVec_apply]
  simp only [BasisPreparation.normalized, NormalizedVector.ket_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _
  ring

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

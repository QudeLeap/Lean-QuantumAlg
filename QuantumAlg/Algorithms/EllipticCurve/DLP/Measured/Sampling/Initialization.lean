/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout.Initialized
import all QuantumAlg.Core.Execution.Context.Union.Preparation.State
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution

/-!
# Original exponent action through actual workspace initialization

The original exponent operator preserves both fixed fresh factors in every
complete input density, including arbitrary external-reference coherences.
The tensor identity below is the matrix part of the actual initialization
exchange; it makes no claim that marginal equality alone determines a full
classical-quantum execution state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open GenericPointAddition.InPlace
open scoped Kronecker

private theorem prependPrepared_applyUnitary {R S : Register}
    (operator : UnitaryOperator R) (input : DensityOperator R)
    (prepared : NormalizedVector S) :
    DensityOperator.applyUnitary (UnitaryOperator.prodTensor (1 : UnitaryOperator S) operator)
        (prependPrepared input prepared) =
      prependPrepared (DensityOperator.applyUnitary operator input) prepared := by
  apply DensityOperator.ext
  change ((1 : HilbertOperator S) ⊗ₖ (operator : HilbertOperator R)) *
      ((DensityOperator.ofPure prepared).matrix ⊗ₖ input.matrix) *
      ((1 : HilbertOperator S) ⊗ₖ (operator : HilbertOperator R)).conjTranspose =
    (DensityOperator.ofPure prepared).matrix ⊗ₖ
      ((operator : HilbertOperator R) * input.matrix *
        (operator : HilbertOperator R).conjTranspose)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

private theorem afterExponentOperator_assembly (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register) :
    UnitaryOperator.prodTensor
        (afterExponentProgram modulus exponentWidth program physical).matrix
        (1 : UnitaryOperator Reference) =
      UnitaryOperator.reindex (initializedJointAssembly modulus (2 * exponentWidth) Reference)
        (UnitaryOperator.prodTensor
          (1 : UnitaryOperator (indexedLayout modulus.size (2 * exponentWidth)).register)
          (UnitaryOperator.prodTensor
            (1 : UnitaryOperator (InputPreparation.auxiliaryLayout modulus.size).register)
            (beforeExponentOperator modulus exponentWidth program physical Reference))) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨selectorRow, auxiliaryRow, originalRow⟩, rfl⟩ :=
    (initializedJointAssembly modulus (2 * exponentWidth) Reference).surjective row
  obtain ⟨⟨selectorColumn, auxiliaryColumn, originalColumn⟩, rfl⟩ :=
    (initializedJointAssembly modulus (2 * exponentWidth) Reference).surjective column
  change (afterExponentProgram modulus exponentWidth program physical).matrix
      (initializedAssembly modulus (2 * exponentWidth)
        (selectorRow, auxiliaryRow, originalRow.1))
      (initializedAssembly modulus (2 * exponentWidth)
        (selectorColumn, auxiliaryColumn, originalColumn.1)) *
        (if originalRow.2 = originalColumn.2 then 1 else 0) = _
  rw [afterExponentProgram_assembly_entry]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply,
    UnitaryOperator.prodTensor_apply, beforeExponentOperator,
    Matrix.UnitaryGroup.one_apply, Matrix.one_apply]
  ring

/-- Both fixed preparations commute with the exact original full-reference exponent density. -/
theorem afterExponentOperator_initializedDensity (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (Reference : Register)
    (input : DensityOperator
      (Register.prod (before modulus.size (2 * exponentWidth)).register Reference)) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program physical).matrix
          (1 : UnitaryOperator Reference))
        (initializedDensity modulus (2 * exponentWidth) Reference input) =
      initializedDensity modulus (2 * exponentWidth) Reference
        (DensityOperator.applyUnitary
          (beforeExponentOperator modulus exponentWidth program physical Reference) input) := by
  rw [afterExponentOperator_assembly, initializedDensity,
    ← DensityOperator.applyUnitary_reindex, prependPrepared_applyUnitary,
    prependPrepared_applyUnitary]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

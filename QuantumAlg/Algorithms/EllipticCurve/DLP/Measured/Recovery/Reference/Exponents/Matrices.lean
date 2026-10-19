/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Exponents.Coordinates
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Exponents
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Primitives.QFT.Mathematics

/-!
# Paired range-preparation amplitudes and inverse Fourier coefficients

The exact two-range amplitudes include every padded zero label. The inverse
Fourier coefficients retain their negative-frequency sign and first/second
pair order independently of a physical allocation or readout context.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Exponents

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement ScalarMultiplication.MeasuredPlacement.Allocation
open MAU.Inversion.SharedEEA
open ECDLP.Measured FiniteCyclicDLP ConcreteCircuitAccess
open Recovery.Reference.Measured.CommonBank
open scoped BigOperators

universe u
variable {G : Type u} [Group G]

/-- The paired range preparations have their exact complex amplitudes. -/
def preparationAmplitude (problem : KnownOrderProblem G) (pair : Pair (orderWidth problem)) : ℂ :=
  OrderPreparation.state problem pair.1 * OrderPreparation.state problem pair.2

/-- Both ranges use the known order, including every zero-amplitude padded label. -/
lemma preparationAmplitude_apply (problem : KnownOrderProblem G)
    (pair : Pair (orderWidth problem)) :
    preparationAmplitude problem pair =
      (if pair.1.val < problem.order then OrderPreparation.invSqrtOrder problem.order else 0) *
      (if pair.2.val < problem.order then OrderPreparation.invSqrtOrder problem.order else 0) := by
  simp only [preparationAmplitude, OrderPreparation.state_apply]

lemma preparation_zero_column (problem : KnownOrderProblem G) (pair : Pair (orderWidth problem)) :
    ((exponentPreparationCircuit problem).binaryMatrix OracleModel.emptyInterpretation) (prodEquiv
      pair)
      (prodEquiv ((0, 0) : Pair (orderWidth problem))) = preparationAmplitude problem pair := by
  have prepared := congrArg
    (fun state : NormalizedVector (Qubits (orderWidth problem + orderWidth problem)) =>
      state (prodEquiv pair)) (exponentPreparationCircuit_apply_zero (environment :=
        OracleModel.emptyInterpretation)
        problem)
  change ((exponentPreparationCircuit problem).binaryMatrix
    OracleModel.emptyInterpretation).applyVec
    (NormalizedVector.ket (R := Qubits (orderWidth problem + orderWidth problem)) 0).vec
      (prodEquiv pair) = _ at prepared
  simp only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.tensor_apply, Equiv.symm_apply_apply] at prepared
  have zero : prodEquiv ((0, 0) : Pair (orderWidth problem)) =
      (0 : Fin (2 ^ (orderWidth problem + orderWidth problem))) := by
    apply Fin.ext
    simp [prodEquiv, finProdFinEquiv]
  rw [zero]
  exact prepared

/-- The two inverse QFTs supply this exact complex row coefficient. -/
def readoutCoefficient (problem : KnownOrderProblem G)
    (output input : Pair (orderWidth problem)) : ℂ :=
  star (QFTOperator (orderWidth problem)) output.1 input.1 *
    star (QFTOperator (orderWidth problem)) output.2 input.2

/-- The real inverse words retain the negative frequency sign and original pair order. -/
lemma readoutCoefficient_negative (problem : KnownOrderProblem G)
    (output input : Pair (orderWidth problem)) :
    readoutCoefficient problem output input =
      (invSqrtN (orderWidth problem) * ω (orderWidth problem) ^
        (-((input.1.val : Int) * (output.1.val : Int)))) *
      (invSqrtN (orderWidth problem) * ω (orderWidth problem) ^
        (-((input.2.val : Int) * (output.2.val : Int)))) := by
  change ((QFTOperator (orderWidth problem))⁻¹ : UnitaryOperator _)
      output.1 input.1 *
    ((QFTOperator (orderWidth problem))⁻¹ : UnitaryOperator _)
      output.2 input.2 = _
  rw [QuantumAlg.invQFTOperator_entry, QuantumAlg.invQFTOperator_entry]

end

end Exponents
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Montgomery
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Resources

/-!
# Original exponent preparation, measured scalar execution, and inverse QFT

This actual circuit prepares the original two exponent registers, initializes
the arithmetic workspace, converts the supplied Montgomery coordinates, runs
the measured point cascade, converts the result back, and applies the original
inverse QFT on the same exponent systems. The final readout measurements follow
this prefix in their own actual allocation and output owner.

The density theorem retains the complete quantum register and its arbitrary
external reference. Its only branch condition is the original active-step
exceptional domain on the mathematically prepared input. Native event budgets
and depths include both original exponent programs and all scalar operations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP ConcreteCircuitAccess
open GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual original exponent programs surround the complete measured scalar implementation. -/
def preMeasurement (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty) (before p.size (2 * orderWidth problem))
      (after p.size (2 * orderWidth problem)) :=
  ((beforeExponentPreparation p problem).seq
    (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd))).seq (afterExponentReadout p problem)

/-- The original exponent operator independently defines the complete prepared input. -/
def exponentPreparedDensity (problem : KnownOrderProblem E.GroupPoint) (Reference : Register)
    (input : DensityOperator (Register.prod
      (before p.size (2 * orderWidth problem)).register Reference)) :
    DensityOperator (Register.prod (before p.size (2 * orderWidth problem)).register Reference) :=
  DensityOperator.applyUnitary
    (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
      Reference) input

/-- The full density includes real initialization, scalar target, and original readout. -/
def preMeasurementDensity (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (Reference : Register)
    (input : DensityOperator (Register.prod
      (before p.size (2 * orderWidth problem)).register Reference)) :
    DensityOperator (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor
      (afterExponentProgram p (orderWidth problem)
        (exponentReadoutCircuit problem)).matrix (1 : UnitaryOperator Reference))
    (Encoding.convertedResultDensity E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd) Reference
      (exponentPreparedDensity E problem Reference input))

/-- Actual preparation, measured scalar execution and inverse QFT retain the original domain. -/
theorem preMeasurement_density (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (input : State (before p.size (2 * orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference input.quantumMarginal).matrix
          basis basis = 0) :
    ((preMeasurement E fieldTail odd problem points).execute Reference input).quantumMarginal =
      preMeasurementDensity E fieldTail odd problem points Reference input.quantumMarginal := by
  have prepared := beforeExponentCircuit_density p (orderWidth problem)
    (exponentPreparationCircuit problem)
    input
  have domain : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        ((beforeExponentPreparation p problem).execute Reference input).quantumMarginal.matrix
          basis basis = 0 := by
    rw [beforeExponentPreparation, prepared]
    exact support
  have scalar := Encoding.convertedCircuit_density_of_pairedMontgomery_admissible E
    fieldTail sameWidth fits odd points seed
    ((beforeExponentPreparation p problem).execute Reference input) domain
  rw [preMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    afterExponentReadout, afterExponentCircuit_density, Circuit.execute_seq,
    State.mapHistory_quantumMarginal, scalar]
  rw [beforeExponentPreparation, prepared]
  rfl

/-- The actual prefix charges the original exponent programs and the complete converted cascade. -/
theorem preMeasurement_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).resourcePool path ≤
      (exponentPreparationCircuit problem).eventCost +
        Encoding.convertedEventBudget p (2 * orderWidth problem) (2 * orderWidth problem) +
          (exponentReadoutCircuit problem).eventCost := by
  change ResourcePool.ofList
    (((beforeExponentPreparation p problem).eventTrace path.1.1 ++
      (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
        (Semantics.radixUnit p fieldTail.succ odd)).eventTrace path.1.2) ++
      (afterExponentReadout p problem).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  change (beforeExponentPreparation p problem).resourcePool path.1.1 +
    (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)).resourcePool path.1.2 +
    (afterExponentReadout p problem).resourcePool path.2 ≤ _
  have prepared := beforeExponentCircuit_cost p (orderWidth problem)
    (exponentPreparationCircuit problem)
    path.1.1
  have readout := afterExponentCircuit_cost p (orderWidth problem)
    (exponentReadoutCircuit problem) path.2
  exact ResourcePool.add_mono (ResourcePool.add_mono prepared.le
    (by
      simpa only [List.length_finRange] using Encoding.convertedCircuit_budget E points
        (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
        path.1.2)) readout.le

/-- Serial depth includes both original exponent programs and every charged scalar operation. -/
theorem preMeasurement_depth (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).depth (fun _ => 1) path ≤
      (exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (ResourcePool.weightedCount (fun _ => 1)
          (ResourcePool.ofList (Allocation.initializationTrace p
            (2 * orderWidth problem))) +
          (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) := by
  change (beforeExponentPreparation p problem).depth (fun _ => 1) path.1.1 +
    (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)).depth (fun _ => 1) path.1.2 +
    (afterExponentReadout p problem).depth (fun _ => 1) path.2 ≤ _
  have prepared := beforeExponentCircuit_depth p (orderWidth problem)
    (exponentPreparationCircuit problem)
    (fun _ => 1) path.1.1
  have readout := afterExponentCircuit_depth p (orderWidth problem)
    (exponentReadoutCircuit problem)
    (fun _ => 1) path.2
  have scalar := Encoding.convertedCircuit_depth E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
    path.1.2
  rw [List.length_finRange] at scalar
  exact Nat.add_le_add (Nat.add_le_add prepared.le
    scalar) readout.le

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

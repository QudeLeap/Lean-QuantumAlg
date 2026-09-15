/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Complete live space of the actual ECDLP prefix

Original exponent preparation and inverse QFT act on their existing contexts.
The complete measured scalar allocation determines the peak of the composed
prefix. Both supplied exponent registers, coordinate words, arithmetic work,
selector, and retained intermediate results contribute in their actual roles.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation GenericPointAddition.InPlace
open FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The whole actual prefix has precisely the scalar implementation's complete resident peak. -/
theorem preMeasurement_resident (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).peakResidentSpace path =
      readySpace p.size (2 * orderWidth problem) := by
  have inputBound := Circuit.input_residentSpace_le_peak (Encoding.convertedCircuit E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)) path.1.2
  rw [Encoding.convertedCircuit_resident] at inputBound
  have prepared : (beforeExponentPreparation p problem).peakResidentSpace path.1.1 =
      (before p.size (2 * orderWidth problem)).residentSpace := SpacePool.max_zero _
  have readout : (afterExponentReadout p problem).peakResidentSpace path.2 =
      (after p.size (2 * orderWidth problem)).residentSpace := SpacePool.max_zero _
  have scalarPeak := Encoding.convertedCircuit_resident E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd) path.1.2
  have inner := Circuit.peakResidentSpace_seq (beforeExponentPreparation p problem)
    (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)) path.1
  have innerPeak := inner.trans ((congrArg₂ SpacePool.max prepared scalarPeak).trans
    (SpacePool.max_eq_right inputBound))
  have readoutPeak := readout.trans (after_resident p.size (2 * orderWidth problem))
  have whole := Circuit.peakResidentSpace_seq
    ((beforeExponentPreparation p problem).seq (Encoding.convertedCircuit E points
      (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)))
    (afterExponentReadout p problem) path
  exact whole.trans ((congrArg₂ SpacePool.max innerPeak readoutPeak).trans
    (SpacePool.max_eq_right le_rfl))

/-- The same actual prefix retains exactly the original fixed auxiliary roles at its peak. -/
theorem preMeasurement_auxiliary (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (path : (preMeasurement E fieldTail odd problem points).Path) :
    (preMeasurement E fieldTail odd problem points).peakAuxiliarySpace path =
      readySpace p.size (2 * orderWidth problem) := by
  have inputBound := Circuit.input_auxiliarySpace_le_peak (Encoding.convertedCircuit E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)) path.1.2
  rw [Encoding.convertedCircuit_auxiliary] at inputBound
  have prepared : (beforeExponentPreparation p problem).peakAuxiliarySpace path.1.1 =
      (before p.size (2 * orderWidth problem)).auxiliarySpace := SpacePool.max_zero _
  have readout : (afterExponentReadout p problem).peakAuxiliarySpace path.2 =
      (after p.size (2 * orderWidth problem)).auxiliarySpace := SpacePool.max_zero _
  have scalarPeak := Encoding.convertedCircuit_auxiliary E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd) path.1.2
  have inner := Circuit.peakAuxiliarySpace_seq (beforeExponentPreparation p problem)
    (Encoding.convertedCircuit E points (List.finRange (2 * orderWidth problem))
      (Semantics.radixUnit p fieldTail.succ odd)) path.1
  have innerPeak := inner.trans ((congrArg₂ SpacePool.max prepared scalarPeak).trans
    (SpacePool.max_eq_right inputBound))
  have readoutPeak := readout.trans (after_auxiliary p.size (2 * orderWidth problem))
  have whole := Circuit.peakAuxiliarySpace_seq
    ((beforeExponentPreparation p problem).seq (Encoding.convertedCircuit E points
      (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)))
    (afterExponentReadout p problem) path
  exact whole.trans ((congrArg₂ SpacePool.max innerPeak readoutPeak).trans
    (SpacePool.max_eq_right le_rfl))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

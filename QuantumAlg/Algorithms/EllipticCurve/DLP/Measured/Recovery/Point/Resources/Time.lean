/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Execution
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Resources

/-!
# Time of the literal allocation-free measured point body

These bounds follow the actual reset outcome, selected arithmetic suffix and
five consecutive point instructions. Existing independent native allowances
bound the actual placed programs. No execution is replaced by a resource pool,
and no input state, clean bank or positive-mass condition is assumed.


-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Time

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.MAU.Inversion.SharedEEA

attribute [local irreducible] MeasuredPointAddition.beforeDivision
  MeasuredPointAddition.beforeMultiplication MeasuredPointAddition.afterMultiplication
  MeasuredPointAddition.beforeBudget MeasuredPointAddition.middleBudget
  MeasuredPointAddition.afterBudget

private lemma numeratorReset_unitDepth (width : Nat)
    (path : (numeratorReset width).Path) :
    (numeratorReset width).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  have first :
      (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).evaluatedEventDepth
        (fun _ => 1) = if width = 0 then 0 else 1 := by
    rw [NumeratorReset.placement_depth]
    change (UnitaryCircuit.onBinarySuffix (encoding width).width
      (Gate.HadamardLayer.circuit .empty width)).evaluatedEventDepth (fun _ => 1) = _
    rw [UnitaryCircuit.unitaryCircuit_onBinarySuffix_evaluatedEventDepth]
    exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth .empty width
  have measured :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).depth (fun _ => 1) path.2.1 = width :=
    (Circuit.measurementSequence_unitDepth (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (NumeratorMeasurement.readouts width)
      path.2.1).trans List.length_ofFn
  have last :
      (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).evaluatedEventDepth
        (fun _ => 1) ≤ if width = 0 then 0 else 1 := by
    rw [NumeratorReset.placement_depth]
    change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
      (NumeratorResetParallel.program (NumeratorReset.outcome path.2.2.1))).evaluatedEventDepth
        (fun _ => 1) ≤ _
    rw [UnitaryCircuit.onCanonicalBinarySuffix_evaluatedEventDepth]
    exact NumeratorResetParallel.program_unitDepth _
  change (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).evaluatedEventDepth
      (fun _ => 1) +
    ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (NumeratorMeasurement.readouts width)).depth (fun _ => 1) path.2.1 +
      (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).evaluatedEventDepth
        (fun _ => 1)) ≤ _
  rw [first, measured]
  split_ifs at * <;> omega

private lemma controlledNative_unitDepth (width : Nat)
    (native : InPlaceControlled.NativeCircuit width)
    (path : (controlledNative width native).Path) :
    (controlledNative width native).depth (fun _ => 1) path ≤ native.eventCost.card := by
  change (InPlaceControlled.runtimeProgram width native).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [← InPlaceControlled.runtimeProgram_cost width native]
  exact ShiftResources.unitDepth_le_count _

private lemma controlledReset_unitDepth (width : Nat)
    (path : (controlledReset width).Path) :
    (controlledReset width).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  change (numeratorReset width).depth (fun _ => 1) path ≤ _
  exact numeratorReset_unitDepth width path

private lemma controlledBody_unitDepth (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (controlledBody operation modulus prime).Path) :
    (controlledBody operation modulus prime).depth (fun _ => 1) path ≤
      InPlaceControlled.depthBound operation modulus.size := by
  change
    (controlledNative modulus.size (InPlaceControlled.beforeReset operation modulus prime)).depth
        (fun _ => 1) path.1 +
      ((controlledReset modulus.size).depth (fun _ => 1) path.2.1 +
        (controlledNative modulus.size (InPlaceControlled.suffix operation modulus prime
          path.2.2.1)).depth (fun _ => 1) path.2.2.2) ≤ _
  exact Nat.add_le_add
    ((controlledNative_unitDepth _ _ _).trans
      (Multiset.card_le_card (InPlaceControlled.beforeReset_budget operation modulus prime)))
    (Nat.add_le_add (controlledReset_unitDepth modulus.size path.2.1)
      ((controlledNative_unitDepth _ _ _).trans
        (Multiset.card_le_card (InPlaceControlled.suffix_budget operation modulus prime
          path.2.2.1))))

private lemma pointNative_unitDepth (width : Nat)
    (native : MeasuredPointAddition.NativeCircuit width)
    (path : (pointNative width native).Path) :
    (pointNative width native).depth (fun _ => 1) path ≤ native.eventCost.card := by
  change (MeasuredPointAddition.runtimeProgram width native).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [← MeasuredPointAddition.runtimeProgram_cost width native]
  exact ShiftResources.unitDepth_le_count _

private lemma pointArithmetic_unitDepth (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (path : (pointArithmetic operation modulus prime).Path) :
    (pointArithmetic operation modulus prime).depth (fun _ => 1) path ≤
      InPlaceControlled.depthBound operation modulus.size := by
  change (controlledBody operation modulus prime).depth (fun _ => 1) path ≤ _
  exact controlledBody_unitDepth operation modulus prime path

/-- All five actual point stages satisfy the original independent measured depth allowance. -/
lemma pointBody_unitDepth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (pointBody E Q).Path) :
    (pointBody E Q).depth (fun _ => 1) path ≤ MeasuredPointAddition.depthBound p.size := by
  have beforeCard : (MeasuredPointAddition.beforeDivision Q).eventCost.card ≤
      (MeasuredPointAddition.beforeBudget p.size).card :=
    Multiset.card_le_card (MeasuredPointAddition.beforeDivision_budget (E := E) Q)
  have before := (pointNative_unitDepth p.size (MeasuredPointAddition.beforeDivision Q)
    path.1).trans beforeCard
  have division := pointArithmetic_unitDepth .division p Fact.out path.2.1
  have middleCard : (MeasuredPointAddition.beforeMultiplication Q).eventCost.card ≤
      (MeasuredPointAddition.middleBudget p.size).card :=
    Multiset.card_le_card (MeasuredPointAddition.beforeMultiplication_budget (E := E) Q)
  have middle := (pointNative_unitDepth p.size (MeasuredPointAddition.beforeMultiplication Q)
    path.2.2.1).trans middleCard
  have multiplication := pointArithmetic_unitDepth .multiplication p Fact.out path.2.2.2.1
  have afterCard : (MeasuredPointAddition.afterMultiplication E Q).eventCost.card ≤
      (MeasuredPointAddition.afterBudget p.size).card :=
    Multiset.card_le_card (MeasuredPointAddition.afterMultiplication_budget E Q)
  have after := (pointNative_unitDepth p.size (MeasuredPointAddition.afterMultiplication E Q)
    path.2.2.2.2).trans afterCard
  change (pointNative p.size (MeasuredPointAddition.beforeDivision Q)).depth (fun _ => 1) path.1 +
    ((pointArithmetic .division p Fact.out).depth (fun _ => 1) path.2.1 +
      ((pointNative p.size (MeasuredPointAddition.beforeMultiplication Q)).depth
          (fun _ => 1) path.2.2.1 +
        ((pointArithmetic .multiplication p Fact.out).depth (fun _ => 1) path.2.2.2.1 +
          (pointNative p.size (MeasuredPointAddition.afterMultiplication E Q)).depth
            (fun _ => 1) path.2.2.2.2))) ≤ _
  unfold MeasuredPointAddition.depthBound
  omega

/-- Canonical quantum time retains the same measured point path and all selected suffixes. -/
lemma pointBody_quantumTime {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (pointBody E Q).Path) :
    (pointBody E Q).quantumTime path ≤ MeasuredPointAddition.depthBound p.size :=
  (Circuit.quantumTime_le_unitDepth (pointBody E Q) path).trans (pointBody_unitDepth E Q path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Time

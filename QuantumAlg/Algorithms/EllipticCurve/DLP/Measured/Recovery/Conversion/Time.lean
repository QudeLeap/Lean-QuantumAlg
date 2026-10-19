/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Resources.Time
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Time
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Resources

/-!
# Quantum time of the actual four-conversion streaming sampler

The literal conversion placements, each actual measured point suffix, all
feedback reads, the native two-qubit preparation and the measured readout
correction are charged on the original complete paths. The conservative
feedback allowance retains every candidate previous index. No success,
state-initialization or clean-cell condition is required.

 Its bound is
for one actual reset and sample, rather than a complete recovery contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace Time

noncomputable section

private lemma circuit_conditional_quantumTime {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allowAllocation : Bool} {condition : Prop}
    (decision : Decidable condition)
    (yes no : Circuit model ctx ctx allowAllocation) (bound : Nat)
    (yesBound : ∀ path : yes.Path, yes.quantumTime path ≤ bound)
    (noBound : ∀ path : no.Path, no.quantumTime path ≤ bound) :
    ∀ path : (@ite (Circuit model ctx ctx allowAllocation) condition decision yes no).Path,
      (@ite (Circuit model ctx ctx allowAllocation) condition decision yes no).quantumTime
        path ≤ bound := by
  cases decision with
  | isTrue selected => exact yesBound
  | isFalse absent => exact noBound


open scoped BigOperators

private lemma coordinateCircuit_unitDepth (width m : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width m modulus coefficient coordinate).Path) :
    (coordinateCircuit width m modulus coefficient coordinate).depth (fun _ => 1) path ≤
      MAU.Multiplication.Gidney.eventBound width := by
  change (coordinateProgram width m modulus coefficient coordinate).evaluatedEventDepth
    (fun _ => 1) ≤ _
  rw [coordinateProgram, UnitaryCircuit.placeAt_evaluatedEventDepth]
  change (ScalarMultiplication.MeasuredPlacement.Encoding.coordinateCircuit width 2 modulus
    coefficient coordinate false).depth
    (fun _ => 1) path ≤ _
  exact ScalarMultiplication.MeasuredPlacement.Encoding.coordinateCircuit_depth (allowAllocation
    := false) width 2 modulus coefficient coordinate path

private lemma pairCircuit_quantumTime (width m : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width m modulus coefficient).Path) :
    (pairCircuit width m modulus coefficient).quantumTime path ≤
      2 * MAU.Multiplication.Gidney.eventBound width := by
  have first := (Circuit.quantumTime_le_unitDepth
    (coordinateCircuit width m modulus coefficient .x) path.1).trans
      (coordinateCircuit_unitDepth width m modulus coefficient .x path.1)
  have last := (Circuit.quantumTime_le_unitDepth
    (coordinateCircuit width m modulus coefficient .y) path.2).trans
      (coordinateCircuit_unitDepth width m modulus coefficient .y path.2)
  change (coordinateCircuit width m modulus coefficient .x).quantumTime path.1 +
    (coordinateCircuit width m modulus coefficient .y).quantumTime path.2 ≤ _
  omega

private lemma preparation_quantumTime (width m r remaining : Nat) :
    (Recovery.Layout.preparation width m r remaining).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 11 := by
  have dominated := DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one
    ((Recovery.Layout.preparation width m r remaining).eventDepth .empty .empty)
  change (Recovery.Layout.preparation width m r remaining).evaluatedEventDepth
      Resource.Event.quantumDuration ≤
    (Recovery.Layout.preparation width m r remaining).evaluatedEventDepth (fun _ => 1) at dominated
  refine dominated.trans ?_
  rw [Recovery.Layout.preparation, UnitaryCircuit.placeAt_evaluatedEventDepth]
  change (Recovery.Point.Program.program (Recovery.Point.Extension.fixedGates (2 ^ remaining)
    (r % (2 * 2 ^ remaining)) (Nat.mod_lt r (by positivity)))).evaluatedEventDepth
      (fun _ => 1) ≤ 11
  rw [Recovery.Point.Program.fixed_native_depth]
  split_ifs <;> decide

private lemma phaseProgram_quantumTime (width m : Nat) (previous current : Fin (2 * m))
    (value : CShape.Value (.finite 2)) :
    (Recovery.Stage.phaseProgram width m previous current value).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 1 := by
  cases value with
  | finite bit =>
      change (if bit.val = 1 then
        Gate.singleQubitAt (Recovery.Stage.Context width m).quantumLayout .empty
          (phaseGateOp (-(QuantumFourierTransform.Source.phaseAngle
            (current.val - previous.val - 1))))
          (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)
        else UnitaryCircuit.identity AlgorithmGate.model .empty
          (Recovery.Stage.Context width m).quantumLayout).evaluatedEventDepth
            Resource.Event.quantumDuration ≤ 1
      split_ifs
      · simpa only [Gate.singleQubitAt, UnitaryCircuit.evaluatedEventDepth_native,
          Resource.Event.quantumDuration_gate] using (Nat.le_refl 1)
      · rw [UnitaryCircuit.evaluatedEventDepth_identity]
        exact Nat.zero_le 1


private lemma feedbackOne_quantumTime (width m : Nat) (previous current : Fin (2 * m))
    (path : (Recovery.Stage.feedbackOne width m previous current).Path) :
    (Recovery.Stage.feedbackOne width m previous current).quantumTime path ≤ 1 := by
  revert path
  unfold Recovery.Stage.feedbackOne
  refine circuit_conditional_quantumTime _ _ _ 1 ?_ ?_
  · intro path
    change (Recovery.Stage.phaseProgram width m previous current path.1).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 1
    exact phaseProgram_quantumTime width m previous current path.1
  · intro path
    rw [Circuit.quantumTime_id]
    exact Nat.zero_le 1

private lemma feedback_quantumTime (width m : Nat) (current : Fin (2 * m))
    (previous : List (Fin (2 * m))) (path : (Recovery.Stage.feedback width m current
      previous).Path) :
    (Recovery.Stage.feedback width m current previous).quantumTime path ≤ previous.length := by
  induction previous with
  | nil =>
      change 0 ≤ 0
      exact Nat.le_refl 0
  | cons head tail ih =>
      change (Recovery.Stage.feedbackOne width m head current).quantumTime path.1 +
        (Recovery.Stage.feedback width m current tail).quantumTime path.2 ≤ tail.length + 1
      have first := feedbackOne_quantumTime width m head current path.1
      have last := ih path.2
      omega

private lemma readout_quantumTime (width m : Nat) (index : Fin (2 * m))
    (path : (Recovery.Stage.readout width m index).Path) :
    (Recovery.Stage.readout width m index).quantumTime path ≤ 2 := by
  change 1 + (0 + (QuditShift.qubitShiftCircuit
    (Recovery.Layout.terminal width m).quantumLayout (Recovery.Layout.position width m 0)
    (Recovery.Layout.position_qubit width m 0) .empty (-path.2.2.1.toFin)).evaluatedEventDepth
      Resource.Event.quantumDuration) ≤ 2
  rw [Recovery.Initialization.Time.qubitShift_duration]
  split_ifs <;> decide

private lemma streamingPointCall_quantumTime {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (path : (Recovery.Point.streamingPointCall E points index).Path) :
    (Recovery.Point.streamingPointCall E points index).quantumTime path ≤
      MeasuredPointAddition.depthBound p.size := by
  change (Recovery.Point.pointBody E (points index)).quantumTime path ≤ _
  exact Recovery.Point.Time.pointBody_quantumTime E (points index) path

private lemma stage_quantumTime {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (path : (Recovery.Stage.stage E r points index).Path) :
    (Recovery.Stage.stage E r points index).quantumTime path ≤
      MeasuredPointAddition.depthBound p.size + 2 * m + 13 := by
  have prepared := preparation_quantumTime p.size m r (Recovery.Layout.remaining m index)
  have point := streamingPointCall_quantumTime (m := m) E points index path.2.1
  have feedback := feedback_quantumTime p.size m index (Recovery.Layout.order m) path.2.2.1
  have measured := readout_quantumTime p.size m index path.2.2.2
  change (Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m
    index)).evaluatedEventDepth
      Resource.Event.quantumDuration +
    ((Recovery.Point.streamingPointCall E points index).quantumTime path.2.1 +
      ((Recovery.Stage.feedback p.size m index (Recovery.Layout.order m)).quantumTime path.2.2.1 +
        (Recovery.Stage.readout p.size m index).quantumTime path.2.2.2)) ≤ _
  have orderLength : (Recovery.Layout.order m).length = 2 * m := by
    rw [Recovery.Layout.order, List.length_finRange]
  rw [orderLength] at feedback
  omega

private lemma stages_quantumTime {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) (path : (Recovery.Stage.stages E r points indices).Path) :
    (Recovery.Stage.stages E r points indices).quantumTime path ≤
      indices.length * (MeasuredPointAddition.depthBound p.size + 2 * m + 13) := by
  induction indices with
  | nil =>
      simp only [List.length_nil, Nat.zero_mul]
      exact (Circuit.quantumTime_id (model := .quantum AlgorithmGate.model .empty)
        (allowAllocation := false) (Recovery.Stage.Context p.size m) path).le
  | cons index tail ih =>
      change (Recovery.Stage.stage E r points index).quantumTime path.1 +
        (Recovery.Stage.stages E r points tail).quantumTime path.2 ≤ _
      calc
        _ ≤ (MeasuredPointAddition.depthBound p.size + 2 * m + 13) +
            tail.length * (MeasuredPointAddition.depthBound p.size + 2 * m + 13) :=
          Nat.add_le_add (stage_quantumTime (m := m) E r points index path.1) (ih path.2)
        _ = _ :=
          (Nat.add_comm _ _).trans
            (Nat.succ_mul tail.length
              (MeasuredPointAddition.depthBound p.size + 2 * m + 13)).symm

/-- Arbitrary event durations decompose at the same literal conversion/stage paths. -/
lemma convertedStages_duration {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) (coefficient : (ZMod p)ˣ)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (convertedStages E r points indices coefficient).Path) :
    (convertedStages E r points indices coefficient).depth duration path =
      (pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p) coefficient⁻¹).depth
          duration path.1 +
        ((Recovery.Stage.stages E r points indices).depth duration path.2.1 +
          (pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p) coefficient).depth
            duration path.2.2) := rfl

/-- The actual four conversions and every full streaming stage have a width-only bound. -/
lemma convertedStages_quantumTime_le {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) (coefficient : (ZMod p)ˣ)
    (path : (convertedStages E r points indices coefficient).Path) :
    (convertedStages E r points indices coefficient).quantumTime path ≤
      4 * MAU.Multiplication.Gidney.eventBound p.size +
        indices.length * (MeasuredPointAddition.depthBound p.size + 2 * m + 13) := by
  have first := pairCircuit_quantumTime p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
    coefficient⁻¹ path.1
  have body := stages_quantumTime (m := m) E r points indices path.2.1
  have last := pairCircuit_quantumTime p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
    coefficient path.2.2
  change (pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
    coefficient⁻¹).quantumTime
      path.1 +
    ((Recovery.Stage.stages E r points indices).quantumTime path.2.1 +
      (pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient).quantumTime path.2.2) ≤ _
  omega

/-- One actual reset followed by this sampler pays both parts of the same complete path. -/
lemma actualreset_converted_quantumTime_le {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (fieldTail m : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (indices : List (Fin (2 * m)))
    (coefficient : (ZMod p)ˣ)
    (path : ((Recovery.Initialization.newReset E fieldTail m seed).seq
      (convertedStages E r points indices coefficient)).Path) :
    ((Recovery.Initialization.newReset E fieldTail m seed).seq
      (convertedStages E r points indices coefficient)).quantumTime path ≤
      (Recovery.Layout.terminal p.size m).systemCount +
        (4 * MAU.Multiplication.Gidney.eventBound p.size +
          indices.length * (MeasuredPointAddition.depthBound p.size + 2 * m + 13)) := by
  change (Recovery.Initialization.newReset E fieldTail m seed).quantumTime path.1 +
    (convertedStages E r points indices coefficient).quantumTime path.2 ≤ _
  exact Nat.add_le_add
    (Recovery.Initialization.Time.newReset_quantumTime_le E fieldTail m seed path.1)
    (convertedStages_quantumTime_le E r points indices coefficient path.2)

end

end Time
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion

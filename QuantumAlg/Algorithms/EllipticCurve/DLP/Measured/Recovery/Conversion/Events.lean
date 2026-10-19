/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Placement
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Execution.Context.Union.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Resources
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Framing
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Program
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.NativeResources
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources
import all QuantumAlg.Components.Encoded.BitGates.Resources
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# Full native events of the actual four-conversion streaming sampler

All four physical conversion programs retain the original native multiplier
pool. Each actual stage retains its complete point, preparation, feedback and
measured readout pool. Independent parameter formulas preserve the original
three native gate ceilings, including room for the actual reset's possible X
corrections. The sampler's measurements are charged separately and completely.

The fixed twelvefold oversampling supplies the bank-width inequality internally.
No caller gate budget, count positivity or path restriction is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace Events

noncomputable section

open FiniteCyclicDLP (KnownOrderProblem orderWidth oversampledOrder)

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty
private abbrev single := Recovery.Stage.Events.single
private abbrev cnot := Recovery.Stage.Events.cnot
private abbrev measured := Recovery.Stage.Events.measured

def toffoli : ResourcePool Model := ResourcePool.singleton (.gate .toffoli)

/-- Independent literal allowance for four native conversions and the full actual stage order. -/
def samplerBudget (width m : Nat) : ResourcePool Model :=
  4 • MAU.Multiplication.Gidney.nativeBudget width +
    (2 * m) • Recovery.Stage.Events.stageBudget width m

/-- Original three gate ceilings plus every actual sampler measurement, before reset writes. -/
def gateBudget (width m : Nat) : ResourcePool Model :=
  LogicalResources.Scalar.roundToffoli width m • toffoli +
    LogicalResources.Scalar.roundCnot width m • cnot +
    LogicalResources.Scalar.roundSingle width m • single +
    (2 * m * (2 * width + 1)) • measured

lemma gateBudget_single_count (width m : Nat) :
    ResourcePool.count (model := Model) (.gate .singleQubit) (gateBudget width m) =
      LogicalResources.Scalar.roundSingle width m := by
  simp [gateBudget, single, cnot, toffoli, measured,
    Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured]

lemma gateBudget_cnot_count (width m : Nat) :
    ResourcePool.count (model := Model) (.gate .cnot) (gateBudget width m) =
      LogicalResources.Scalar.roundCnot width m := by
  simp [gateBudget, single, cnot, toffoli, measured,
    Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured]

lemma gateBudget_toffoli_count (width m : Nat) :
    ResourcePool.count (model := Model) (.gate .toffoli) (gateBudget width m) =
      LogicalResources.Scalar.roundToffoli width m := by
  simp [gateBudget, single, cnot, toffoli, measured,
    Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured]

lemma gateBudget_measurement_count (width m : Nat) (dimension : ℕ+) :
    ResourcePool.count (model := Model) (.measurement dimension) (gateBudget width m) =
      if 2 = dimension then 2 * m * (2 * width + 1) else 0 := by
  by_cases same : (2 : ℕ+) = dimension <;>
    simp [gateBudget, single, cnot, toffoli, measured,
      Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured,
        same]

lemma gateBudget_preparation_count (width m : Nat) (dimension : ℕ+) :
    ResourcePool.count (model := Model) (.preparation dimension) (gateBudget width m) = 0 := by
  simp [gateBudget, single, cnot, toffoli, measured,
    Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured]

/-- The actual physical conversion placement preserves its original native multiplier ledger. -/
lemma coordinateCircuit_cost (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width m modulus coefficient coordinate).Path) :
    (coordinateCircuit width m modulus coefficient coordinate).resourcePool path =
      (MAU.Multiplication.Gidney.program width modulus coefficient).eventCost := by
  change ResourcePool.ofList
    ((coordinateProgram width m modulus coefficient coordinate).eventTrace) = _
  rw [coordinateProgram, UnitaryCircuit.placeAt_eventTrace]
  change (ScalarMultiplication.MeasuredPlacement.Encoding.coordinateCircuit width 2 modulus
    coefficient coordinate false).resourcePool
    path = _
  exact ScalarMultiplication.MeasuredPlacement.Encoding.coordinateCircuit_cost (allowAllocation :=
    false) width 2 modulus coefficient coordinate path

/-- One actual conversion pays the existing complete independent multiplier allowance. -/
lemma coordinateCircuit_budget (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (coordinate : MeasuredPointAddition.Coordinate)
    (path : (coordinateCircuit width m modulus coefficient coordinate).Path) :
    (coordinateCircuit width m modulus coefficient coordinate).resourcePool path ≤
      MAU.Multiplication.Gidney.nativeBudget width := by
  rw [coordinateCircuit_cost]
  exact MAU.Multiplication.Gidney.gidneyUnitMultiplication_native_bound _ _ _

/-- Both real coordinate calls retain their separate native multiplier allowances. -/
lemma pairCircuit_budget (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ)
    (path : (pairCircuit width m modulus coefficient).Path) :
    (pairCircuit width m modulus coefficient).resourcePool path ≤
      2 • MAU.Multiplication.Gidney.nativeBudget width := by
  change ResourcePool.ofList
    ((coordinateCircuit width m modulus coefficient .x).eventTrace path.1 ++
      (coordinateCircuit width m modulus coefficient .y).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, two_nsmul]
  exact add_le_add (coordinateCircuit_budget width m modulus coefficient .x path.1)
    (coordinateCircuit_budget width m modulus coefficient .y path.2)

/-- All four conversions and every actual finite stage are charged on the original Path. -/
lemma convertedStages_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) (coefficient : (ZMod p)ˣ)
    (path : (convertedStages E r points indices coefficient).Path) :
    (convertedStages E r points indices coefficient).resourcePool path ≤
      4 • MAU.Multiplication.Gidney.nativeBudget p.size +
        indices.length • Recovery.Stage.Events.stageBudget p.size m := by
  have first := pairCircuit_budget p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
    coefficient⁻¹ path.1
  have body := Recovery.Stage.Events.stages_budget E r points indices path.2.1
  have last := pairCircuit_budget p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
    coefficient path.2.2
  change ResourcePool.ofList
    ((pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
      coefficient⁻¹).eventTrace path.1 ++
      ((Recovery.Stage.stages E r points indices).eventTrace path.2.1 ++
        (pairCircuit p.size m (MeasuredUncompute.InPlaceTarget.modulusWord p)
          coefficient).eventTrace path.2.2)) ≤ _
  simp only [ResourcePool.ofList_append]
  refine (add_le_add first (add_le_add body last)).trans_eq ?_
  rw [show (4 : Nat) = 2 + 2 by decide, add_nsmul]
  ac_rfl

private lemma multiplier_budget_coordinates (width : Nat) :
    MAU.Multiplication.Gidney.nativeBudget width =
      LogicalResources.Scalar.multiplierSingle width • single +
        LogicalResources.Scalar.multiplierCnot width • cnot +
        LogicalResources.Scalar.multiplierSingle width • toffoli := by
  classical
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event _ = ResourcePool.count event _
  cases event with
  | gate coordinate =>
      cases coordinate with
      | singleQubit =>
          simpa [single, cnot, toffoli, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
            LogicalResources.Scalar.multiplierSingle] using
            MAU.Multiplication.Gidney.nativeBudget_singleQubit_count_symbolic width
      | cnot =>
          simpa [single, cnot, toffoli, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
            LogicalResources.Scalar.multiplierCnot, LogicalResources.Scalar.multiplierSingle]
            using MAU.Multiplication.Gidney.nativeBudget_cnot_count_symbolic width
      | toffoli =>
          simpa [single, cnot, toffoli, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
            LogicalResources.Scalar.multiplierSingle] using
            MAU.Multiplication.Gidney.nativeBudget_toffoli_count_symbolic width
  | oracle impossible => cases impossible
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | preparation dimension =>
      simp [MAU.Multiplication.Gidney.nativeBudget, MAU.Multiplication.Gidney.wordSwapBudget,
        MAU.Multiplication.Accumulate.Gidney.nativeBudget,
        MAU.Multiplication.Accumulate.Gidney.nativeAlphabet, EncodedBit.GateSpec.primitiveAlphabet,
        single, cnot, toffoli, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
        List.count_replicate]
  | measurement dimension =>
      simp [MAU.Multiplication.Gidney.nativeBudget, MAU.Multiplication.Gidney.wordSwapBudget,
        MAU.Multiplication.Accumulate.Gidney.nativeBudget,
        MAU.Multiplication.Accumulate.Gidney.nativeAlphabet, EncodedBit.GateSpec.primitiveAlphabet,
        single, cnot, toffoli, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
        List.count_replicate]

private lemma point_budget_coordinates (width : Nat) :
    MeasuredPointAddition.events width =
      LogicalResources.Scalar.pointSingle width • single +
        LogicalResources.Scalar.pointCnot width • cnot +
        LogicalResources.Scalar.pointToffoli width • toffoli + (2 * width) • measured := by
  classical
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event _ = ResourcePool.count event _
  cases event with
  | gate coordinate =>
      cases coordinate with
      | singleQubit =>
          simpa [single, cnot, toffoli, measured, Recovery.Stage.Events.single,
            Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured,
              LogicalResources.Scalar.pointSingle]
            using MeasuredPointAddition.events_singleQubit_count width
      | cnot =>
          simpa [single, cnot, toffoli, measured, Recovery.Stage.Events.single,
            Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured,
              LogicalResources.Scalar.pointCnot]
            using MeasuredPointAddition.events_cnot_count width
      | toffoli =>
          simpa [single, cnot, toffoli, measured, Recovery.Stage.Events.single,
            Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured,
            LogicalResources.Scalar.pointToffoli]
            using MeasuredPointAddition.events_toffoli_count width
  | oracle impossible => cases impossible
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | preparation dimension =>
      simp [MeasuredPointAddition.events, MeasuredPointAddition.beforeBudget,
        MeasuredPointAddition.middleBudget, MeasuredPointAddition.afterBudget,
        MeasuredPointAddition.offsetBudget, MeasuredPointAddition.squareBudget,
        MeasuredPointAddition.selectorBudget, MeasuredPointAddition.comparisonBudget,
        MeasuredPointAddition.pivotBudget, MeasuredPointAddition.controlledBudget,
        MeasuredPointAddition.cnotBudget, MeasuredUncompute.InPlaceControlled.events,
          MeasuredUncompute.InPlaceControlled.beforeBudget,
        MeasuredUncompute.InPlaceControlled.afterBudget,
          MeasuredUncompute.InPlaceControlled.saveBudget,
        MeasuredUncompute.InPlaceControlled.correctionBudget,
          MeasuredUncompute.InPlaceControlled.controlledBudget,
        MeasuredUncompute.InPlaceControlled.copyBudget,
          MeasuredUncompute.InPlaceControlled.maskBudget, MeasuredUncompute.NumeratorReset.budget,
        MAU.Multiplication.VariableGidney.nativeBudget,
        MAU.Multiplication.VariableGidney.stageBudget,
        EncodedBit.GateSpec.primitiveAlphabet, Circuit.zEvent, single, cnot, toffoli, measured,
        Recovery.Stage.Events.single, Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured]
  | measurement dimension =>
      by_cases same : (2 : ℕ+) = dimension <;>
        simp [MeasuredPointAddition.events, MeasuredPointAddition.beforeBudget,
          MeasuredPointAddition.middleBudget, MeasuredPointAddition.afterBudget,
          MeasuredPointAddition.offsetBudget, MeasuredPointAddition.squareBudget,
          MeasuredPointAddition.selectorBudget, MeasuredPointAddition.comparisonBudget,
          MeasuredPointAddition.pivotBudget, MeasuredPointAddition.controlledBudget,
          MeasuredPointAddition.cnotBudget, MeasuredUncompute.InPlaceControlled.events,
          MeasuredUncompute.InPlaceControlled.beforeBudget,
          MeasuredUncompute.InPlaceControlled.afterBudget,
            MeasuredUncompute.InPlaceControlled.saveBudget,
          MeasuredUncompute.InPlaceControlled.correctionBudget,
            MeasuredUncompute.InPlaceControlled.controlledBudget,
          MeasuredUncompute.InPlaceControlled.copyBudget,
            MeasuredUncompute.InPlaceControlled.maskBudget,
            MeasuredUncompute.NumeratorReset.budget,
          MAU.Multiplication.VariableGidney.nativeBudget,
          MAU.Multiplication.VariableGidney.stageBudget, EncodedBit.GateSpec.primitiveAlphabet,
          Circuit.zEvent, single, cnot, toffoli, measured, Recovery.Stage.Events.single,
          Recovery.Stage.Events.cnot, Recovery.Stage.Events.measured, same]; omega

private lemma resetGateEnvelope_measurement_count_le (width m : Nat) (dimension : ℕ+) :
    ResourcePool.count (model := Model) (.measurement dimension)
        ((3 * width + 4 * width.size + 14) • single + samplerBudget width m) ≤
      ResourcePool.count (model := Model) (.measurement dimension) (gateBudget width m) := by
  classical
  by_cases same : (2 : ℕ+) = dimension <;>
    simp [samplerBudget, gateBudget, Recovery.Stage.Events.stageBudget,
      multiplier_budget_coordinates, point_budget_coordinates,
      single, cnot, toffoli, measured, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
      Recovery.Stage.Events.measured, same]
  nlinarith

/-- Parameter-only comparison keeps the original three gate ceilings and pays every readout. -/
lemma resetGateEnvelope_add_budget_le (width m : Nat) (wide : 2 ≤ m) :
    (3 * width + 4 * width.size + 14) • single + samplerBudget width m ≤
      gateBudget width m := by
  classical
  have pairs : 2 * m.choose 2 = m * (m - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm 2,
      Nat.div_mul_cancel (Nat.even_mul_pred_self m).two_dvd]
  have predecessor : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
  have square : 2 * m ≤ m * m := Nat.mul_le_mul_right m wide
  apply ResourcePool.le_iff_count.mpr
  intro event
  cases event with
  | gate coordinate =>
      cases coordinate with
      | singleQubit =>
          simp [samplerBudget, gateBudget, Recovery.Stage.Events.stageBudget,
            multiplier_budget_coordinates, point_budget_coordinates,
            single, cnot, toffoli, measured, Recovery.Stage.Events.single,
              Recovery.Stage.Events.cnot,
            Recovery.Stage.Events.measured, LogicalResources.Scalar.roundSingle,
            LogicalResources.Scalar.qubits, LogicalResources.Scalar.readoutSingle]
          nlinarith
      | cnot =>
          have enoughPairs : m ≤ 2 * m.choose 2 := by
            rw [pairs]
            simpa only [mul_one] using
              Nat.mul_le_mul_left m (show 1 ≤ m - 1 by omega)
          simp [samplerBudget, gateBudget, Recovery.Stage.Events.stageBudget,
            multiplier_budget_coordinates, point_budget_coordinates,
            single, cnot, toffoli, measured, Recovery.Stage.Events.single,
              Recovery.Stage.Events.cnot,
            Recovery.Stage.Events.measured, LogicalResources.Scalar.roundCnot,
            LogicalResources.Scalar.readoutCnot]
          omega
      | toffoli =>
          simp [samplerBudget, gateBudget, Recovery.Stage.Events.stageBudget,
            multiplier_budget_coordinates, point_budget_coordinates,
            single, cnot, toffoli, measured, Recovery.Stage.Events.single,
              Recovery.Stage.Events.cnot,
            Recovery.Stage.Events.measured, LogicalResources.Scalar.roundToffoli]
  | oracle impossible => cases impossible
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | preparation dimension =>
      simp [samplerBudget, gateBudget, Recovery.Stage.Events.stageBudget,
        multiplier_budget_coordinates, point_budget_coordinates,
        single, cnot, toffoli, measured, Recovery.Stage.Events.single, Recovery.Stage.Events.cnot,
        Recovery.Stage.Events.measured]
  | measurement dimension =>
      exact resetGateEnvelope_measurement_count_le width m dimension

/-- Twelvefold known-order oversampling gives the required two positions without a new premise. -/
lemma orderWidth_two_le {G : Type} [Group G] (problem : KnownOrderProblem G) :
    2 ≤ orderWidth problem := by
  have positive := problem.order_pos
  have wide : 1 < Nat.clog 2 (oversampledOrder problem) := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    change 2 < 12 * problem.order
    omega
  exact wide

/-- The actual full order leaves room for reset X gates inside the original gate ceilings. -/
lemma convertedStages_original_gateBudget {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (problem : KnownOrderProblem E.GroupPoint) (r : Nat)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (path : (convertedStages E r points (Recovery.Layout.order (orderWidth problem))
      coefficient).Path) :
    (3 * p.size + 4 * p.size.size + 14) • single +
        (convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).resourcePool path ≤ gateBudget p.size (orderWidth problem) := by
  have actual := convertedStages_budget E r points (Recovery.Layout.order (orderWidth problem))
    coefficient path
  change (convertedStages E r points (Recovery.Layout.order (orderWidth problem))
    coefficient).resourcePool path ≤
      4 • MAU.Multiplication.Gidney.nativeBudget p.size +
        (List.finRange (2 * orderWidth problem)).length •
          Recovery.Stage.Events.stageBudget p.size (orderWidth problem) at actual
  rw [List.length_finRange] at actual
  exact (add_le_add le_rfl actual).trans
    (resetGateEnvelope_add_budget_le p.size (orderWidth problem) (orderWidth_two_le problem))

end

end Events
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion

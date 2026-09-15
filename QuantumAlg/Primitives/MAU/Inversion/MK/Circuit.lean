/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Correction
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Compact.Fold
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.RoutedRound
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Static fixed-round inversion circuit
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

open MK
open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Six-stage static round ledger -/

/-- Complete primitive source list for one fixed round, in the same physical
order as the six actual stage circuits. -/
def roundGates (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  originalActiveLatchGates tail counterWidth ++
  inactivePaddingGates tail counterWidth ++
  controlledActiveOnlyGates tail counterWidth comparisonIndex
    roundIndex workIndex ++
  branchResidueCleanupGates tail counterWidth roundIndex ++
  spillWorkingPathGates tail counterWidth roundIndex ++
  resetWorkingPathGates tail counterWidth roundIndex

/-! ## Width-only primitive-leaf bounds -/

/-- Conservative width-only bound `P(t,c)` for the detector-gated
terminating route. -/
def terminatingRouteGateLengthBound (tail counterWidth : Nat) : Nat :=
  8 * tail.succ + 24 * counterWidth + 5

/-- Conservative width-only bound `Q(t,c)` for the uncontrolled active-only
route. -/
def activeRouteGateLengthBound (tail counterWidth : Nat) : Nat :=
  2 * terminatingRouteGateLengthBound tail counterWidth + 370 * tail + 274

/-- Conservative width-only bound `R(t,c)` for one complete six-stage round. -/
def roundGateLengthBound (tail counterWidth : Nat) : Nat :=
  24 * counterWidth + 11 +
    3 * activeRouteGateLengthBound tail counterWidth

/-- Conservative width-only bound `F(t,c)` for the fixed `2(t+1)`-round
fold. -/
def foldGateLengthBound (tail counterWidth : Nat) : Nat :=
  2 * tail.succ * roundGateLengthBound tail counterWidth

private theorem vZeroDetectorWithComparisonWorkGates_length
    (tail counterWidth : Nat) :
    (vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).length =
      4 * tail.succ + 1 := by
  simp only [vZeroDetectorWithComparisonWorkGates,
    vZeroDetectorNegateVGates, vZeroDetectorPrefixGates,
    List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
    List.length_reverse]
  omega

private theorem vZeroDetectorWithComparisonWorkGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail.succ := by
  simp [vZeroDetectorWithComparisonWorkGates,
    vZeroDetectorNegateVGates, vZeroDetectorPrefixGates,
    vZeroDetectorCopyOutGate, List.sum_ofFn]
  omega

private theorem vZeroDetectorWithComparisonWorkGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
  simp [vZeroDetectorWithComparisonWorkGates,
    vZeroDetectorNegateVGates, vZeroDetectorPrefixGates,
    vZeroDetectorCopyOutGate, List.sum_ofFn]

private theorem vZeroDetectorWithComparisonWorkGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * tail := by
  simp [vZeroDetectorWithComparisonWorkGates,
    vZeroDetectorNegateVGates, vZeroDetectorPrefixGates,
    vZeroDetectorCopyOutGate, List.sum_ofFn, Nat.mul_comm]
  omega

private theorem detectorCounterTerminatingCounterModeGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterTerminatingCounterModeGates
        tail.succ counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 1 := by
  simp [detectorCounterTerminatingCounterModeGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum]

private theorem detectorCounterTerminatingCounterModeGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterTerminatingCounterModeGates
        tail.succ counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * counterWidth := by
  simp [detectorCounterTerminatingCounterModeGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum]

private theorem
    detectorCounterTerminatingCounterModeGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterTerminatingCounterModeGates
        tail.succ counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        6 * (counterWidth - 1) := by
  simp [detectorCounterTerminatingCounterModeGates,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum]

private theorem
    detectorCounterControlledTerminatingCounterModeGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterControlledTerminatingCounterModeGates
        tail counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  unfold detectorCounterControlledTerminatingCounterModeGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    detectorCounterTerminatingCounterModeGates_xMultiplicity_sum]

private theorem
    detectorCounterControlledTerminatingCounterModeGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterControlledTerminatingCounterModeGates
        tail counterWidth).map EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  unfold detectorCounterControlledTerminatingCounterModeGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum]

private theorem
    detectorCounterControlledTerminatingCounterModeGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterControlledTerminatingCounterModeGates
        tail counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        2 * counterWidth + 18 * (counterWidth - 1) := by
  unfold detectorCounterControlledTerminatingCounterModeGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    detectorCounterTerminatingCounterModeGates_cnotMultiplicity_sum,
    detectorCounterTerminatingCounterModeGates_toffoliMultiplicity_sum]
  omega

private theorem detectorCounterVZeroDetectorGates_events_eq_source
    (tail counterWidth : Nat) :
    (detectorCounterVZeroDetectorGates tail.succ counterWidth).map
        EncodedBit.GateSpec.event =
      (vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
        EncodedBit.GateSpec.event := by
  unfold detectorCounterVZeroDetectorGates
  exact EncodedBit.GateSpec.map_event_prodLeft
    (counterIncrementWorkEncoding counterWidth)
    (vZeroDetectorWithComparisonWorkGates tail.succ counterWidth)

private theorem detectorCounterVZeroDetectorGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterVZeroDetectorGates tail.succ counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail.succ := by
  calc
    _ = ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
          EncodedBit.GateSpec.xMultiplicity).sum :=
      EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        (detectorCounterVZeroDetectorGates_events_eq_source
          tail counterWidth)
    _ = 2 * tail.succ :=
      vZeroDetectorWithComparisonWorkGates_xMultiplicity_sum
        tail counterWidth

private theorem detectorCounterVZeroDetectorGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterVZeroDetectorGates tail.succ counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
  calc
    _ = ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
          EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        (detectorCounterVZeroDetectorGates_events_eq_source
          tail counterWidth)
    _ = 3 := vZeroDetectorWithComparisonWorkGates_cnotMultiplicity_sum
      tail counterWidth

private theorem detectorCounterVZeroDetectorGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterVZeroDetectorGates tail.succ counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * tail := by
  calc
    _ = ((vZeroDetectorWithComparisonWorkGates tail.succ counterWidth).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        (detectorCounterVZeroDetectorGates_events_eq_source
          tail counterWidth)
    _ = 2 * tail :=
      vZeroDetectorWithComparisonWorkGates_toffoliMultiplicity_sum
        tail counterWidth

private theorem
    detectorGatedTerminatingCounterModeWithWorkGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorGatedTerminatingCounterModeWithWorkGates
        tail counterWidth).map EncodedBit.GateSpec.xMultiplicity).sum =
      4 * tail.succ := by
  simp only [detectorGatedTerminatingCounterModeWithWorkGates,
    List.map_append, List.sum_append,
    detectorCounterVZeroDetectorGates_xMultiplicity_sum,
    detectorCounterControlledTerminatingCounterModeGates_xMultiplicity_sum]
  omega

private theorem
    detectorGatedTerminatingCounterModeWithWorkGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorGatedTerminatingCounterModeWithWorkGates
        tail counterWidth).map EncodedBit.GateSpec.cnotMultiplicity).sum = 7 := by
  simp only [detectorGatedTerminatingCounterModeWithWorkGates,
    List.map_append, List.sum_append,
    detectorCounterVZeroDetectorGates_cnotMultiplicity_sum,
    detectorCounterControlledTerminatingCounterModeGates_cnotMultiplicity_sum]

private theorem
    detectorGatedTerminatingCounterModeWithWorkGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorGatedTerminatingCounterModeWithWorkGates
        tail counterWidth).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      4 * tail + 2 * counterWidth + 18 * (counterWidth - 1) := by
  simp only [detectorGatedTerminatingCounterModeWithWorkGates,
    List.map_append, List.sum_append,
    detectorCounterVZeroDetectorGates_toffoliMultiplicity_sum,
    detectorCounterControlledTerminatingCounterModeGates_toffoliMultiplicity_sum]
  omega

private theorem fullRoundWorkTerminatingStandardLayoutGates_events_eq_source
    (tail counterWidth : Nat) :
    (fullRoundWorkTerminatingStandardLayoutGates tail counterWidth).map
        EncodedBit.GateSpec.event =
      (detectorGatedTerminatingCounterModeWithWorkGates
        tail counterWidth).map EncodedBit.GateSpec.event := by
  unfold fullRoundWorkTerminatingStandardLayoutGates
  simp only [List.map_map]
  apply List.map_congr_left
  intro gate _
  exact event_insertMiddleGateSpec (coeffAdderWorkEncoding tail.succ) gate

private theorem
    fullRoundWorkTerminatingStandardLayoutGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((fullRoundWorkTerminatingStandardLayoutGates tail counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 * tail.succ := by
  calc
    _ = ((detectorGatedTerminatingCounterModeWithWorkGates
          tail counterWidth).map EncodedBit.GateSpec.xMultiplicity).sum :=
      EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        (fullRoundWorkTerminatingStandardLayoutGates_events_eq_source
          tail counterWidth)
    _ = 4 * tail.succ :=
      detectorGatedTerminatingCounterModeWithWorkGates_xMultiplicity_sum
        tail counterWidth

private theorem
    fullRoundWorkTerminatingStandardLayoutGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((fullRoundWorkTerminatingStandardLayoutGates tail counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 7 := by
  calc
    _ = ((detectorGatedTerminatingCounterModeWithWorkGates
          tail counterWidth).map EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        (fullRoundWorkTerminatingStandardLayoutGates_events_eq_source
          tail counterWidth)
    _ = 7 :=
      detectorGatedTerminatingCounterModeWithWorkGates_cnotMultiplicity_sum
        tail counterWidth

private theorem
    fullRoundWorkTerminatingStandardLayoutGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((fullRoundWorkTerminatingStandardLayoutGates tail counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      4 * tail + 2 * counterWidth + 18 * (counterWidth - 1) := by
  calc
    _ = ((detectorGatedTerminatingCounterModeWithWorkGates
          tail counterWidth).map EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        (fullRoundWorkTerminatingStandardLayoutGates_events_eq_source
          tail counterWidth)
    _ = 4 * tail + 2 * counterWidth + 18 * (counterWidth - 1) :=
      detectorGatedTerminatingCounterModeWithWorkGates_toffoliMultiplicity_sum
        tail counterWidth

private theorem detectorCounterTerminatingCounterModeGates_length_le
    (tail counterWidth : Nat) :
    (detectorCounterTerminatingCounterModeGates tail.succ counterWidth).length ≤
      8 * counterWidth + 1 := by
  have hcarry :
      (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
        (detectorCounterIncrementLayout tail.succ counterWidth)).length ≤
        8 * counterWidth :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length_le
      (detectorCounterIncrementLayout tail.succ counterWidth)
  simp only [detectorCounterTerminatingCounterModeGates,
    List.length_append, List.length_cons, List.length_nil]
  omega

private theorem detectorCounterControlledTerminatingCounterModeGates_length_le
    (tail counterWidth : Nat) :
    (detectorCounterControlledTerminatingCounterModeGates
      tail counterWidth).length ≤ 24 * counterWidth + 3 := by
  have hsource :=
    detectorCounterTerminatingCounterModeGates_length_le tail counterWidth
  unfold detectorCounterControlledTerminatingCounterModeGates
  calc
    _ ≤ 3 *
        (detectorCounterTerminatingCounterModeGates
          tail.succ counterWidth).length :=
      EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
        (detectorCounterCompareBit tail.succ counterWidth)
        (detectorCounterComparisonCarryBit tail.succ counterWidth
          (Fin.last tail))
        (detectorCounterTerminatingCounterModeGates tail.succ counterWidth)
        (detectorCounterTerminatingCounterModeGates_bitDisjoint_compare
          tail.succ counterWidth)
        (detectorCounterTerminatingCounterModeGates_bitDisjoint_comparisonCarry
          tail.succ counterWidth (Fin.last tail))
        (detectorCounterCompareBit_comparisonCarryBit_wire_ne
          tail.succ counterWidth (Fin.last tail))
    _ ≤ 24 * counterWidth + 3 := by omega

private theorem
    detectorCounterActiveFalseControlledInactivePaddingGates_length_le
    (tail counterWidth : Nat) :
    (detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth).length ≤ 24 * counterWidth + 2 := by
  have hpadding :
      (detectorCounterInactivePaddingGates tail.succ counterWidth).length ≤
        8 * counterWidth := by
    simpa only [detectorCounterInactivePaddingGates] using
      (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length_le
        (detectorCounterIncrementLayout tail.succ counterWidth))
  have hcontrolled :
      (EncodedBit.GateSpec.controlledListWithWorkGates
        (detectorCounterActiveBit tail.succ counterWidth)
        (detectorCounterComparisonCarryBit tail.succ counterWidth
          (Fin.last tail))
        (detectorCounterInactivePaddingGates tail.succ counterWidth)
        (detectorCounterInactivePaddingGates_bitDisjoint_active
          tail.succ counterWidth)
        (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
          tail.succ counterWidth (Fin.last tail))
        (detectorCounterActiveBit_comparisonCarryBit_wire_ne
          tail.succ counterWidth (Fin.last tail))).length ≤
        3 *
          (detectorCounterInactivePaddingGates
            tail.succ counterWidth).length :=
    EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
      (detectorCounterActiveBit tail.succ counterWidth)
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail))
      (detectorCounterInactivePaddingGates tail.succ counterWidth)
      (detectorCounterInactivePaddingGates_bitDisjoint_active
        tail.succ counterWidth)
      (detectorCounterInactivePaddingGates_bitDisjoint_comparisonCarry
        tail.succ counterWidth (Fin.last tail))
      (detectorCounterActiveBit_comparisonCarryBit_wire_ne
        tail.succ counterWidth (Fin.last tail))
  simp only [detectorCounterActiveFalseControlledInactivePaddingGates,
    List.length_append, List.length_cons, List.length_nil]
  omega

private theorem inactivePaddingGates_length_le (tail counterWidth : Nat) :
    (inactivePaddingGates tail counterWidth).length ≤
      24 * counterWidth + 2 := by
  let detectorGates :
      List (EncodedBit.GateSpec
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
    detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth
  let fullRoundGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    detectorGates.map
      (EncodedBit.GateSpec.insertMiddle
        (coeffAdderWorkEncoding tail.succ))
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    fullRoundGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    (pathControlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).length ≤
      24 * counterWidth + 2
  calc
    _ = pathControlGates.length := by simp only [List.length_map]
    _ = pathGates.length := by
      simp only [pathControlGates, List.length_map]
    _ = fullRoundGates.length := by
      simp only [pathGates, List.length_map]
    _ = detectorGates.length := by
      simp only [fullRoundGates, List.length_map]
    _ ≤ 24 * counterWidth + 2 := by
      exact
        detectorCounterActiveFalseControlledInactivePaddingGates_length_le
          tail counterWidth

private theorem detectorCounterInactivePaddingGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterInactivePaddingGates tail.succ counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simpa only [detectorCounterInactivePaddingGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (detectorCounterIncrementLayout tail.succ counterWidth))

private theorem detectorCounterInactivePaddingGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterInactivePaddingGates tail.succ counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * counterWidth := by
  simpa only [detectorCounterInactivePaddingGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (detectorCounterIncrementLayout tail.succ counterWidth))

private theorem detectorCounterInactivePaddingGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterInactivePaddingGates tail.succ counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      6 * (counterWidth - 1) := by
  simpa only [detectorCounterInactivePaddingGates] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (detectorCounterIncrementLayout tail.succ counterWidth))

private theorem
    detectorCounterActiveFalseControlledInactivePaddingGates_xMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterActiveFalseControlledInactivePaddingGates
        tail counterWidth).map EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp only [detectorCounterActiveFalseControlledInactivePaddingGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum,
    EncodedBit.GateSpec.xMultiplicity_x]
  omega

private theorem
    detectorCounterActiveFalseControlledInactivePaddingGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterActiveFalseControlledInactivePaddingGates
        tail counterWidth).map EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [detectorCounterActiveFalseControlledInactivePaddingGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    detectorCounterInactivePaddingGates_xMultiplicity_sum,
    EncodedBit.GateSpec.cnotMultiplicity_x]
  omega

private theorem
    detectorCounterActiveFalseControlledInactivePaddingGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((detectorCounterActiveFalseControlledInactivePaddingGates
        tail counterWidth).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * counterWidth + 18 * (counterWidth - 1) := by
  simp only [detectorCounterActiveFalseControlledInactivePaddingGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    detectorCounterInactivePaddingGates_cnotMultiplicity_sum,
    detectorCounterInactivePaddingGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_x]
  omega

private theorem inactivePaddingGates_events_eq_source
    (tail counterWidth : Nat) :
    (inactivePaddingGates tail counterWidth).map EncodedBit.GateSpec.event =
      (detectorCounterActiveFalseControlledInactivePaddingGates
        tail counterWidth).map EncodedBit.GateSpec.event := by
  let detectorGates :
      List (EncodedBit.GateSpec
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
    detectorCounterActiveFalseControlledInactivePaddingGates
      tail counterWidth
  let fullRoundGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    detectorGates.map
      (EncodedBit.GateSpec.insertMiddle
        (coeffAdderWorkEncoding tail.succ))
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    fullRoundGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    ((pathControlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).map
          EncodedBit.GateSpec.event) =
      detectorGates.map EncodedBit.GateSpec.event
  calc
    _ = pathControlGates.map EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft
        (wordEncoding (2 * tail.succ)) pathControlGates
    _ = pathGates.map EncodedBit.GateSpec.event := by
      simpa only [pathControlGates] using
        (EncodedBit.GateSpec.map_event_prodLeft
          BinaryLabelEncoding.bool pathGates)
    _ = fullRoundGates.map EncodedBit.GateSpec.event := by
      simpa only [pathGates] using
        (EncodedBit.GateSpec.map_event_prodLeft
          BinaryLabelEncoding.bool fullRoundGates)
    _ = detectorGates.map EncodedBit.GateSpec.event := by
      simp only [fullRoundGates, List.map_map]
      apply List.map_congr_left
      intro gate _
      exact
        event_insertMiddleGateSpec (coeffAdderWorkEncoding tail.succ) gate

private theorem inactivePaddingGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((inactivePaddingGates tail counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  calc
    _ = ((detectorCounterActiveFalseControlledInactivePaddingGates
          tail counterWidth).map EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        (inactivePaddingGates_events_eq_source tail counterWidth)
    _ = 0 :=
      detectorCounterActiveFalseControlledInactivePaddingGates_cnotMultiplicity_sum
        tail counterWidth

private theorem inactivePaddingGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((inactivePaddingGates tail counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * counterWidth + 18 * (counterWidth - 1) := by
  calc
    _ = ((detectorCounterActiveFalseControlledInactivePaddingGates
          tail counterWidth).map EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        (inactivePaddingGates_events_eq_source tail counterWidth)
    _ = 2 * counterWidth + 18 * (counterWidth - 1) :=
      detectorCounterActiveFalseControlledInactivePaddingGates_toffoliMultiplicity_sum
        tail counterWidth

private theorem detectorCounterVZeroDetectorGates_length
    (tail counterWidth : Nat) :
    (detectorCounterVZeroDetectorGates tail.succ counterWidth).length =
      4 * tail.succ + 1 := by
  simpa only [detectorCounterVZeroDetectorGates, List.length_map] using
    vZeroDetectorWithComparisonWorkGates_length tail counterWidth

private theorem detectorGatedTerminatingCounterModeWithWorkGates_length_le
    (tail counterWidth : Nat) :
    (detectorGatedTerminatingCounterModeWithWorkGates
      tail counterWidth).length ≤
      terminatingRouteGateLengthBound tail counterWidth := by
  have hdetector := detectorCounterVZeroDetectorGates_length tail counterWidth
  have hmode :=
    detectorCounterControlledTerminatingCounterModeGates_length_le
      tail counterWidth
  simp only [detectorGatedTerminatingCounterModeWithWorkGates,
    List.length_append, terminatingRouteGateLengthBound]
  omega

private theorem fullRoundWorkTerminatingStandardLayoutGates_length_le
    (tail counterWidth : Nat) :
    (fullRoundWorkTerminatingStandardLayoutGates tail counterWidth).length ≤
      terminatingRouteGateLengthBound tail counterWidth := by
  let detectorGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithComparisonWorkEncoding tail.succ counterWidth)
          (counterIncrementWorkEncoding counterWidth))) :=
    detectorGatedTerminatingCounterModeWithWorkGates tail counterWidth
  change
    (detectorGates.map
      (EncodedBit.GateSpec.insertMiddle
        (coeffAdderWorkEncoding tail.succ))).length ≤
      terminatingRouteGateLengthBound tail counterWidth
  calc
    _ = detectorGates.length := by simp only [List.length_map]
    _ ≤ terminatingRouteGateLengthBound tail counterWidth := by
      exact detectorGatedTerminatingCounterModeWithWorkGates_length_le
        tail counterWidth

private theorem fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_length_le
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex).length ≤
      activeRouteGateLengthBound tail counterWidth := by
  have hterminating :=
    fullRoundWorkTerminatingStandardLayoutGates_length_le
      tail counterWidth
  simp only [fullRoundWorkKaliskiActiveOnlyRoundConcreteGates,
    List.length_append,
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_length,
    activeRouteGateLengthBound]
  omega

private theorem liftedActiveOnlyGates_length_le
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    (liftedActiveOnlyGates tail counterWidth comparisonIndex
      historyIndex workIndex).length ≤
      activeRouteGateLengthBound tail counterWidth := by
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    (pathControlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).length ≤
      activeRouteGateLengthBound tail counterWidth
  calc
    _ = pathControlGates.length := by simp only [List.length_map]
    _ = pathGates.length := by
      simp only [pathControlGates, List.length_map]
    _ = baseGates.length := by
      simp only [pathGates, List.length_map]
    _ ≤ activeRouteGateLengthBound tail counterWidth := by
      exact fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_length_le
        tail counterWidth comparisonIndex historyIndex workIndex

private theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_xMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 * tail + 6 := by
  simp only [fullRoundWorkKaliskiActiveOnlyRoundConcreteGates,
    List.map_append, List.sum_append,
    fullRoundWorkTerminatingStandardLayoutGates_xMultiplicity_sum,
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_xMultiplicity_sum]
  omega

private theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 4 * tail + 19 := by
  simp only [fullRoundWorkKaliskiActiveOnlyRoundConcreteGates,
    List.map_append, List.sum_append,
    fullRoundWorkTerminatingStandardLayoutGates_cnotMultiplicity_sum,
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_cnotMultiplicity_sum]
  omega

private theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      370 * tail + 2 * counterWidth + 18 * (counterWidth - 1) + 260 := by
  simp only [fullRoundWorkKaliskiActiveOnlyRoundConcreteGates,
    List.map_append, List.sum_append,
    fullRoundWorkTerminatingStandardLayoutGates_toffoliMultiplicity_sum,
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_toffoliMultiplicity_sum]
  omega

private theorem liftedActiveOnlyGates_events_eq_source
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    (liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.event =
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
        tail counterWidth comparisonIndex historyIndex workIndex).map
          EncodedBit.GateSpec.event := by
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
      tail counterWidth comparisonIndex historyIndex workIndex
  let pathGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  let pathControlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (registersWithFullRoundWorkEncoding tail.succ counterWidth)
            BinaryLabelEncoding.bool)
          BinaryLabelEncoding.bool)) :=
    pathGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    ((pathControlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).map
          EncodedBit.GateSpec.event) =
      baseGates.map EncodedBit.GateSpec.event
  calc
    _ = pathControlGates.map EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft
        (wordEncoding (2 * tail.succ)) pathControlGates
    _ = pathGates.map EncodedBit.GateSpec.event := by
      simpa only [pathControlGates] using
        (EncodedBit.GateSpec.map_event_prodLeft
          BinaryLabelEncoding.bool pathGates)
    _ = baseGates.map EncodedBit.GateSpec.event := by
      simpa only [pathGates] using
        (EncodedBit.GateSpec.map_event_prodLeft
          BinaryLabelEncoding.bool baseGates)

private theorem liftedActiveOnlyGates_xMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.xMultiplicity).sum =
      4 * tail + 6 := by
  calc
    _ = ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
          tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum :=
      EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        (liftedActiveOnlyGates_events_eq_source tail counterWidth
          comparisonIndex historyIndex workIndex)
    _ = 4 * tail + 6 :=
      fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_xMultiplicity_sum
        tail counterWidth comparisonIndex historyIndex workIndex

private theorem liftedActiveOnlyGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.cnotMultiplicity).sum =
      4 * tail + 19 := by
  calc
    _ = ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
          tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        (liftedActiveOnlyGates_events_eq_source tail counterWidth
          comparisonIndex historyIndex workIndex)
    _ = 4 * tail + 19 :=
      fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_cnotMultiplicity_sum
        tail counterWidth comparisonIndex historyIndex workIndex

private theorem liftedActiveOnlyGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((liftedActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      370 * tail + 2 * counterWidth + 18 * (counterWidth - 1) + 260 := by
  calc
    _ = ((fullRoundWorkKaliskiActiveOnlyRoundConcreteGates
          tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        (liftedActiveOnlyGates_events_eq_source tail counterWidth
          comparisonIndex historyIndex workIndex)
    _ = 370 * tail + 2 * counterWidth +
        18 * (counterWidth - 1) + 260 :=
      fullRoundWorkKaliskiActiveOnlyRoundConcreteGates_toffoliMultiplicity_sum
        tail counterWidth comparisonIndex historyIndex workIndex

private theorem controlledActiveOnlyGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((controlledActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.cnotMultiplicity).sum =
      4 * tail + 6 := by
  unfold controlledActiveOnlyGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    liftedActiveOnlyGates_xMultiplicity_sum]

private theorem controlledActiveOnlyGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((controlledActiveOnlyGates tail counterWidth comparisonIndex historyIndex
      workIndex).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      1114 * tail + 6 * counterWidth +
        54 * (counterWidth - 1) + 799 := by
  unfold controlledActiveOnlyGates
  rw [EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    liftedActiveOnlyGates_cnotMultiplicity_sum,
    liftedActiveOnlyGates_toffoliMultiplicity_sum]
  omega

private theorem controlledActiveOnlyGates_length_le
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    (controlledActiveOnlyGates tail counterWidth comparisonIndex
      historyIndex workIndex).length ≤
      3 * activeRouteGateLengthBound tail counterWidth := by
  have hsource := liftedActiveOnlyGates_length_le
    tail counterWidth comparisonIndex historyIndex workIndex
  unfold controlledActiveOnlyGates
  calc
    _ ≤ 3 *
        (liftedActiveOnlyGates tail counterWidth comparisonIndex
          historyIndex workIndex).length :=
      EncodedBit.GateSpec.controlledListWithWorkGates_length_le_three_mul
        (workingPathBit tail counterWidth)
        (workingControlBit tail counterWidth)
        (liftedActiveOnlyGates tail counterWidth comparisonIndex
          historyIndex workIndex)
        (liftedActiveOnlyGates_bitDisjoint_path tail counterWidth
          comparisonIndex historyIndex workIndex)
        (liftedActiveOnlyGates_bitDisjoint_controlWork tail counterWidth
          comparisonIndex historyIndex workIndex)
        (workingPathBit_workingControlBit_wire_ne tail counterWidth)
    _ ≤ 3 * activeRouteGateLengthBound tail counterWidth := by omega

private theorem originalActiveLatchGates_length (tail counterWidth : Nat) :
    (originalActiveLatchGates tail counterWidth).length = 1 := by
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)) :=
    fullRoundPathWorkOriginalActiveLatchGates tail counterWidth
  let controlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    (controlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).length = 1
  calc
    _ = controlGates.length := by simp only [List.length_map]
    _ = baseGates.length := by
      simp only [controlGates, List.length_map]
    _ = 1 := by rfl

private theorem branchResidueCleanupGates_length
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (branchResidueCleanupGates tail counterWidth roundIndex).length = 6 := by
  rfl

private theorem spillWorkingPathGates_length
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (spillWorkingPathGates tail counterWidth roundIndex).length = 1 := by
  rfl

private theorem resetWorkingPathGates_length
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (resetWorkingPathGates tail counterWidth roundIndex).length = 1 := by
  rfl

private theorem originalActiveLatchGates_events_eq_source
    (tail counterWidth : Nat) :
    (originalActiveLatchGates tail counterWidth).map
        EncodedBit.GateSpec.event =
      (fullRoundPathWorkOriginalActiveLatchGates tail counterWidth).map
        EncodedBit.GateSpec.event := by
  let baseGates :
      List (EncodedBit.GateSpec
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)) :=
    fullRoundPathWorkOriginalActiveLatchGates tail counterWidth
  let controlGates :
      List (EncodedBit.GateSpec
        (BinaryLabelEncoding.prod
          (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
          BinaryLabelEncoding.bool)) :=
    baseGates.map
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)
  change
    ((controlGates.map
      (EncodedBit.GateSpec.prodLeft
        (wordEncoding (2 * tail.succ)))).map
          EncodedBit.GateSpec.event) =
      baseGates.map EncodedBit.GateSpec.event
  calc
    _ = controlGates.map EncodedBit.GateSpec.event :=
      EncodedBit.GateSpec.map_event_prodLeft
        (wordEncoding (2 * tail.succ)) controlGates
    _ = baseGates.map EncodedBit.GateSpec.event := by
      simpa only [controlGates] using
        (EncodedBit.GateSpec.map_event_prodLeft
          BinaryLabelEncoding.bool baseGates)

private theorem originalActiveLatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) :
    ((originalActiveLatchGates tail counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  calc
    _ = ((fullRoundPathWorkOriginalActiveLatchGates
          tail counterWidth).map EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        (originalActiveLatchGates_events_eq_source tail counterWidth)
    _ = 1 := by
      simp [fullRoundPathWorkOriginalActiveLatchGates,
        fullRoundPathWorkOriginalActiveLatchGate]

private theorem originalActiveLatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) :
    ((originalActiveLatchGates tail counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  calc
    _ = ((fullRoundPathWorkOriginalActiveLatchGates
          tail counterWidth).map EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        (originalActiveLatchGates_events_eq_source tail counterWidth)
    _ = 0 := by
      simp [fullRoundPathWorkOriginalActiveLatchGates,
        fullRoundPathWorkOriginalActiveLatchGate]

private theorem branchResidueCleanupGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((branchResidueCleanupGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 4 := by
  simp [branchResidueCleanupGates]

private theorem branchResidueCleanupGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((branchResidueCleanupGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  simp [branchResidueCleanupGates]

private theorem spillWorkingPathGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((spillWorkingPathGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [spillWorkingPathGates, spillWorkingPathGate]

private theorem spillWorkingPathGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((spillWorkingPathGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [spillWorkingPathGates, spillWorkingPathGate]

private theorem resetWorkingPathGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((resetWorkingPathGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [resetWorkingPathGates, resetWorkingPathGate]

private theorem resetWorkingPathGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    ((resetWorkingPathGates tail counterWidth roundIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [resetWorkingPathGates, resetWorkingPathGate]

/-- Exact CNOT coordinate of one physical six-stage round. -/
theorem roundGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    ((roundGates tail counterWidth comparisonIndex workIndex roundIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 4 * tail + 13 := by
  simp only [roundGates, List.map_append, List.sum_append,
    originalActiveLatchGates_cnotMultiplicity_sum,
    inactivePaddingGates_cnotMultiplicity_sum,
    controlledActiveOnlyGates_cnotMultiplicity_sum,
    branchResidueCleanupGates_cnotMultiplicity_sum,
    spillWorkingPathGates_cnotMultiplicity_sum,
    resetWorkingPathGates_cnotMultiplicity_sum]
  omega

/-- Exact Toffoli coordinate of one physical six-stage round. -/
theorem roundGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    ((roundGates tail counterWidth comparisonIndex workIndex roundIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      1114 * tail + 8 * counterWidth +
        72 * (counterWidth - 1) + 801 := by
  simp only [roundGates, List.map_append, List.sum_append,
    originalActiveLatchGates_toffoliMultiplicity_sum,
    inactivePaddingGates_toffoliMultiplicity_sum,
    controlledActiveOnlyGates_toffoliMultiplicity_sum,
    branchResidueCleanupGates_toffoliMultiplicity_sum,
    spillWorkingPathGates_toffoliMultiplicity_sum,
    resetWorkingPathGates_toffoliMultiplicity_sum]
  omega

/-- Every static round has the declared width-only primitive-leaf bound. -/
theorem roundGates_length_le
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    (roundGates tail counterWidth comparisonIndex workIndex roundIndex).length ≤
      roundGateLengthBound tail counterWidth := by
  have hlatch := originalActiveLatchGates_length tail counterWidth
  have hinactive := inactivePaddingGates_length_le tail counterWidth
  have hactive := controlledActiveOnlyGates_length_le tail counterWidth
    comparisonIndex roundIndex workIndex
  have hcleanup := branchResidueCleanupGates_length
    tail counterWidth roundIndex
  have hspill := spillWorkingPathGates_length tail counterWidth roundIndex
  have hreset := resetWorkingPathGates_length tail counterWidth roundIndex
  simp only [roundGates, List.length_append, roundGateLengthBound]
  omega

/-- The one-round program ledger.  Its order is the physical order: latch the
original active flag, perform inactive padding, run the complete active route
under that latch, clean branch residue, spill the latch, then reset it. -/
def roundPrograms (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    List (UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width)) :=
  [ originalActiveLatchProgram tail counterWidth
  , inactivePaddingProgram tail counterWidth
  , controlledActiveOnlyProgram tail counterWidth comparisonIndex
      roundIndex workIndex
  , branchResidueCleanupProgram tail counterWidth roundIndex
  , spillWorkingPathProgram tail counterWidth roundIndex
  , resetWorkingPathProgram tail counterWidth roundIndex ]

/-- Exact structured steps corresponding one-for-one to `roundPrograms`. -/
def roundSteps (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    List (RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth) :=
  [ originalActiveLatchStep tail counterWidth
  , inactivePaddingStep tail counterWidth
  , controlledActiveOnlyStep tail counterWidth comparisonIndex
      roundIndex workIndex
  , branchResidueCleanupStep tail counterWidth roundIndex
  , spillWorkingPathStep tail counterWidth roundIndex
  , resetWorkingPathStep tail counterWidth roundIndex ]

/-- Each actual stage circuit realizes the corresponding structured step. -/
theorem roundSchedules_forall₂_realizes
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    List.Forall₂
      (fun program step =>
        UnitaryCircuit.Realizes (encoding tail.succ counterWidth) program step)
      (roundPrograms tail counterWidth comparisonIndex workIndex roundIndex)
      (roundSteps tail counterWidth comparisonIndex workIndex roundIndex) := by
  exact List.Forall₂.cons
    (originalActiveLatch_realizes tail counterWidth)
    (List.Forall₂.cons
      (inactivePadding_realizes tail counterWidth)
      (List.Forall₂.cons
        (controlledActiveOnly_realizes tail counterWidth comparisonIndex
          roundIndex workIndex)
        (List.Forall₂.cons
          (branchResidueCleanup_realizes tail counterWidth roundIndex)
          (List.Forall₂.cons
            (spillWorkingPath_realizes tail counterWidth roundIndex)
            (List.Forall₂.cons
              (resetWorkingPath_realizes tail counterWidth roundIndex)
              List.Forall₂.nil)))))

/-- One actual circuit for the complete six-stage round ledger. -/
def roundProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  (roundPrograms tail counterWidth comparisonIndex workIndex roundIndex).foldr
    UnitaryCircuit.seq
    (UnitaryCircuit.identity (Qubits (encoding tail.succ counterWidth).width)
      [] (by simp))

/-- Structured action realized by the complete six-stage round ledger. -/
def roundStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    (roundSteps tail counterWidth comparisonIndex workIndex roundIndex)

theorem roundStep_eq_stages
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    roundStep tail counterWidth comparisonIndex workIndex roundIndex x =
      resetWorkingPathStep tail counterWidth roundIndex
        (spillWorkingPathStep tail counterWidth roundIndex
          (branchResidueCleanupStep tail counterWidth roundIndex
            (controlledActiveOnlyStep tail counterWidth comparisonIndex
              roundIndex workIndex
              (inactivePaddingStep tail counterWidth
                (originalActiveLatchStep tail counterWidth x))))) := by
  rfl

/-- The primitive source list for one round has exactly the established
six-stage semantic action. -/
theorem roundGates_stepList_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (roundGates tail counterWidth comparisonIndex workIndex roundIndex) x =
      roundStep tail counterWidth comparisonIndex workIndex roundIndex x := by
  unfold roundGates roundStep roundSteps
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [originalActiveLatchGates_stepList_eq]
  rw [inactivePaddingGates_stepList_eq]
  rfl

/-- Direct compilation of the one-round primitive source list realizes the
same semantic action as the established six-stage actual circuit. -/
theorem roundGates_realizes
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (roundGates tail counterWidth comparisonIndex workIndex roundIndex))
      (roundStep tail counterWidth comparisonIndex workIndex roundIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (roundGates tail counterWidth comparisonIndex workIndex roundIndex)
    (roundGates_stepList_eq tail counterWidth comparisonIndex workIndex
      roundIndex)

/-- The established actual round circuit has exactly the strict primitive
event trace of its complete source list. -/
theorem roundProgram_eventTrace
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    (roundProgram tail counterWidth comparisonIndex workIndex roundIndex).eventTrace =
      (roundGates tail counterWidth comparisonIndex workIndex roundIndex).map
        EncodedBit.GateSpec.event := by
  simp [roundProgram, roundPrograms, roundGates,
    originalActiveLatchProgram_eventTrace,
    inactivePaddingProgram_eventTrace,
    controlledActiveOnlyProgram, branchResidueCleanupProgram,
    spillWorkingPathProgram, resetWorkingPathProgram]

theorem roundStep_eq_structured_of_clean
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hwork : (workingControlBit tail counterWidth).get x = false) :
    roundStep tail counterWidth comparisonIndex workIndex roundIndex
        x =
      roundStructuredStep tail counterWidth comparisonIndex workIndex
        roundIndex x := by
  have hworkPadded :
      (workingControlBit tail counterWidth).get
          (inactivePaddingStep tail counterWidth
            (originalActiveLatchStep tail counterWidth x)) = false := by
    change x.1.2 = false
    change x.1.2 = false at hwork
    exact hwork
  rw [roundStep_eq_stages]
  rw [controlledActiveOnlyStep_eq_semantic_of_clean
    tail counterWidth comparisonIndex roundIndex workIndex _ hworkPadded]
  rfl

set_option maxHeartbeats 800000 in
-- The six-way physical branch dispatch normalizes the entire round boundary record.
/-- One encoded fixed round reaches the exact clean physical/source boundary.
The proof dispatches over the six source branches, certifies their raw physical
residue, and then applies the common reversible cleanup suffix. -/
theorem roundStep_cleanBoundary
    (tail counterWidth modulus : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (source : RoundState)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (hinput : RoundCleanInput tail counterWidth roundIndex x)
    (hsource : RoundState.fromRegisters tail.succ counterWidth
      (dataRegisters tail counterWidth x) source.kaliskiSteps
      source.paddingSteps = source)
    (hcounter : (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus source)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x)) :
    ∃ after : RegistersWithRouteHistory tail.succ counterWidth,
      roundStep tail counterWidth comparisonIndex workIndex roundIndex
          x = after ∧
      RoundCleanBoundary tail counterWidth roundIndex source x after := by
  let routed :=
    routedStepBeforeCleanup tail counterWidth comparisonIndex roundIndex
      workIndex x
  have hbezoutInput :
      RoundState.BezoutInvariant modulus
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x) source.kaliskiSteps
          source.paddingSteps) := by
    simpa only [hsource] using hbezout
  have hrouted :
      BranchResidueCertificate tail counterWidth roundIndex routed ∧
        ReusableWorkspaceClean tail counterWidth routed ∧
        RoutedPersistentBoundary tail counterWidth roundIndex source x
          routed := by
    cases hactive : (dataRegisters tail counterWidth x).active with
    | false =>
        exact
          ⟨routedStepBeforeCleanup_inactive_residueCertificate
              tail counterWidth comparisonIndex roundIndex workIndex x hinput
              hactive,
            routedStepBeforeCleanup_inactive_reusableWorkspaceClean
              tail counterWidth comparisonIndex roundIndex workIndex x hinput
              hactive,
            routedStepBeforeCleanup_inactive_persistentBoundary
              tail counterWidth comparisonIndex roundIndex workIndex source x
              hinput hsource hcounter hactive⟩
    | true =>
        by_cases hvZero : (dataRegisters tail counterWidth x).v.val = 0
        · exact
            ⟨routedStepBeforeCleanup_active_terminated_residueCertificate
                tail counterWidth comparisonIndex roundIndex workIndex x
                hinput hactive hvZero,
              routedStepBeforeCleanup_active_terminated_reusableWorkspaceClean
                tail counterWidth comparisonIndex roundIndex workIndex x
                hinput hactive hvZero,
              routedStepBeforeCleanup_active_terminated_persistentBoundary
                tail counterWidth comparisonIndex roundIndex workIndex source
                x hinput hsource hcounter hactive hvZero⟩
        · have hvNonzero :
              (dataRegisters tail counterWidth x).v.val ≠ 0 := hvZero
          cases huParity :
              (dataRegisters tail counterWidth x).u.val.testBit (0 : Nat) with
          | false =>
              exact
                ⟨routedStepBeforeCleanup_active_uEven_residueCertificate
                    tail counterWidth modulus source.kaliskiSteps
                    source.paddingSteps comparisonIndex roundIndex workIndex x
                    hinput hactive hvNonzero huParity hmodulusOdd hbezoutInput,
                  routedStepBeforeCleanup_active_uEven_reusableWorkspaceClean
                    tail counterWidth comparisonIndex roundIndex workIndex x
                    hinput hactive hvNonzero huParity,
                  routedStepBeforeCleanup_active_uEven_persistentBoundary
                    tail counterWidth comparisonIndex roundIndex workIndex
                    source x hinput hsource hcounter hactive hvNonzero
                    huParity hfinal arith⟩
          | true =>
              cases hvParity :
                  (dataRegisters tail counterWidth x).v.val.testBit
                    (0 : Nat) with
              | false =>
                  exact
                    ⟨routedStepBeforeCleanup_active_vEven_residueCertificate
                        tail counterWidth comparisonIndex roundIndex workIndex
                        x hinput hactive hvNonzero huParity hvParity arith,
                      routedStepBeforeCleanup_active_vEven_reusableWorkspaceClean
                        tail counterWidth comparisonIndex roundIndex workIndex
                        x hinput hactive hvNonzero huParity hvParity,
                      routedStepBeforeCleanup_active_vEven_persistentBoundary
                        tail counterWidth comparisonIndex roundIndex workIndex
                        source x hinput hsource hcounter hactive hvNonzero
                        huParity hvParity hfinal arith⟩
              | true =>
                  by_cases hlt :
                      (dataRegisters tail counterWidth x).v.val <
                        (dataRegisters tail counterWidth x).u.val
                  · exact
                      ⟨routedStepBeforeCleanup_active_uGreater_residueCertificate
                          tail counterWidth modulus source.kaliskiSteps
                          source.paddingSteps comparisonIndex roundIndex
                          workIndex x hinput hactive hvNonzero huParity
                          hvParity hlt hfinal hmodulusOdd hbezoutInput arith,
                        routedStepBeforeCleanup_active_odd_reusableWorkspaceClean
                          tail counterWidth comparisonIndex roundIndex
                          workIndex x hinput hactive hvNonzero huParity hvParity
                          hfinal,
                        routedStepBeforeCleanup_active_uGreater_persistentBoundary
                          tail counterWidth comparisonIndex roundIndex
                          workIndex source x hinput hsource hcounter hactive
                          hvNonzero huParity hvParity hlt hfinal arith⟩
                  · exact
                      ⟨routedStepBeforeCleanup_active_vLe_residueCertificate
                          tail counterWidth comparisonIndex roundIndex workIndex
                          x hinput hactive hvNonzero huParity hvParity hlt
                          hfinal arith,
                        routedStepBeforeCleanup_active_odd_reusableWorkspaceClean
                          tail counterWidth comparisonIndex roundIndex
                          workIndex x hinput hactive hvNonzero huParity hvParity
                          hfinal,
                        routedStepBeforeCleanup_active_vLe_persistentBoundary
                          tail counterWidth comparisonIndex roundIndex
                          workIndex source x hinput hsource hcounter hactive
                          hvNonzero huParity hvParity hlt hfinal arith⟩
  let after :=
    roundStructuredStep tail counterWidth comparisonIndex workIndex roundIndex x
  have hwork : (workingControlBit tail counterWidth).get x = false := by
    change x.1.2 = false
    rw [hinput.workspace]
    rfl
  refine ⟨after, ?_, ?_⟩
  · exact roundStep_eq_structured_of_clean tail counterWidth
      comparisonIndex workIndex roundIndex x hwork
  · exact roundStructuredStep_cleanBoundary_of_routed tail counterWidth
      comparisonIndex workIndex roundIndex source x hinput hsource hrouted.1
      hrouted.2.1 hrouted.2.2

theorem round_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes
      (encoding tail.succ counterWidth)
      (roundProgram tail counterWidth comparisonIndex workIndex roundIndex)
      (roundStep tail counterWidth comparisonIndex workIndex roundIndex) :=
  UnitaryCircuit.Realizes.appendList
    (encoding tail.succ counterWidth)
    (roundPrograms tail counterWidth comparisonIndex workIndex roundIndex)
    (roundSteps tail counterWidth comparisonIndex workIndex roundIndex)
    (roundSchedules_forall₂_realizes tail counterWidth comparisonIndex
      workIndex roundIndex)

/-- The established actual round program and the directly compiled primitive
source list agree on every encoded basis state. -/
theorem roundProgram_gateList_applyNormalized_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (roundProgram tail counterWidth comparisonIndex workIndex roundIndex).applyNormalized
        (NormalizedVector.ket
          ((encoding tail.succ counterWidth).encode x)) =
      (EncodedBit.GateSpec.programList
        (roundGates tail counterWidth comparisonIndex workIndex roundIndex)).applyNormalized
          (NormalizedVector.ket
            ((encoding tail.succ counterWidth).encode x)) := by
  rw [(round_realizes tail counterWidth comparisonIndex workIndex
    roundIndex).apply_encoded_ket]
  rw [(roundGates_realizes tail counterWidth comparisonIndex workIndex
    roundIndex).apply_encoded_ket]

/-! ## Input-independent `2n` fold and physical inverse -/

/-- Statically indexed list of the `2n` complete round programs. -/
def foldPrograms (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width)) :=
  List.ofFn fun roundIndex : Fin (2 * tail.succ) =>
    roundProgram tail counterWidth comparisonIndex workIndex roundIndex

@[simp] theorem foldPrograms_length (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
  (foldPrograms tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [foldPrograms]
  omega

/-- Statically indexed list of the `2n` complete structured round actions. -/
def foldSteps (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth) :=
  List.ofFn fun roundIndex : Fin (2 * tail.succ) =>
    roundStep tail counterWidth comparisonIndex workIndex roundIndex

/-- Complete primitive source list for the input-independent fixed-round
fold, flattened in increasing round-index order. -/
def foldGates (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex).flatMap
    (roundGates tail counterWidth comparisonIndex workIndex)

private theorem flatMap_roundGates_length_le
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ roundIndices : List (Fin (2 * tail.succ)),
      (roundIndices.flatMap
        (roundGates tail counterWidth comparisonIndex workIndex)).length ≤
        roundIndices.length * roundGateLengthBound tail counterWidth
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hround := roundGates_length_le tail counterWidth comparisonIndex
        workIndex roundIndex
      have hrest := flatMap_roundGates_length_le tail counterWidth
        comparisonIndex workIndex rest
      calc
        (roundGates tail counterWidth comparisonIndex workIndex roundIndex).length +
            (rest.flatMap
              (roundGates tail counterWidth comparisonIndex workIndex)).length ≤
            roundGateLengthBound tail counterWidth +
              rest.length * roundGateLengthBound tail counterWidth :=
          Nat.add_le_add hround hrest
        _ = rest.length.succ * roundGateLengthBound tail counterWidth := by
          calc
            roundGateLengthBound tail counterWidth +
                rest.length * roundGateLengthBound tail counterWidth =
                rest.length * roundGateLengthBound tail counterWidth +
                  roundGateLengthBound tail counterWidth := Nat.add_comm _ _
            _ = rest.length.succ * roundGateLengthBound tail counterWidth :=
              (Nat.succ_mul rest.length
                (roundGateLengthBound tail counterWidth)).symm

/-- The input-independent fixed fold has the declared width-only
primitive-leaf bound. -/
theorem foldGates_length_le (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (foldGates tail counterWidth comparisonIndex workIndex).length ≤
      foldGateLengthBound tail counterWidth := by
  have h := flatMap_roundGates_length_le tail counterWidth comparisonIndex
    workIndex
    (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex)
  simpa only [foldGates, foldGateLengthBound, List.length_ofFn] using h

private theorem flatMap_roundGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ roundIndices : List (Fin (2 * tail.succ)),
      (((roundIndices.flatMap
          (roundGates tail counterWidth comparisonIndex workIndex)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum) =
        roundIndices.length * (4 * tail + 13)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons, roundGates_cnotMultiplicity_sum,
        flatMap_roundGates_cnotMultiplicity_sum tail counterWidth
          comparisonIndex workIndex rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

private theorem flatMap_roundGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ roundIndices : List (Fin (2 * tail.succ)),
      (((roundIndices.flatMap
          (roundGates tail counterWidth comparisonIndex workIndex)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum) =
        roundIndices.length *
          (1114 * tail + 8 * counterWidth +
            72 * (counterWidth - 1) + 801)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons, roundGates_toffoliMultiplicity_sum,
        flatMap_roundGates_toffoliMultiplicity_sum tail counterWidth
          comparisonIndex workIndex rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Exact CNOT coordinate of the fixed `2(t+1)`-round gate list. -/
theorem foldGates_cnotMultiplicity_sum (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ((foldGates tail counterWidth comparisonIndex workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * tail.succ * (4 * tail + 13) := by
  have h := flatMap_roundGates_cnotMultiplicity_sum tail counterWidth
    comparisonIndex workIndex
    (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex)
  simpa only [foldGates, List.length_ofFn] using h

/-- Exact Toffoli coordinate of the fixed `2(t+1)`-round gate list. -/
theorem foldGates_toffoliMultiplicity_sum (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ((foldGates tail counterWidth comparisonIndex workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * tail.succ *
        (1114 * tail + 8 * counterWidth +
          72 * (counterWidth - 1) + 801) := by
  have h := flatMap_roundGates_toffoliMultiplicity_sum tail counterWidth
    comparisonIndex workIndex
    (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex)
  simpa only [foldGates, List.length_ofFn] using h

@[simp] theorem foldSteps_length (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
  (foldSteps tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [foldSteps]
  omega

theorem foldSteps_get (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    (foldSteps tail counterWidth comparisonIndex workIndex).get
        ⟨roundIndex.val, by
          rw [foldSteps_length]
          exact roundIndex.isLt⟩ =
      roundStep tail counterWidth comparisonIndex workIndex roundIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (2 * tail.succ) =>
        roundStep tail counterWidth comparisonIndex workIndex roundIndex)).get
        ⟨roundIndex.val, by
          simp
          omega⟩ =
      roundStep tail counterWidth comparisonIndex workIndex roundIndex
  rw [List.get_ofFn]
  congr 1

/-- Fixed-width relation used during schedule induction. -/
abbrev FoldRealizesRelation (tail counterWidth : Nat)
    (program : UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width))
    (step : RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth) :
    Prop :=
  UnitaryCircuit.Realizes
    (encoding tail.succ counterWidth)
    program step

/-- The static program and named semantic schedules agree pointwise through
the one-round realization theorem. -/
theorem foldSchedules_forall₂_realizes
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List.Forall₂
      (FoldRealizesRelation tail counterWidth)
      (foldPrograms tail counterWidth comparisonIndex workIndex)
      (foldSteps tail counterWidth comparisonIndex workIndex) := by
  apply List.forall₂_of_length_eq_of_get
  · rw [foldPrograms_length, foldSteps_length]
  · intro i hprogram hstep
    let roundIndex : Fin (2 * tail.succ) :=
      ⟨i, by
        rw [foldSteps_length] at hstep
        exact hstep⟩
    change
      FoldRealizesRelation tail counterWidth
        ((List.ofFn
          (fun roundIndex : Fin (2 * tail.succ) =>
            roundProgram tail counterWidth comparisonIndex workIndex
              roundIndex)).get ⟨i, hprogram⟩)
        ((List.ofFn
          (fun roundIndex : Fin (2 * tail.succ) =>
            roundStep tail counterWidth comparisonIndex workIndex
              roundIndex)).get ⟨i, hstep⟩)
    rw [List.get_ofFn, List.get_ofFn]
    unfold FoldRealizesRelation
    exact round_realizes tail counterWidth comparisonIndex workIndex roundIndex

/-- Actual circuit for the full fixed-round fold. -/
def foldProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  (foldPrograms tail counterWidth comparisonIndex workIndex).foldr
    UnitaryCircuit.seq
    (UnitaryCircuit.identity (Qubits (encoding tail.succ counterWidth).width)
      [] (by simp))

private theorem foldrSeq_roundPrograms_eventTrace
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ (roundIndices : List (Fin (2 * tail.succ))),
      ((roundIndices.map
          (roundProgram tail counterWidth comparisonIndex workIndex)).foldr
        UnitaryCircuit.seq
        (UnitaryCircuit.identity (Qubits (encoding tail.succ counterWidth).width)
          [] (by simp))).eventTrace =
        (roundIndices.flatMap
          (roundGates tail counterWidth comparisonIndex workIndex)).map
          EncodedBit.GateSpec.event
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.map_cons, List.foldr_cons, UnitaryCircuit.seq_eventTrace,
        List.flatMap_cons, List.map_append]
      rw [roundProgram_eventTrace,
        foldrSeq_roundPrograms_eventTrace tail counterWidth comparisonIndex
          workIndex rest]

/-- The established actual fold circuit has exactly the strict primitive
event trace of its flattened source list. -/
theorem foldProgram_eventTrace (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (foldProgram tail counterWidth comparisonIndex workIndex).eventTrace =
      (foldGates tail counterWidth comparisonIndex workIndex).map
        EncodedBit.GateSpec.event := by
  simpa only [foldProgram, foldPrograms, foldGates, List.map_ofFn,
    Function.comp_def] using
    foldrSeq_roundPrograms_eventTrace tail counterWidth comparisonIndex
      workIndex
      (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex)

/-- The production fold event pool is therefore exactly the one compiled
from its flattened primitive source list. -/
theorem foldProgram_eventCost_eq_gateList (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (foldProgram tail counterWidth comparisonIndex workIndex).eventCost =
      (EncodedBit.GateSpec.programList
        (foldGates tail counterWidth comparisonIndex workIndex)).eventCost := by
  calc
    (foldProgram tail counterWidth comparisonIndex workIndex).eventCost =
        ResourcePool.ofList
          (foldProgram tail counterWidth comparisonIndex workIndex).eventTrace := by
      symm
      exact UnitaryCircuit.ofList_eventTrace_eq_eventCost _
    _ = ResourcePool.ofList
          ((foldGates tail counterWidth comparisonIndex workIndex).map
            EncodedBit.GateSpec.event) := by
      rw [foldProgram_eventTrace]
    _ = (EncodedBit.GateSpec.programList
          (foldGates tail counterWidth comparisonIndex workIndex)).eventCost := by
      rw [← EncodedBit.GateSpec.programList_eventTrace]
      exact UnitaryCircuit.ofList_eventTrace_eq_eventCost _

/-- Structured action realized by the full fixed-round fold. -/
def foldStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    (foldSteps tail counterWidth comparisonIndex workIndex)

private theorem stepList_flatMap_roundGates
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ (roundIndices : List (Fin (2 * tail.succ)))
      (x : RegistersWithRouteHistory tail.succ counterWidth),
      EncodedBit.GateSpec.stepList
          (roundIndices.flatMap
            (roundGates tail counterWidth comparisonIndex workIndex)) x =
        UnitaryCircuit.Realizes.stepList
          (roundIndices.map
            (roundStep tail counterWidth comparisonIndex workIndex)) x
  | [], _ => rfl
  | roundIndex :: rest, x => by
      change
        EncodedBit.GateSpec.stepList
            (roundGates tail counterWidth comparisonIndex workIndex
              roundIndex ++
              rest.flatMap
                (roundGates tail counterWidth comparisonIndex workIndex)) x =
          UnitaryCircuit.Realizes.stepList
            (rest.map
              (roundStep tail counterWidth comparisonIndex workIndex))
            (roundStep tail counterWidth comparisonIndex workIndex
              roundIndex x)
      rw [EncodedBit.GateSpec.stepList_append]
      rw [roundGates_stepList_eq]
      exact stepList_flatMap_roundGates tail counterWidth comparisonIndex
        workIndex rest
        (roundStep tail counterWidth comparisonIndex workIndex roundIndex x)

/-- The flattened fixed-round primitive source list has exactly the
established input-independent fold action. -/
theorem foldStep_eq_gateList (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (foldGates tail counterWidth comparisonIndex workIndex) x =
      foldStep tail counterWidth comparisonIndex workIndex x := by
  simpa only [foldGates, foldStep, foldSteps, List.map_ofFn,
    Function.comp_def] using
    stepList_flatMap_roundGates tail counterWidth comparisonIndex workIndex
      (List.ofFn fun roundIndex : Fin (2 * tail.succ) => roundIndex) x

/-- Direct compilation of the fixed-round primitive source list realizes the
same semantic action as the established fold circuit. -/
theorem foldGates_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (foldGates tail counterWidth comparisonIndex workIndex))
      (foldStep tail counterWidth comparisonIndex workIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (foldGates tail counterWidth comparisonIndex workIndex)
    (foldStep_eq_gateList tail counterWidth comparisonIndex workIndex)

/-- Semantic action of a bounded prefix of the fixed physical round ledger. -/
def foldPrefix (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (rounds : Nat) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    ((foldSteps tail counterWidth comparisonIndex workIndex).take rounds)

@[simp] theorem foldPrefix_zero (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    foldPrefix tail counterWidth comparisonIndex workIndex 0 x = x := by
  rfl

theorem foldPrefix_succ (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    foldPrefix tail counterWidth comparisonIndex workIndex
        (roundIndex.val + 1) x =
      roundStep tail counterWidth comparisonIndex workIndex roundIndex
        (foldPrefix tail counterWidth comparisonIndex workIndex
          roundIndex.val x) := by
  unfold foldPrefix
  let schedule := foldSteps tail counterWidth comparisonIndex workIndex
  have hlen : roundIndex.val < schedule.length := by
    rw [foldSteps_length]
    exact roundIndex.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ
    schedule roundIndex.val hlen]
  have hget :
      schedule.get ⟨roundIndex.val, hlen⟩ =
        roundStep tail counterWidth comparisonIndex workIndex roundIndex := by
    simpa [schedule] using
      foldSteps_get tail counterWidth comparisonIndex workIndex roundIndex
  rw [hget]

theorem foldPrefix_full (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    foldPrefix tail counterWidth comparisonIndex workIndex (2 * tail.succ) =
      foldStep tail counterWidth comparisonIndex workIndex := by
  funext x
  unfold foldPrefix foldStep
  rw [List.take_of_length_le]
  rw [foldSteps_length]

/-- Inductive physical/source contract for a concrete prefix of the fixed
round ledger.  Written and fresh suffixes are tracked separately for both the
source branch history and the reversible route history. -/
structure CleanPrefixInvariant (tail counterWidth : Nat)
    (p input : Word tail.succ) (rounds : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth) : Prop where
  rounds_le : rounds ≤ 2 * tail.succ
  modulusOdd : p.val % 2 = 1
  clean : PhysicalWorkspaceClean tail counterWidth x
  source_eq :
    let source :=
      (Trace.ofInput tail.succ p.val input.val).prefixState rounds
    RoundState.fromRegisters tail.succ counterWidth
        (dataRegisters tail counterWidth x)
        source.kaliskiSteps source.paddingSteps = source
  counter_mod :
    let source :=
      (Trace.ofInput tail.succ p.val input.val).prefixState rounds
    (dataRegisters tail counterWidth x).counter.val =
      source.paddingSteps % 2 ^ counterWidth
  history_written :
    ∀ i : Fin (2 * tail.succ), i.val < rounds ->
      (RegisterBits.historyBit tail.succ counterWidth i).get
          (dataRegisters tail counterWidth x) =
        RoundState.historyBit
          ((Trace.ofInput tail.succ p.val input.val).prefixState i.val)
  history_fresh :
    ∀ i : Fin (2 * tail.succ), rounds ≤ i.val ->
      (RegisterBits.historyBit tail.succ counterWidth i).get
        (dataRegisters tail counterWidth x) = false
  route_written :
    ∀ i : Fin (2 * tail.succ), i.val < rounds ->
      (routeHistoryBit tail counterWidth i).get x =
        ((Trace.ofInput tail.succ p.val input.val).prefixState i.val).active
  route_fresh :
    ∀ i : Fin (2 * tail.succ), rounds ≤ i.val ->
      (routeHistoryBit tail counterWidth i).get x = false

/-- A clean routed prefix carries all arithmetic side conditions required by
the next concrete fixed-round step. -/
theorem cleanPrefixInvariant_arithmeticCertificate
    (tail counterWidth : Nat)
    (p input : Word tail.succ)
    (rounds : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (inv : CleanPrefixInvariant tail counterWidth p input rounds x) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      (dataRegisters tail counterWidth x) := by
  let trace := Trace.ofInput tail.succ p.val input.val
  let source := trace.prefixState rounds
  have hsource :
      RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x)
          source.kaliskiSteps source.paddingSteps = source := by
    simpa only [source, trace] using inv.source_eq
  have hpMod : p.val % 2 = 1 := inv.modulusOdd
  have hpPos : 0 < p.val := by
    omega
  have hsourceBezout : RoundState.BezoutInvariant p.val source := by
    change RoundState.BezoutInvariant p.val
      (RoundState.runRounds rounds (RoundState.initial p.val input.val))
    exact RoundState.runRounds_bezoutInvariant rounds p.val
      (RoundState.initial p.val input.val)
      (RoundState.initial_bezoutInvariant p.val input.val)
  have hregisterBezout :
      RoundState.BezoutInvariant p.val
        (RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x)
          source.kaliskiSteps source.paddingSteps) := by
    rw [hsource]
    exact hsourceBezout
  have hbezout :
      (dataRegisters tail counterWidth x).rCoeff.val *
            (dataRegisters tail counterWidth x).v.val +
          (dataRegisters tail counterWidth x).sCoeff.val *
            (dataRegisters tail counterWidth x).u.val =
        p.val := by
    simpa only [RoundState.BezoutInvariant, RoundState.bezoutValue,
      RoundState.fromRegisters] using hregisterBezout
  have hsourceUPos : 0 < source.u := by
    change 0 < (RoundState.runRounds rounds
      (RoundState.initial p.val input.val)).u
    exact RoundState.runRounds_u_pos_of_pos rounds
      (RoundState.initial p.val input.val) (by
        simpa [RoundState.initial] using hpPos)
  have huPos : 0 < (dataRegisters tail counterWidth x).u.val := by
    have hsourceU : (dataRegisters tail counterWidth x).u.val = source.u := by
      simpa only [RoundState.fromRegisters] using
        congrArg RoundState.u hsource
    rw [hsourceU]
    exact hsourceUPos
  exact modeControlledSemanticStepArithmeticCertificate_of_bezout_bound
    tail counterWidth p.val (dataRegisters tail counterWidth x) hbezout p.isLt
    (fun _ _ => Nat.ne_of_gt huPos)

/-- Stable accessor for a route slot already consumed by a clean prefix. -/
theorem routeHistoryBit_eq_originalActive
    (tail counterWidth : Nat) (p input : Word tail.succ)
    (rounds : Nat)
    (x : RegistersWithRouteHistory tail.succ counterWidth)
    (inv : CleanPrefixInvariant tail counterWidth p input rounds x)
    (roundIndex : Fin (2 * tail.succ))
    (hconsumed : roundIndex.val < rounds) :
    (routeHistoryBit tail counterWidth roundIndex).get x =
      ((Trace.ofInput tail.succ p.val input.val).prefixState
        roundIndex.val).active :=
  inv.route_written roundIndex hconsumed

theorem initial_cleanPrefixInvariant
    (tail counterWidth : Nat) (p input : Word tail.succ)
    (hpOdd : p.val % 2 = 1) :
    CleanPrefixInvariant tail counterWidth p input 0
      (withCleanRouteHistory tail.succ counterWidth
        (initialRegisters tail.succ counterWidth p input)) := by
  refine
    { rounds_le := by omega
      modulusOdd := hpOdd
      clean := ?_
      source_eq := ?_
      counter_mod := ?_
      history_written := ?_
      history_fresh := ?_
      route_written := ?_
      route_fresh := ?_ }
  · constructor <;> rfl
  · simpa [Trace.prefixState, Trace.ofInput, RoundState.runRounds,
      RoundState.initial,
      dataRegisters,
      withCleanRouteHistory, withCleanFullRoundPathControlWork,
      withCleanFullRoundPathWork] using
      (RoundState.fromRegisters_initialRegisters
        tail.succ counterWidth p input)
  · simp [Trace.prefixState, Trace.ofInput, RoundState.runRounds,
      RoundState.initial,
      dataRegisters,
      withCleanRouteHistory, withCleanFullRoundPathControlWork,
      withCleanFullRoundPathWork, initialRegisters]
  · intro _ h
    omega
  · intro i _
    simpa [dataRegisters, withCleanRouteHistory,
      withCleanFullRoundPathControlWork,
      withCleanFullRoundPathWork] using
      initialRegisters_historyBit_get
        tail.succ counterWidth p input i
  · intro _ h
    omega
  · intro i _
    simp [routeHistoryBit, withCleanRouteHistory,
      BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.finIdentityBit,
      BinaryLabelEncoding.ofEquivBit, WireAddress.bitIndex]

set_option maxHeartbeats 800000 in
-- Prefix induction repeatedly normalizes one full routed round and its invariants.
/-- Every bounded prefix of the static round ledger is a structured state
satisfying the exact physical/source prefix invariant. -/
theorem foldPrefix_cleanInvariant
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (p input : Word tail.succ)
    (hpOdd : p.val % 2 = 1)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : RegistersWithRouteHistory tail.succ counterWidth),
        CleanPrefixInvariant tail counterWidth p input roundIndex.val x ->
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (dataRegisters tail counterWidth x))
    (rounds : Nat) (hrounds : rounds ≤ 2 * tail.succ) :
    ∃ x : RegistersWithRouteHistory tail.succ counterWidth,
      foldPrefix tail counterWidth comparisonIndex workIndex rounds
          (withCleanRouteHistory tail.succ counterWidth
            (initialRegisters tail.succ counterWidth p input)) = x ∧
      CleanPrefixInvariant tail counterWidth p input rounds x := by
  revert hrounds
  induction rounds with
  | zero =>
      intro _
      refine
        ⟨withCleanRouteHistory tail.succ counterWidth
            (initialRegisters tail.succ counterWidth p input), rfl, ?_⟩
      exact initial_cleanPrefixInvariant tail counterWidth p input hpOdd
  | succ rounds ih =>
      intro hrounds
      have hlt : rounds < 2 * tail.succ := by omega
      let roundIndex : Fin (2 * tail.succ) := ⟨rounds, hlt⟩
      rcases ih (by omega) with ⟨x, hfold, inv⟩
      let trace := Trace.ofInput tail.succ p.val input.val
      let source := trace.prefixState rounds
      have hinput : RoundCleanInput tail counterWidth roundIndex x :=
        { toPhysicalWorkspaceClean := inv.clean
          historyFresh := inv.history_fresh roundIndex (by
            change rounds ≤ rounds
            omega)
          routeFresh := inv.route_fresh roundIndex (by
            change rounds ≤ rounds
            omega) }
      have hsource :
          RoundState.fromRegisters tail.succ counterWidth
              (dataRegisters tail counterWidth x) source.kaliskiSteps
              source.paddingSteps = source := by
        simpa only [source, trace] using inv.source_eq
      have hcounter :
          (dataRegisters tail counterWidth x).counter.val =
            source.paddingSteps % 2 ^ counterWidth := by
        simpa only [source, trace] using inv.counter_mod
      have hbezout : RoundState.BezoutInvariant p.val source := by
        change RoundState.BezoutInvariant p.val
          (RoundState.runRounds rounds (RoundState.initial p.val input.val))
        exact RoundState.runRounds_bezoutInvariant rounds p.val
          (RoundState.initial p.val input.val)
          (RoundState.initial_bezoutInvariant p.val input.val)
      rcases roundStep_cleanBoundary tail counterWidth p.val comparisonIndex
          workIndex roundIndex source x hinput hsource hcounter hfinal hpOdd
          hbezout (arithAt roundIndex x inv) with
        ⟨after, hstep, boundary⟩
      refine ⟨after, ?_, ?_⟩
      · change foldPrefix tail counterWidth comparisonIndex workIndex
            (roundIndex.val + 1)
            (withCleanRouteHistory tail.succ counterWidth
              (initialRegisters tail.succ counterWidth p input)) = _
        rw [foldPrefix_succ, hfold, hstep]
      · refine
          { rounds_le := hrounds
            modulusOdd := hpOdd
            clean := boundary.toPhysicalWorkspaceClean
            source_eq := ?_
            counter_mod := ?_
            history_written := ?_
            history_fresh := ?_
            route_written := ?_
            route_fresh := ?_ }
        · change RoundState.fromRegisters tail.succ counterWidth
              (dataRegisters tail counterWidth after)
              (trace.prefixState (rounds + 1)).kaliskiSteps
              (trace.prefixState (rounds + 1)).paddingSteps =
            trace.prefixState (rounds + 1)
          rw [Trace.prefixState_succ]
          exact boundary.sourceAfter
        · change (dataRegisters tail counterWidth after).counter.val =
            (trace.prefixState (rounds + 1)).paddingSteps %
              2 ^ counterWidth
          rw [Trace.prefixState_succ]
          exact boundary.counterAfter
        · intro i hi
          change
            (RegisterBits.historyBit tail.succ counterWidth i).get
                (dataRegisters tail counterWidth after) =
              RoundState.historyBit (trace.prefixState i.val)
          by_cases hcurrent : i = roundIndex
          · subst i
            simpa only [source, roundIndex] using boundary.historyWritten
          · have hvalne : i.val ≠ rounds := by
              intro heq
              apply hcurrent
              apply Fin.ext
              exact heq
            have hprior : i.val < rounds := by omega
            calc
              _ = (RegisterBits.historyBit tail.succ counterWidth i).get
                  (dataRegisters tail counterWidth x) :=
                boundary.historyPreserved i (Ne.symm hcurrent)
              _ = RoundState.historyBit (trace.prefixState i.val) := by
                simpa only [trace] using inv.history_written i hprior
        · intro i hi
          have hne : roundIndex ≠ i := by
            intro heq
            have hval := congrArg Fin.val heq
            change rounds = i.val at hval
            omega
          calc
            _ = (RegisterBits.historyBit tail.succ counterWidth i).get
                (dataRegisters tail counterWidth x) :=
              boundary.historyPreserved i hne
            _ = false := inv.history_fresh i (by omega)
        · intro i hi
          change (routeHistoryBit tail counterWidth i).get after =
            (trace.prefixState i.val).active
          by_cases hcurrent : i = roundIndex
          · subst i
            simpa only [source, roundIndex] using boundary.routeWritten
          · have hvalne : i.val ≠ rounds := by
              intro heq
              apply hcurrent
              apply Fin.ext
              exact heq
            have hprior : i.val < rounds := by omega
            calc
              _ = (routeHistoryBit tail counterWidth i).get x :=
                boundary.routePreserved i (Ne.symm hcurrent)
              _ = (trace.prefixState i.val).active := by
                simpa only [trace] using inv.route_written i hprior
        · intro i hi
          have hne : roundIndex ≠ i := by
            intro heq
            have hval := congrArg Fin.val heq
            change rounds = i.val at hval
            omega
          calc
            _ = (routeHistoryBit tail counterWidth i).get x :=
              boundary.routePreserved i hne
            _ = false := inv.route_fresh i (by omega)

set_option maxHeartbeats 800000 in
-- Closing the full fold rewrites the bounded prefix into the fixed source endpoint.
/-- The complete static fold reaches the encoded clean endpoint whose source
readout is exactly the fixed `2n` Montgomery--Kaliski state. -/
theorem foldStep_cleanEndpoint_eq_source
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (p input : Word tail.succ)
    (hpOdd : p.val % 2 = 1)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : RegistersWithRouteHistory tail.succ counterWidth),
        CleanPrefixInvariant tail counterWidth p input roundIndex.val x ->
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (dataRegisters tail counterWidth x)) :
    ∃ x : RegistersWithRouteHistory tail.succ counterWidth,
      foldStep tail counterWidth comparisonIndex workIndex
          (withCleanRouteHistory tail.succ counterWidth
            (initialRegisters tail.succ counterWidth p input)) = x ∧
      CleanPrefixInvariant tail counterWidth p input (2 * tail.succ) x ∧
      RoundState.fromRegisters tail.succ counterWidth
          (dataRegisters tail counterWidth x)
          (RoundState.fixedRoundState tail.succ p.val input.val).kaliskiSteps
          (RoundState.fixedRoundState tail.succ p.val input.val).paddingSteps =
        RoundState.fixedRoundState tail.succ p.val input.val := by
  rcases foldPrefix_cleanInvariant tail counterWidth comparisonIndex workIndex
      p input hpOdd hfinal arithAt (2 * tail.succ) (by omega) with
    ⟨x, hfold, inv⟩
  refine ⟨x, ?_, inv, ?_⟩
  · rw [← foldPrefix_full tail counterWidth comparisonIndex workIndex]
    exact hfold
  · let trace := Trace.ofInput tail.succ p.val input.val
    have hsource :
        RoundState.fromRegisters tail.succ counterWidth
            (dataRegisters tail counterWidth x)
            (trace.prefixState (2 * tail.succ)).kaliskiSteps
            (trace.prefixState (2 * tail.succ)).paddingSteps =
          trace.prefixState (2 * tail.succ) := by
      simpa only [trace] using inv.source_eq
    have hfull : trace.prefixState (2 * tail.succ) = trace.finish := by
      simpa using Trace.prefixState_full trace
    rw [hfull] at hsource
    simpa only [trace, Trace.ofInput] using hsource

theorem fold_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (encoding tail.succ counterWidth)
      (foldProgram tail counterWidth comparisonIndex workIndex)
      (foldStep tail counterWidth comparisonIndex workIndex) :=
  UnitaryCircuit.Realizes.appendList
    (encoding tail.succ counterWidth)
    (foldPrograms tail counterWidth comparisonIndex workIndex)
    (foldSteps tail counterWidth comparisonIndex workIndex)
    (foldSchedules_forall₂_realizes
      tail counterWidth comparisonIndex workIndex)

/-- The established actual fold program and the directly compiled primitive
source list agree on every encoded basis state. -/
theorem foldProgram_gateList_applyNormalized_eq
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (foldProgram tail counterWidth comparisonIndex workIndex).applyNormalized
        (NormalizedVector.ket
          ((encoding tail.succ counterWidth).encode x)) =
      (EncodedBit.GateSpec.programList
        (foldGates tail counterWidth comparisonIndex workIndex)).applyNormalized
          (NormalizedVector.ket
            ((encoding tail.succ counterWidth).encode x)) := by
  rw [(fold_realizes tail counterWidth comparisonIndex workIndex).apply_encoded_ket]
  rw [(foldGates_realizes tail counterWidth comparisonIndex workIndex).apply_encoded_ket]

/-- Semantic inverse selected on the finite encoded workspace. -/
noncomputable def foldInverseStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithRouteHistory tail.succ counterWidth ->
      RegistersWithRouteHistory tail.succ counterWidth :=
  letI : Nonempty (RegistersWithRouteHistory tail.succ counterWidth) :=
    ⟨withCleanRouteHistory tail.succ counterWidth
      (initialRegisters tail.succ counterWidth 0 0)⟩
  Function.invFun (foldStep tail counterWidth comparisonIndex workIndex)

/-- The actual fold semantics is surjective on its finite encoded workspace. -/
theorem foldStep_surjective (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    Function.Surjective
      (foldStep tail counterWidth comparisonIndex workIndex) :=
  letI : Finite (RegistersWithRouteHistory tail.succ counterWidth) :=
    Finite.of_injective (encoding tail.succ counterWidth).encode
      (encoding tail.succ counterWidth).encode_injective
  Finite.surjective_of_injective
    (UnitaryCircuit.Realizes.injective
      (fold_realizes tail counterWidth comparisonIndex workIndex))

/-- The selected inverse is a right inverse for the forward fold semantics. -/
theorem foldStep_compute_rightInverse (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ x,
      foldStep tail counterWidth comparisonIndex workIndex
          (foldInverseStep tail counterWidth comparisonIndex workIndex x) =
        x :=
  letI : Nonempty (RegistersWithRouteHistory tail.succ counterWidth) :=
    ⟨withCleanRouteHistory tail.succ counterWidth
      (initialRegisters tail.succ counterWidth 0 0)⟩
  Function.rightInverse_invFun
    (foldStep_surjective tail counterWidth comparisonIndex workIndex)

/-- Running the selected inverse after the forward fold restores its input. -/
theorem foldInverseStep_foldStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ x,
      foldInverseStep tail counterWidth comparisonIndex workIndex
          (foldStep tail counterWidth comparisonIndex workIndex x) = x := by
  intro x
  apply UnitaryCircuit.Realizes.injective
    (fold_realizes tail counterWidth comparisonIndex workIndex)
  exact foldStep_compute_rightInverse tail counterWidth comparisonIndex
    workIndex (foldStep tail counterWidth comparisonIndex workIndex x)

/-- Physical inverse of the full fixed-round fold program. -/
def foldInverseProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  (foldProgram tail counterWidth comparisonIndex workIndex).dagger

/-- The actual reversed circuit realizes the selected semantic inverse. -/
theorem foldInverse_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (encoding tail.succ counterWidth)
      (foldInverseProgram tail counterWidth comparisonIndex workIndex)
      (foldInverseStep tail counterWidth comparisonIndex workIndex) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse
    (fold_realizes tail counterWidth comparisonIndex workIndex)
    (foldStep_compute_rightInverse tail counterWidth comparisonIndex workIndex)

/-- The reversed actual circuit cleans every route-history bit and all other
work whenever it is applied after the exact forward fold basis action. -/
theorem foldInverseProgram_cleans_route_history
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithRouteHistory tail.succ counterWidth) :
    (foldInverseProgram tail counterWidth comparisonIndex workIndex).applyNormalized
        (NormalizedVector.ket
          ((encoding tail.succ counterWidth).encode
            (foldStep tail counterWidth comparisonIndex workIndex x))) =
      NormalizedVector.ket ((encoding tail.succ counterWidth).encode x) := by
  rw [(foldInverse_realizes tail counterWidth comparisonIndex
    workIndex).apply_encoded_ket]
  rw [foldInverseStep_foldStep]

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end

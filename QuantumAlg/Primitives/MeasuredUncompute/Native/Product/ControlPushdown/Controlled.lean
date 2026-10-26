/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MeasuredUncompute.Native.Product.ControlPushdown
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.ControlPushdown
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Controlled

/-!
# The actual supplied-control consumer after variable-product pushdown

The point-arithmetic control still lowers every real source CNOT to one
Toffoli and every source Toffoli to four Toffolis. The previous comparison
word is placed and controlled on the identical complete carrier. Both
native Toffoli counts and actual quantum durations include this expansion.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown.Controlled

noncomputable section

open MAU.Multiplication ProductPlacement EncodedBit GateSpec
open VariableGidney.PushdownComparison
open Accumulate.Gidney.ControlPushdown

private def previousLifted (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (sourceEncoding width)) :=
  (previousGates width modulus).map
    (GateSpec.prodLeft (BinaryLabelEncoding.finIdentity (historyWidth width)))

private def previousSource (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (frameEncoding width)) :=
  (previousLifted width modulus).map (placement width).placeGate

private lemma previousSource_events (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (previousSource width modulus).map (event .empty) =
      (previousGates width modulus).map (event .empty) := by
  have placed := (placement width).placeGates_eventTrace (QubitLayout.canonical _) .empty
    (previousLifted width modulus)
  rw [programList_eventTrace] at placed
  exact placed.trans (map_event_prodLeft (oracles := .empty)
    (left := VariableGidney.encoding width)
    (BinaryLabelEncoding.finIdentity (historyWidth width)) (previousGates width modulus))

private def previousControlledGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (NativeProductFrame.Controlled.encoding width)) :=
  NativeFrameControl.gates width true (previousSource width modulus)

private lemma previous_controlled_coordinates (width : Nat)
    (modulus : Fin (2 ^ width + 1)) :
    xCount (previousControlledGates width modulus) = 0 ∧
      cCount (previousControlledGates width modulus) = 0 ∧
      tCount (previousControlledGates width modulus) = 4 * previousToffoliCount width modulus := by
  have source := previousSource_events width modulus
  have lifted := map_event_prodLeft (oracles := .empty) (left := frameEncoding width)
    BinaryLabelEncoding.bool (previousSource width modulus)
  have same := lifted.trans source
  have x := sum_xMultiplicity_eq_of_events_eq .empty same
  have c := sum_cnotMultiplicity_eq_of_events_eq .empty same
  have t := sum_toffoliMultiplicity_eq_of_events_eq .empty same
  have controls := NativeFrameControl.nativeFrameControl_counts width true
    (previousSource width modulus)
  change xCount (previousControlledGates width modulus) = 0 ∧
    cCount (previousControlledGates width modulus) =
      ((previousSource width modulus).map (GateSpec.prodLeft BinaryLabelEncoding.bool) |>.map
        xMultiplicity).sum ∧
    tCount (previousControlledGates width modulus) =
      ((previousSource width modulus).map (GateSpec.prodLeft BinaryLabelEncoding.bool) |>.map
        cnotMultiplicity).sum +
      4 * ((previousSource width modulus).map (GateSpec.prodLeft BinaryLabelEncoding.bool) |>.map
        toffoliMultiplicity).sum at controls
  have oldX : xCount (previousGates width modulus) = 0 := by
    have countZero (count : Nat) (within : count ≤ width) :
        xCount (previousPrefixGates width modulus count within) = 0 := by
      induction count with
      | zero => rfl
      | succ index ih =>
          have zero : xCount (previousStageGates width modulus ⟨index, by omega⟩) = 0 :=
            (Accumulate.Gidney.ControlPushdown.originalControlled_native_counts
              width width ⟨index, by omega⟩
              (Accumulate.Gidney.gates width modulus (2 ^ index))).1
          rw [previousPrefixGates, Accumulate.Gidney.ControlPushdown.xCount_append,
            ih (by omega), zero, Nat.zero_add]
    exact countZero width (Nat.le_refl width)
  have oldC := (exact_comparison width modulus).2.1
  refine ⟨controls.1, ?_, ?_⟩
  · exact controls.2.1.trans (x.trans oldX)
  · rw [controls.2.2, c, t]
    change previousCnotCount width modulus + 4 * previousToffoliCount width modulus = _
    rw [oldC, Nat.zero_add]

/-- The previous literal placed-and-controlled program's actual Toffoli coordinate. -/
public def previousControlledToffoliCount (width : Nat)
    (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (programList (QubitLayout.canonical _) .empty
      (previousControlledGates width modulus)).eventCost

/-- The Toffoli coordinate of the actual Generic supplied-control product consumer. -/
public def controlledToffoliCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (NativeProductFrame.Controlled.program width modulus (QubitLayout.canonical _)).eventCost

/-- CNOTs of the same actual supplied-control program. -/
public def controlledCnotCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (NativeProductFrame.Controlled.program width modulus (QubitLayout.canonical _)).eventCost

/-- Single-qubit gates of that same actual supplied-control program. -/
public def controlledSingleQubitCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (NativeProductFrame.Controlled.program width modulus (QubitLayout.canonical _)).eventCost

/-- The previous controlled word's true serial quantum duration. -/
public def previousControlledQuantumTime (width : Nat)
    (modulus : Fin (2 ^ width + 1)) : Nat :=
  (programList (QubitLayout.canonical _) .empty
    (previousControlledGates width modulus)).evaluatedEventDepth Resource.Event.quantumDuration

/-- True quantum duration of the actual supplied-control consumer. -/
public def controlledQuantumTime (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
    (NativeProductFrame.Controlled.program width modulus (QubitLayout.canonical _))

/-- Exact Toffoli and time savings after paying the real outer-control expansion. -/
public def controlledSaving (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  3 * actualCnotCount width modulus + 4 * quantumTimeSaving width modulus

/-- The actual final control consumes the increased CNOT coordinate explicitly. -/
public lemma controlled_coordinates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    controlledSingleQubitCount width modulus = 0 ∧ controlledCnotCount width modulus = 0 ∧
      controlledToffoliCount width modulus = actualCnotCount width modulus +
        4 * actualToffoliCount width modulus := by
  have counts := NativeProductFrame.Controlled.nativeProductControlled_counts width modulus
    (QubitLayout.canonical _)
  have placed := placed_coordinates width modulus
  have zero := (exact_comparison width modulus).2.2.1
  refine ⟨counts.1, ?_, ?_⟩
  · exact counts.2.1.trans (placed.2.2.trans zero)
  · exact counts.2.2.trans (congrArg₂ (fun a b : Nat => a + 4 * b) placed.2.1 placed.1)

private lemma controlled_time_eq_toffoli (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    controlledQuantumTime width modulus = controlledToffoliCount width modulus := by
  have counts := controlled_coordinates width modulus
  unfold controlledQuantumTime NativeProductFrame.Controlled.program
  rw [Accumulate.Gidney.ControlPushdown.native_time, length_eq_multiplicity_sums]
  have x := programList_x_count_eq_sum (QubitLayout.canonical _) .empty
    (NativeProductFrame.Controlled.gates width modulus)
  have c := programList_cnot_count_eq_sum (QubitLayout.canonical _) .empty
    (NativeProductFrame.Controlled.gates width modulus)
  have t := programList_toffoli_count_eq_sum (QubitLayout.canonical _) .empty
    (NativeProductFrame.Controlled.gates width modulus)
  change _ = controlledToffoliCount width modulus
  have zeroX : ((NativeProductFrame.Controlled.gates width modulus).map xMultiplicity).sum = 0 :=
    x.symm.trans counts.1
  have zeroC : ((NativeProductFrame.Controlled.gates width modulus).map
      cnotMultiplicity).sum = 0 := c.symm.trans counts.2.1
  rw [zeroX, zeroC, Nat.zero_add]
  exact t.symm

/-- Both compared real words include every supplied-control gate and arbitrary-dirty restoration. -/
public lemma controlled_comparison (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    previousControlledToffoliCount width modulus = controlledToffoliCount width modulus +
        controlledSaving width modulus ∧
      previousControlledQuantumTime width modulus = controlledQuantumTime width modulus +
        controlledSaving width modulus := by
  have before := previous_controlled_coordinates width modulus
  have beforeCount : previousControlledToffoliCount width modulus =
      4 * previousToffoliCount width modulus := by
    unfold previousControlledToffoliCount
    rw [programList_toffoli_count_eq_sum]
    exact before.2.2
  have toffoli := (exact_comparison width modulus).1
  have split := saving_decomposition width modulus
  have afterCount := (controlled_coordinates width modulus).2.2
  have comparison : previousControlledToffoliCount width modulus =
      controlledToffoliCount width modulus + controlledSaving width modulus := by
    rw [beforeCount, toffoli, split, afterCount]
    unfold controlledSaving
    ring
  refine ⟨comparison, ?_⟩
  unfold previousControlledQuantumTime
  rw [Accumulate.Gidney.ControlPushdown.native_time, length_eq_multiplicity_sums]
  change xCount _ + cCount _ + tCount _ = _
  rw [before.1, before.2.1, Nat.zero_add,
    before.2.2, ← beforeCount, comparison, controlled_time_eq_toffoli]

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown.Controlled

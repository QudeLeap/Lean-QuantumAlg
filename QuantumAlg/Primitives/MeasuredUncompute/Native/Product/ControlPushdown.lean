/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.ControlPushdown.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.ControlPushdown.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Gates

/-!
# Control pushdown consumed by the existing measured-arithmetic product ports

These coordinates observe the actual placed NativeProductFrame program used
by generic measured point arithmetic. Its original three ports and complete
retained frame remain unchanged. No preparation or input restriction is added.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown

noncomputable section

open MAU.Multiplication ProductPlacement EncodedBit GateSpec
open VariableGidney.PushdownComparison

private lemma same_pool (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost = (VariableGidney.program width modulus).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, nativeProductFrame_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The real placed Toffoli coordinate, read from the actual native product program. -/
public def placedToffoliCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (program width modulus).eventCost

/-- The real placed CNOT coordinate, independent of every other coordinate. -/
public def placedCnotCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (program width modulus).eventCost

/-- The real placed single-qubit coordinate. -/
public def placedSingleQubitCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (program width modulus).eventCost

/-- Actual quantum duration of that same placed program. -/
public def placedQuantumTime (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  (program width modulus).evaluatedEventDepth Resource.Event.quantumDuration

/-- The same complete shared frame is retained around all actual product gates. -/
public def placedWidth (width : Nat) : Nat := (frameEncoding width).width

/-- Literal gates, composed source program and actual placed program have identical coordinates. -/
public lemma placed_coordinates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    placedToffoliCount width modulus = actualToffoliCount width modulus ∧
      placedCnotCount width modulus = actualCnotCount width modulus ∧
      placedSingleQubitCount width modulus = actualSingleQubitCount width modulus := by
  have toffoli := programList_toffoli_count_eq_sum (QubitLayout.canonical _) .empty
    (VariableGidney.gates width modulus)
  have cnot := programList_cnot_count_eq_sum (QubitLayout.canonical _) .empty
    (VariableGidney.gates width modulus)
  have single := programList_x_count_eq_sum (QubitLayout.canonical _) .empty
    (VariableGidney.gates width modulus)
  rw [programList_eventCost, VariableGidney.variableGidney_gates_eventCost] at toffoli cnot single
  unfold placedToffoliCount placedCnotCount placedSingleQubitCount
  rw [same_pool]
  exact ⟨toffoli, cnot, single⟩

/-- Actual placement retains the original program's dependency depth. -/
public lemma placed_quantumTime (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    placedQuantumTime width modulus = actualQuantumTime width modulus := by
  unfold placedQuantumTime program
  rw [FullPlacement.place_evaluatedEventDepth]
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth
    (historyWidth width) Resource.Event.quantumDuration (VariableGidney.program width modulus)

/-- This real Generic consumer preserves the exact per-coordinate and time comparison. -/
public lemma placed_comparison (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    previousToffoliCount width modulus = placedToffoliCount width modulus +
        toffoliSaving width modulus ∧
      previousCnotCount width modulus = 0 ∧ placedSingleQubitCount width modulus = 0 ∧
      previousQuantumTime width modulus = placedQuantumTime width modulus +
        quantumTimeSaving width modulus := by
  rw [(placed_coordinates width modulus).1, (placed_coordinates width modulus).2.2,
    placed_quantumTime]
  exact exact_comparison width modulus

/-- The original CNOT allowance remains valid after the actual Generic placement. -/
public lemma placed_cnot_bound (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    placedCnotCount width modulus ≤ nativeCoordinateCap width := by
  rw [(placed_coordinates width modulus).2.1]
  exact actual_cnot_bound width modulus

/-- No physical coordinate is appended to the original product-and-history frame. -/
public lemma placed_width (width : Nat) :
    placedWidth width = 3 * width + 11 + 4 * width.size := by
  unfold placedWidth
  rw [frame_width]
  unfold ProductWires.width tailWidth
  omega

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown

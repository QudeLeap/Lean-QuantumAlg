/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled.Counts
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.ZReset.Resources

/-!
# Independent allowances for the same-bank recycling schedule

The arithmetic allowance separates the selected multiplier's native coordinates
in the actual BitWord execution model. Hadamard, phase and correction occurrences
all use its existing singleQubit coordinate; their separate syntactic terms
remain visible below without inventing a finer gate model. No budget is
computed from the implementation's eventCost or dependency expression.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources

noncomputable section

open Execution

/-- One actual one-qubit instruction in the existing execution model. -/
def oneQubit : ResourcePool model := ResourcePool.singleton (.gate .singleQubit)

/-- One actual binary read into an existing retained cell. -/
def oneMeasurement : ResourcePool model := ResourcePool.singleton (.measurement (2 : ℕ+))

/-- Independent native allowances of the unchanged selected multiplier. -/
def arithmeticGateBound (width : Nat) : AlgorithmGate.Coordinate → Nat
  | .singleQubit => 0
  | .cnot => MAU.Multiplication.Gidney.controlledCnotBound width
  | .toffoli => MAU.Multiplication.Gidney.controlledToffoliBound width

/-- The arithmetic pool contains exactly the two independently bounded native coordinates. -/
def arithmeticBudget (width : Nat) : ResourcePool model :=
  arithmeticGateBound width .cnot • ResourcePool.singleton (model := model) (.gate .cnot) +
    arithmeticGateBound width .toffoli • ResourcePool.singleton (model := model) (.gate .toffoli)

/-- Two Hadamards and at most one correction accompany each actual arithmetic call and read. -/
def baseBudget (width : Nat) : ResourcePool model :=
  arithmeticBudget width + 2 • oneQubit + oneQubit + oneMeasurement

/-- A chronological position reads at most that many earlier feedback bits. -/
def stageBudget (width position : Nat) : ResourcePool model :=
  baseBudget width + position • oneQubit

/-- Number of earlier-bit feedback opportunities in a chronological suffix. -/
def feedbackWork (remaining position : Nat) : Nat :=
  remaining * position + remaining.choose 2

/-- The same complete suffix pays every stage and every preceding-bit feedback opportunity. -/
def suffixBudget (width remaining position : Nat) : ResourcePool model :=
  remaining • baseBudget width + feedbackWork remaining position • oneQubit

/-- Independent complete member allowance for the two sequential exponent streams. -/
def memberBudget (m ell width : Nat) : ResourcePool model :=
  resultBits m ell • baseBudget width +
    ((ell + m).choose 2 + ell.choose 2) • oneQubit

/-- Arithmetic serial work plus two Hadamards and at most one correction per stage. -/
def stageTime (width position : Nat) : Nat :=
  MAU.Multiplication.Gidney.controlledTimeBound width + 3 + position

/-- The quantum time of a suffix includes every chronological feedback position. -/
def suffixTime (width remaining position : Nat) : Nat :=
  remaining * (MAU.Multiplication.Gidney.controlledTimeBound width + 3) +
    feedbackWork remaining position

/-- The two exponent streams run sequentially on the one original carrier. -/
def memberTime (m ell width : Nat) : Nat :=
  resultBits m ell * (MAU.Multiplication.Gidney.controlledTimeBound width + 3) +
    ((ell + m).choose 2 + ell.choose 2)

private lemma feedbackWork_succ (remaining position : Nat) :
    feedbackWork (remaining + 1) position = position + feedbackWork remaining (position + 1) := by
  have choose : (remaining + 1).choose 2 = remaining + remaining.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ remaining 1
  simp only [feedbackWork, choose, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Valid and fallback branches obey each independent native arithmetic allowance. -/
lemma sourceArithmetic_gateCount (width N : Nat) (coefficient : (ZMod N)ˣ)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (sourceArithmetic width N coefficient).eventCost ≤
      arithmeticGateBound width coordinate := by
  unfold sourceArithmetic
  split_ifs with positive fitted
  · have bounds := MAU.Multiplication.Gidney.gidneyControlledUnitMultiplication_native_bounds
      1 width (0 : Fin 1) ⟨N, Nat.lt_succ_of_le fitted⟩
      (Nat.FixedWidth.UnitExponentiation.stageUnit coefficient (0 : Fin 1))
    cases coordinate with
    | singleQubit => exact bounds.1.le
    | cnot => exact bounds.2.1
    | toffoli => exact bounds.2.2
  all_goals simp only [UnitaryCircuit.identity_eventCost, ResourcePool.count_zero, Nat.zero_le]

/-- Serial arithmetic time uses the sum of its independent CNOT and Toffoli allowances. -/
lemma sourceArithmetic_time (width N : Nat) (coefficient : (ZMod N)ˣ) :
    (sourceArithmetic width N coefficient).evaluatedEventDepth (fun _ => 1) ≤
      MAU.Multiplication.Gidney.controlledTimeBound width := by
  unfold sourceArithmetic
  split_ifs with positive fitted
  · exact MAU.Multiplication.Gidney.gidneyControlledUnitMultiplication_time_bound
      1 width (0 : Fin 1) ⟨N, Nat.lt_succ_of_le fitted⟩
      (Nat.FixedWidth.UnitExponentiation.stageUnit coefficient (0 : Fin 1))
  all_goals simpa only [UnitaryCircuit.evaluatedEventDepth_identity] using
    (Nat.zero_le (MAU.Multiplication.Gidney.controlledTimeBound width))

/-- The fixed carrier has one control and two width-bit arithmetic words, at dimension two only. -/
lemma arithmeticBank_quantumSystems (width : Nat) (dimension : ℕ+) :
    SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then 1 + 2 * width else 0 := by
  change (QuantumLayout.uniform (Arithmetic.encoding width).width 2
    (Arithmetic.layout width).physical_idx
    (Arithmetic.layout width).physical_idx_injective).dimensionCount dimension = _
  rw [QuantumLayout.dimensionCount_uniform, Arithmetic.width_eq]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Equal-wire placement preserves each arithmetic coordinate in the real BitWord model. -/
lemma arithmetic_events (N : Nat) (coefficient : (ZMod N)ˣ)
    (path : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) (arithmetic base noQuantum m ell width N coefficient)).Path) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true)
      (arithmetic base noQuantum m ell width N coefficient)).resourcePool path ≤
        arithmeticBudget width := by
  change ResourcePool.ofList
    ((arithmetic base noQuantum m ell width N coefficient).eventTrace BitWord.model .empty) ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (arithmetic base noQuantum m ell width N coefficient) BitWord.model .empty,
    arithmetic, unitaryOfEqualWires_cost]
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      have bounded := sourceArithmetic_gateCount width N coefficient coordinate
      cases coordinate <;> simpa [arithmeticBudget, arithmeticGateBound] using bounded
  | oracle query => exact nomatch query
  | classicalOperation _ => exact Nat.zero_le _
  | classicalQuery _ => exact Nat.zero_le _
  | preparation _ => exact Nat.zero_le _
  | measurement _ => exact Nat.zero_le _

/-- The actual arithmetic dependency expression retains the independent serial stage bound. -/
lemma arithmetic_time (N : Nat) (coefficient : (ZMod N)ˣ)
    (path : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) (arithmetic base noQuantum m ell width N coefficient)).Path) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true)
      (arithmetic base noQuantum m ell width N coefficient)).quantumTime path ≤
        MAU.Multiplication.Gidney.controlledTimeBound width := by
  refine (Circuit.quantumTime_le_unitDepth _ path).trans ?_
  change DepthExpr.depthEval (fun _ => 1)
    ((arithmetic base noQuantum m ell width N coefficient).eventDepth BitWord.model .empty) ≤ _
  rw [arithmetic, unitaryOfEqualWires_depth,
    UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
  exact sourceArithmetic_time width N coefficient

/-- Each of the actual H or phase instructions contributes one existing native event. -/
lemma single_events (operator : UnitaryOperator (Qubits 1))
    (path : (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) (single base noQuantum m ell width operator)).Path) :
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := true) (single base noQuantum m ell width operator)).resourcePool path =
        oneQubit := rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Resources

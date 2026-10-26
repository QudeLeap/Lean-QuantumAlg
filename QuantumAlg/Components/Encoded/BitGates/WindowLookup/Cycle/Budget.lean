/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Resources

/-!
# Independent full-window and tail-window resource budgets

The budgets depend only on the problem's address width and fixed 256-bit
result word. The actual circuit bounds are proved separately from its real
native gates, measured paths, paid classical work and parallel dependencies.
The fixed split uses at most eight low address bits and unitary selectors.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

/-- Independent native coordinates for one 256-bit result load/unlookup pair. -/
structure WindowBudget where
  toffoli : Nat
  cnotClassical : Nat
  singleQubit : Nat
  measurements : Nat
  quantumTime : Nat

/-- The prescribed low-address split, including the four-bit final window. -/
def windowLowWidth (width : Nat) : Nat := min 8 ((width + 1) / 2)

/-- Problem-side resource limits, independent of any supplied circuit or table values. -/
def windowBudget (width : Nat) : WindowBudget :=
  let low := windowLowWidth width
  let entries := 2 ^ width
  let lowEntries := 2 ^ low
  let highEntries := 2 ^ (width - low)
  { toffoli := 2 * entries + 2 * highEntries + 2 * lowEntries - 8
    cnotClassical := 771 * entries + 2 * lowEntries - 2
    singleQubit := 2 * entries + 2 * highEntries + 2 * lowEntries + 514
    measurements := 256
    quantumTime := 38 * entries + (4 * low + 6) * highEntries +
      2 * lowEntries + 2 * low - 4 }

namespace UnlookupFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding 256 lowWidth highRemaining)
  (lookup : SelectorFrame encoding (highRemaining + lowWidth))
  (outsideAddress : ∀ bit index,
    (frame.result.bit bit).wire ≠ (lookup.address index).wire)
  (outsideStack : ∀ bit index,
    (frame.result.bit bit).wire ≠ (lookup.stack index).wire)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
  (output : Fin 256 → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits 256))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)

local notation "code" => frame.cycleCircuit (services := services) lookup outsideAddress
  outsideStack physical sameWires table 8 output mask parity
local notation "budget" => windowBudget (highRemaining + lowWidth + 1)

/-- The full sixteen-bit and final four-bit actual programs meet their independent budgets. -/
lemma cycleCircuit_window_budget
    (selectedSplit : (lowWidth = 8 ∧ highRemaining = 7) ∨
      (lowWidth = 2 ∧ highRemaining = 1))
    (path : (code).Path) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .toffoli)
        ((code).resourcePool path) ≤ (budget).toffoli ∧
    ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .cnot)
        ((code).resourcePool path) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((code).resourcePool path) ≤
        (budget).cnotClassical ∧
    ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
        ((code).resourcePool path) ≤ (budget).singleQubit ∧
    ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+))
        ((code).resourcePool path) = (budget).measurements ∧
    (code).depth Resource.Event.quantumDuration path ≤ (budget).quantumTime := by
  have actualT := frame.cycleCircuit_toffoli_count_le lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity (by decide) path
  have actualC := frame.cycleCircuit_cnot_count_le lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity (by decide) path
  have actualClassical := frame.cycleCircuit_classical_weight_le lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity path
  have actualS := frame.cycleCircuit_singleQubit_count_le lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity (by decide) path
  have actualM := frame.cycleCircuit_measurement_count lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity path
  have actualTime := frame.cycleCircuit_quantumTime_le lookup outsideAddress outsideStack
    physical sameWires table 8 output mask parity path
  have toffoliFit :
      (2 * 2 ^ (highRemaining + lowWidth + 1) - 4) +
        (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) - 4)) ≤ (budget).toffoli := by
    rcases selectedSplit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [windowBudget, windowLowWidth]
  have cnotFit :
      ((2 * (2 ^ (highRemaining + lowWidth) - 1) +
        2 * 2 ^ (highRemaining + lowWidth) * (2 * 256 - 1)) +
        (2 * (2 ^ lowWidth - 1) + (2 * 2 ^ (highRemaining + 1) * 2 ^ lowWidth - 2))) +
        (1 + 2 ^ (highRemaining + 1) * 2 ^ lowWidth * (256 + 1)) ≤ (budget).cnotClassical := by
    rcases selectedSplit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [windowBudget, windowLowWidth]
  have singleFit :
      (2 * 2 ^ (highRemaining + lowWidth + 1) - 2) +
        (2 * 256 + 2 + (4 * 2 ^ (highRemaining + 1) - 2)) ≤ (budget).singleQubit := by
    rcases selectedSplit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [windowBudget, windowLowWidth]
  have timeFit :
      (2 + 10 * (2 ^ (highRemaining + lowWidth) - 1) +
        2 * 2 ^ (highRemaining + lowWidth) * (2 * 8 + 1)) +
        (2 + 2 * (2 ^ lowWidth + lowWidth) +
          ((2 * lowWidth + 8) * 2 ^ (highRemaining + 1) - 8)) ≤ (budget).quantumTime := by
    rcases selectedSplit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [windowBudget, windowLowWidth]
  exact ⟨actualT.trans toffoliFit, (Nat.add_le_add actualC actualClassical).trans cnotFit,
    actualS.trans singleFit, actualM, actualTime.trans timeFit⟩

end UnlookupFrame

/-- Independent three-round limits for two 260-bit streams and six load/unlookup calls per point. -/
lemma windowBudget_three_rounds :
    18 * (32 * (windowBudget 16).toffoli + 2 * (windowBudget 4).toffoli) = 76084128 ∧
    18 * (32 * (windowBudget 16).cnotClassical + 2 * (windowBudget 4).cnotClassical) =
      29105013528 ∧
    18 * (32 * (windowBudget 16).measurements + 2 * (windowBudget 4).measurements) = 156672 ∧
    18 * (32 * (windowBudget 16).quantumTime + 2 * (windowBudget 4).quantumTime) =
      1440381312 := by
  norm_num [windowBudget, windowLowWidth]

end

end QuantumAlg.EncodedBit.WindowLookup

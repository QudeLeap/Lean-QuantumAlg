/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Correction
import all QuantumAlg.Primitives.MeasuredUncompute.ClassicalCorrection
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Actual stored-result selection of native product recomputation

The existing classical reference selects the literal product/Z/inverse
program. Every event comes from this same branch, including both product
passes. No storage is allocated or released. Earlier measurement writes
and reset must be composed with this operation for complete measured
arithmetic [LYL+26, sec_point_add/sec_point_add.tex:85-105].
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductCorrection

noncomputable section

open Execution MAU.Multiplication EncodedBit.Word

/-- The same three actual quantum words remain present throughout correction. -/
theorem program_physical (width : Nat) (_modulus : Fin (2 ^ width + 1))
    (_mask : Fin width → Bool) :
    (QubitLayout.canonical (VariableGidney.encoding width).width).systemIdx =
      List.range (3 * width) := by
  have count : (VariableGidney.encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  rw [QubitLayout.canonical_systemIdx, count]

/-- Independent coordinatewise allowance includes both actual product passes and every Z bit. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  VariableGidney.nativeBudget width +
    (width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) +
      VariableGidney.nativeBudget width)

/-- The selected correction pays only for its actual Z gates within the independent allowance. -/
theorem program_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (program width modulus mask).eventCost ≤ nativeBudget width := by
  have phase : (PhaseCorrection.program (QubitLayout.canonical _) .empty
      (targetWord width) mask).eventCost ≤
      width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      PhaseCorrection.program, PhaseCorrection.phaseCorrection_sequence_trace,
      ResourcePool.ofList_replicate]
    apply ResourcePool.le_iff_count.mpr
    intro event
    rw [ResourcePool.count_scale, ResourcePool.count_nsmul]
    exact Nat.mul_le_mul_right _ (PhaseCorrection.phaseCorrection_selected_count_le mask)
  unfold program Recompute.program nativeBudget
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change _ ≤ VariableGidney.nativeBudget width +
    (width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) +
      VariableGidney.nativeBudget width)
  have inverseCost : (AlgorithmGate.oracleFreePool .empty)
      (VariableGidney.program width modulus).eventCost =
      (VariableGidney.program width modulus).eventCost := by
    change Multiset.map (AlgorithmGate.oracleFreeEvent .empty) _ = _
    have eventId : AlgorithmGate.oracleFreeEvent .empty = id := by
      funext event
      cases event with
      | classicalOperation impossible => cases impossible
      | classicalQuery impossible => cases impossible
      | oracle impossible => cases impossible
      | gate _ => rfl
      | preparation _ => rfl
      | measurement _ => rfl
    rw [eventId, Multiset.map_id]
  rw [inverseCost]
  exact add_le_add (VariableGidney.variableGidney_native_budget width modulus)
    (add_le_add phase (VariableGidney.variableGidney_native_budget width modulus))

/-- The actual serial duration includes the dependency through both product executions. -/
theorem program_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (program width modulus mask).evaluatedEventDepth (fun _ => 1) ≤
      2 * VariableGidney.eventBound width + width := by
  unfold program Recompute.program
  rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth, PhaseCorrection.program,
    PhaseCorrection.phaseCorrection_sequence_depth]
  have product := VariableGidney.variableGidney_unit_depth width modulus
  have phase := PhaseCorrection.phaseCorrection_selected_count_le mask
  omega

/-- Retain the complete surrounding arithmetic history while acting on the three product words. -/
def framedProgram (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical ((VariableGidney.encoding width).width + extraWidth)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix extraWidth (program width modulus mask)

/-- The untouched history stays in the live physical frame and is never released by correction. -/
theorem framedProgram_physical (width extraWidth : Nat) (_modulus : Fin (2 ^ width + 1))
    (_mask : Fin width → Bool) :
    (QubitLayout.canonical ((VariableGidney.encoding width).width + extraWidth)).systemIdx =
      List.range (3 * width + extraWidth) := by
  have count : (VariableGidney.encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  rw [QubitLayout.canonical_systemIdx, count]

/-- Keeping the surrounding history retains exactly the product correction's native events. -/
theorem framedProgram_cost (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (framedProgram width extraWidth modulus mask).eventCost =
      (program width modulus mask).eventCost := by
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost extraWidth
    (program width modulus mask)

/-- The untouched frame contributes no duration to the executed native correction. -/
theorem framedProgram_depth (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (framedProgram width extraWidth modulus mask).evaluatedEventDepth (fun _ => 1) =
      (program width modulus mask).evaluatedEventDepth (fun _ => 1) := by
  exact UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth extraWidth
    (fun _ => 1) (program width modulus mask)

variable {ctx : RuntimeCtx .quantum} {extraWidth : Nat}

/-- Place the complete selected native program in its existing runtime quantum frame. -/
def member (width : Nat) (modulus : Fin (2 ^ width + 1))
    (sameWires : (QubitLayout.canonical
      ((VariableGidney.encoding width).width + extraWidth)).toQuantum.wires =
        ctx.quantumLayout.wires)
    (value : CShape.Value (.bits width)) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  unitaryOfEqualWires
    (QubitLayout.canonical ((VariableGidney.encoding width).width + extraWidth)).toQuantum
    ctx.quantumLayout sameWires
      (framedProgram width extraWidth modulus (ClassicalCorrection.mask value))

/-- Read the actual measured bit word and execute the selected concrete arithmetic gates. -/
def code (width : Nat) (modulus : Fin (2 ^ width + 1))
    (sameWires : (QubitLayout.canonical
      ((VariableGidney.encoding width).width + extraWidth)).toQuantum.wires =
        ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width)) :
    Circuit (.quantum AlgorithmGate.model .empty) ctx ctx :=
  .branch result (fun value => .unitary (member width modulus sameWires value))

/-- The full actual store and external reference select precisely their stored correction. -/
theorem code_reference (width : Nat) (modulus : Fin (2 ^ width + 1))
    (sameWires : (QubitLayout.canonical
      ((VariableGidney.encoding width).width + extraWidth)).toQuantum.wires =
        ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    ((code width modulus sameWires result).execute Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (member width modulus sameWires (entry.1.read result)).matrix
        (1 : UnitaryOperator Reference)).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal result (member width modulus sameWires) state

/-- Each selected execution meets the independent two-product and Z allowance. -/
theorem code_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (sameWires : (QubitLayout.canonical
      ((VariableGidney.encoding width).width + extraWidth)).toQuantum.wires =
        ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width))
    (path : (code width modulus sameWires result).Path) :
    (code width modulus sameWires result).resourcePool path ≤ nativeBudget width := by
  change ResourcePool.ofList (member width modulus sameWires path.1).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, member,
    unitaryOfEqualWires_cost, framedProgram_cost]
  exact program_budget width modulus (ClassicalCorrection.mask path.1)

/-- The actual stored selection retains both arithmetic passes in its serial depth bound. -/
theorem code_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (sameWires : (QubitLayout.canonical
      ((VariableGidney.encoding width).width + extraWidth)).toQuantum.wires =
        ctx.quantumLayout.wires)
    (result : CInputRef ctx (.bits width))
    (path : (code width modulus sameWires result).Path) :
    (code width modulus sameWires result).depth (fun _ => 1) path ≤
      2 * VariableGidney.eventBound width + width := by
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (member width modulus sameWires path.1) ≤ _
  rw [member, UnitaryCircuit.evaluatedEventDepth, unitaryOfEqualWires_depth]
  change (framedProgram width extraWidth modulus
    (ClassicalCorrection.mask path.1)).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [framedProgram_depth]
  exact program_depth width modulus (ClassicalCorrection.mask path.1)

end

end QuantumAlg.MeasuredUncompute.NativeProductCorrection

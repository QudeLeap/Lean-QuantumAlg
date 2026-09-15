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
theorem program_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (program width modulus mask).physical_idx = List.range (3 * width) := by
  have count : (VariableGidney.encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  change UnitaryCircuit.unionPhysicalIdx (VariableGidney.program width modulus).physical_idx
    (UnitaryCircuit.unionPhysicalIdx
      (PhaseCorrection.program (targetWord width) mask).physical_idx
      (VariableGidney.program width modulus).dagger.physical_idx) = _
  rw [UnitaryCircuit.dagger_physical_idx, VariableGidney.variableGidney_physical,
    PhaseCorrection.program, PhaseCorrection.phaseCorrection_sequence_physical, count,
    UnitaryCircuit.unionPhysicalIdx_self, UnitaryCircuit.unionPhysicalIdx_self]

/-- Independent coordinatewise allowance includes both actual product passes and every Z bit. -/
def nativeBudget (width : Nat) : ResourcePool .quantum :=
  VariableGidney.nativeBudget width +
    (width • ResourcePool.singleton
      (Gate.atomicEvent (.declared "QuantumAlg.Components.Gate" "pauli-z")) +
      VariableGidney.nativeBudget width)

/-- The selected correction pays only for its actual Z gates within the independent allowance. -/
theorem program_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (program width modulus mask).eventCost ≤ nativeBudget width := by
  have phase : (PhaseCorrection.program (targetWord width) mask).eventCost ≤
      width • ResourcePool.singleton
        (Gate.atomicEvent (.declared "QuantumAlg.Components.Gate" "pauli-z")) := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      PhaseCorrection.program, PhaseCorrection.phaseCorrection_sequence_trace,
      ResourcePool.ofList_replicate]
    apply ResourcePool.le_iff_count.mpr
    intro event
    rw [ResourcePool.count_scale, ResourcePool.count_nsmul]
    exact Nat.mul_le_mul_right _ (PhaseCorrection.phaseCorrection_selected_count_le mask)
  unfold program Recompute.program nativeBudget
  rw [UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.dagger_eventCost]
  exact add_le_add (VariableGidney.variableGidney_native_budget width modulus)
    (add_le_add phase (VariableGidney.variableGidney_native_budget width modulus))

/-- The actual serial duration includes the dependency through both product executions. -/
theorem program_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (program width modulus mask).evaluatedEventDepth (fun _ => 1) ≤
      2 * VariableGidney.eventBound width + width := by
  unfold program Recompute.program
  rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_dagger, PhaseCorrection.program,
    PhaseCorrection.phaseCorrection_sequence_depth]
  have product := VariableGidney.variableGidney_unit_depth width modulus
  have phase := PhaseCorrection.phaseCorrection_selected_count_le mask
  omega

/-- Retain the complete surrounding arithmetic history while acting on the three product words. -/
def framedProgram (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    UnitaryCircuit (Qubits ((VariableGidney.encoding width).width + extraWidth)) :=
  (UnitaryCircuit.prodLeft (n := extraWidth) (program width modulus mask)).seq
    (.identity _ (List.range ((VariableGidney.encoding width).width + extraWidth))
      List.nodup_range)

/-- The untouched history stays in the live physical frame and is never released by correction. -/
theorem framedProgram_physical (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (framedProgram width extraWidth modulus mask).physical_idx =
      List.range (3 * width + extraWidth) := by
  have count : (VariableGidney.encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  have contained : (program width modulus mask).physical_idx ⊆
      List.range (VariableGidney.encoding width).width := by
    rw [program_physical, count]
    exact List.Subset.refl _
  have full := UnitaryCircuit.prodLeft_physical_idx_subset_range
    (n := extraWidth) (program width modulus mask) contained
  exact full.union_eq_right.trans (congrArg (fun n => List.range (n + extraWidth)) count)

/-- Keeping the surrounding history retains exactly the product correction's native events. -/
theorem framedProgram_cost (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (framedProgram width extraWidth modulus mask).eventCost =
      (program width modulus mask).eventCost := by
  rw [framedProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.prodLeft_eventCost,
    UnitaryCircuit.identity_eventCost, add_zero]

/-- The untouched frame contributes no duration to the executed native correction. -/
theorem framedProgram_depth (width extraWidth : Nat) (modulus : Fin (2 ^ width + 1))
    (mask : Fin width → Bool) :
    (framedProgram width extraWidth modulus mask).evaluatedEventDepth (fun _ => 1) =
      (program width modulus mask).evaluatedEventDepth (fun _ => 1) := by
  rw [framedProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.prodLeft_evaluatedEventDepth]
  rfl

variable {ctx : RuntimeCtx .quantum} {extraWidth : Nat}

/-- Place the complete selected native program in its existing runtime quantum frame. -/
def member (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (value : CShape.Value (.bits width)) : UnitaryCircuit ctx.register :=
  .reindex basis (framedProgram width extraWidth modulus (ClassicalCorrection.mask value))

theorem member_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (placed : List.range (3 * width + extraWidth) = ctx.physicalIdx)
    (value : CShape.Value (.bits width)) :
    (member width modulus basis value).physical_idx = ctx.physicalIdx :=
  (framedProgram_physical width extraWidth modulus (ClassicalCorrection.mask value)).trans placed

/-- Read the actual measured bit word and execute the selected concrete arithmetic gates. -/
def code (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (placed : List.range (3 * width + extraWidth) = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width)) : Circuit ctx ctx :=
  .branch result (fun value => .unitary (member width modulus basis value)
    (member_physical width modulus basis placed value))

/-- The full actual store and external reference select precisely their stored correction. -/
theorem code_reference (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (placed : List.range (3 * width + extraWidth) = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    ((code width modulus basis placed result).execute Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (member width modulus basis (entry.1.read result)).matrix
        (1 : UnitaryOperator Reference)).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal result (member width modulus basis)
    (member_physical width modulus basis placed) state

/-- Each selected execution meets the independent two-product and Z allowance. -/
theorem code_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (placed : List.range (3 * width + extraWidth) = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width))
    (path : (code width modulus basis placed result).Path) :
    (code width modulus basis placed result).resourcePool path ≤ nativeBudget width := by
  change ResourcePool.ofList (member width modulus basis path.1).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, member,
    UnitaryCircuit.reindex_eventCost, framedProgram_cost]
  exact program_budget width modulus (ClassicalCorrection.mask path.1)

/-- The actual stored selection retains both arithmetic passes in its serial depth bound. -/
theorem code_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (basis : (Qubits ((VariableGidney.encoding width).width + extraWidth)).Index ≃
      ctx.register.Index)
    (placed : List.range (3 * width + extraWidth) = ctx.physicalIdx)
    (result : CInputRef ctx (.bits width))
    (path : (code width modulus basis placed result).Path) :
    (code width modulus basis placed result).depth (fun _ => 1) path ≤
      2 * VariableGidney.eventBound width + width := by
  change UnitaryCircuit.evaluatedEventDepth (fun _ => 1)
    (framedProgram width extraWidth modulus (ClassicalCorrection.mask path.1)) ≤ _
  rw [framedProgram_depth]
  exact program_depth width modulus (ClassicalCorrection.mask path.1)

end

end QuantumAlg.MeasuredUncompute.NativeProductCorrection

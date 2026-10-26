/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Phase.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Control.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Resources

/-!
# Native portions of the same two arithmetic-call programs

Each call has two actual resident traversals, the same Save and mask-selected
Phase, four actual enable-transfer directions, and the executed numerical
Swap. Native coordinates and scheduled duration are derived independently.
The frozen resident producer and its own accepted bounds are used together.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open QuantumAlg.EncodedBit

def phaseSelection : Kind → Selector
  | .division => .enable
  | .multiplication => .normal

def transferProgram (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  match kind with
  | .division => Control.prepareProgram stream width bounded
  | .multiplication => Window.Enable.program stream width bounded

def transferCnot : Kind → Nat
  | .division => 1
  | .multiplication => 0

/-- This pool is taken directly from the two actual native portions of the Call syntax. -/
def nativePool (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outcome : Word) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (beforeReset kind stream width bounded).eventCost +
    (tail kind stream width bounded outcome).eventCost

private lemma suffix_cost (body : Native.Circuit) :
    (Window.suffixProgram body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Window.suffixProgram_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Actual four-direction transfer cost is visible, including division's extra four CNOTs. -/
lemma native_count (kind : Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (outcome : Word) (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (nativePool kind stream width bounded outcome) =
      2 * ResourcePool.count focus Inversion.program.eventCost +
        ResourcePool.count focus (Save.program Save.ports (phaseSelection kind)).eventCost +
        ResourcePool.count focus
          (Phase.program phasePorts (phaseSelection kind) outcome).eventCost +
        4 * ResourcePool.count focus (transferProgram kind stream width bounded).eventCost +
        ResourcePool.count focus Swap.program.eventCost := by
  cases kind <;>
    simp only [nativePool, beforeReset, tail, divisionTail, multiplicationTail,
      Control.firstResidentProgram, residentWithTemporary, residentWithNormal,
      UnitaryCircuit.seq_eventCost, suffix_cost, ResourcePool.count_add,
      Inversion.normal_eventCost, Inversion.reusedForward_eventCost,
      Inversion.reusedBackward_eventCost, Control.restoreProgram_count,
      Window.Enable.inverseProgram_count, phaseSelection, transferProgram] <;> omega

private lemma transfer_native_counts (kind : Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (transferProgram kind stream width bounded).eventCost =
        Word.OneDirtyLayout.gateCount (width + 1) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (transferProgram kind stream width bounded).eventCost = transferCnot kind ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (transferProgram kind stream width bounded).eventCost = 2 * (width + 1) + 1 := by
  cases kind with
  | division => exact Control.prepareProgram_native_counts stream width bounded positive
  | multiplication => exact Window.Enable.program_native_counts stream width bounded positive

private lemma swap_gate_count (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
      Swap.program.eventCost = if AlgorithmGate.Coordinate.cnot = coordinate then 768 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Swap.program_eventTrace,
    ResourcePool.ofList_replicate, ResourcePool.count_scale, ResourcePool.count_singleton]
  cases coordinate <;> simp

lemma native_toffoli_count_le (kind : Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (positive : 1 ≤ width) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (nativePool kind stream width bounded outcome) ≤
        474737453 + 4 * Word.OneDirtyLayout.gateCount (width + 1) := by
  rw [native_count, Save.program_toffoli_count, Phase.program_toffoli_count,
    (transfer_native_counts kind stream width bounded positive).1, swap_gate_count]
  have resident := Inversion.program_toffoli_count_le
  simp only [reduceCtorEq, if_false]
  omega

lemma native_cnot_count_le (kind : Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (positive : 1 ≤ width) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (nativePool kind stream width bounded outcome) ≤
        301982217 + Phase.selectedCount outcome + 4 * transferCnot kind := by
  rw [native_count, Save.program_cnot_count, Phase.program_cnot_count,
    (transfer_native_counts kind stream width bounded positive).2.1, swap_gate_count]
  have resident := Inversion.program_cnot_count_le
  simp only [if_true]
  omega

/-- The native single-qubit count is exact; physical reset H/X is charged separately. -/
lemma native_singleQubit_count (kind : Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (positive : 1 ≤ width) (outcome : Word) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (nativePool kind stream width bounded outcome) =
        125477336 + 3 * Phase.selectedCount outcome + 4 * (2 * (width + 1) + 1) := by
  rw [native_count, Save.program_x_count, Phase.program_x_count,
    (transfer_native_counts kind stream width bounded positive).2.2, swap_gate_count,
    Inversion.program_singleQubit_count]
  simp only [reduceCtorEq, if_false]
  omega

lemma native_quantumTime_le (kind : Kind) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (outcome : Word) :
    (beforeReset kind stream width bounded).evaluatedEventDepth Resource.Event.quantumDuration +
        (tail kind stream width bounded outcome).evaluatedEventDepth
          Resource.Event.quantumDuration ≤
      822778665 + 4 * Phase.selectedCount outcome +
        4 * (2 * (width + 1) + Word.OneDirtyLayout.gateCount (width + 1) + 1 +
          transferCnot kind) := by
  have first := Inversion.normal_quantumTime_le
  have forward := Inversion.reusedForward_quantumTime_le
  have backward := Inversion.reusedBackward_quantumTime_le
  cases kind <;>
    simp only [beforeReset, tail, divisionTail, multiplicationTail,
      Control.firstResidentProgram, residentWithTemporary, residentWithNormal,
      UnitaryCircuit.evaluatedEventDepth_seq, Window.suffixProgram_quantumTime,
      Save.program_quantumTime, Phase.program_quantumTime, Swap.program_quantumTime,
      Control.prepareProgram_quantumTime, Control.restoreProgram_quantumTime,
      Window.Enable.program_quantumTime, Window.Enable.inverseProgram_quantumTime,
      transferCnot] <;> omega

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

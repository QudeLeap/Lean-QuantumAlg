/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import Mathlib.Data.Nat.Choose.Basic

/-!
# Native event counts of the recursive QFT word

Each count is a projection of the actual construction. The arbitrary event
coordinate also covers unused Toffoli and oracle coordinates.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

variable (oracles : OracleModel)
variable (event : Resource.Event (.quantum AlgorithmGate.model oracles))

private theorem phaseStep_count (n : Nat) (offset : Fin n) :
    ResourcePool.count event (phaseStep oracles n offset).eventCost =
      3 * (if .gate .singleQubit = event then 1 else 0) +
        2 * (if .gate .cnot = event then 1 else 0) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  unfold phaseStep
  rw [QFTPrimitive.qftPrimitive_circuit_events, ResourcePool.count_ofList]
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  omega

private theorem phasePrefix_count (n count : Nat) (bounded : count ≤ n) :
    ResourcePool.count event (phasePrefix oracles n count bounded).eventCost =
      count * (3 * (if .gate .singleQubit = event then 1 else 0) +
        2 * (if .gate .cnot = event then 1 else 0)) := by
  induction count with
  | zero => simp [phasePrefix]
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        phaseStep_count]
      ring

private theorem leadingHadamard_count (n : Nat) :
    ResourcePool.count event (leadingHadamard oracles n).eventCost =
      if .gate .singleQubit = event then 1 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.count event (ResourcePool.ofList [.gate .singleQubit]) = _
  rw [ResourcePool.count_ofList]
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]

private theorem tailLayer_count (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (QFTPrimitive.layout n)) :
    ResourcePool.count event (tailLayer oracles n body).eventCost =
      ResourcePool.count event body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost body]
  rw [tailLayer, UnitaryCircuit.placeAt_eventTrace]

private theorem noSwap_count (n : Nat) :
    ResourcePool.count event (noSwap oracles n).eventCost =
      n * (if .gate .singleQubit = event then 1 else 0) +
        n.choose 2 * (3 * (if .gate .singleQubit = event then 1 else 0) +
          2 * (if .gate .cnot = event then 1 else 0)) := by
  induction n with
  | zero => simp [noSwap]
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        leadingHadamard_count, phaseLayer, phasePrefix_count, tailLayer_count, ih]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

private theorem swapStep_count (n : Nat) (index : Fin (n / 2)) :
    ResourcePool.count event (swapStep oracles n index).eventCost =
      3 * (if .gate .cnot = event then 1 else 0) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  unfold swapStep
  rw [QFTPrimitive.qftPrimitive_circuit_events, ResourcePool.count_ofList]
  simp only [List.count_cons, List.count_nil, beq_iff_eq]
  omega

private theorem reversePrefix_count (n count : Nat) (bounded : count ≤ n / 2) :
    ResourcePool.count event (reversePrefix oracles n count bounded).eventCost =
      count * (3 * (if .gate .cnot = event then 1 else 0)) := by
  induction count with
  | zero => simp [reversePrefix]
  | succ count ih =>
      rw [reversePrefix, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        swapStep_count]
      ring

/-- Every actual event count is determined by the full native expansion of the same QFT word. -/
public theorem qftNative_circuit_event_count (n : Nat) :
    ResourcePool.count event (circuit oracles n).eventCost =
      (n + 3 * n.choose 2) * (if .gate .singleQubit = event then 1 else 0) +
        (2 * n.choose 2 + 3 * (n / 2)) * (if .gate .cnot = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, noSwap_count,
    bitReverse, reversePrefix_count]
  ring

end

end QuantumAlg.QuantumFourierTransform.Native

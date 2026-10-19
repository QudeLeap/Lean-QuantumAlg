/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Source.Primitive
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import Mathlib.Data.Nat.Choose.Basic

/-!
# Native event counts of the recursive QFT word

Each count is a projection of the actual native source construction. Every
other event coordinate has zero occurrences.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

variable (oracles : OracleModel)
variable (event : Resource.Event (.quantum FourierGate.model oracles))

private lemma phaseStep_count (n : Nat) (offset : Fin n) :
    ResourcePool.count event (phaseStep oracles n offset).eventCost =
      if .gate .controlledPhase = event then 1 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.count event (ResourcePool.ofList [.gate .controlledPhase]) = _
  simp

private lemma phasePrefix_count (n count : Nat) (bounded : count ≤ n) :
    ResourcePool.count event (phasePrefix oracles n count bounded).eventCost =
      count * (if .gate .controlledPhase = event then 1 else 0) := by
  induction count with
  | zero => simp [phasePrefix]
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ih,
        phaseStep_count]
      ring

private lemma leadingHadamard_count (n : Nat) :
    ResourcePool.count event (leadingHadamard oracles n).eventCost =
      if .gate .hadamard = event then 1 else 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ResourcePool.count event (ResourcePool.ofList [.gate .hadamard]) = _
  rw [ResourcePool.count_ofList]
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]

private lemma tailLayer_count (n : Nat)
    (body : UnitaryCircuit FourierGate.model oracles (QFTPrimitive.layout n)) :
    ResourcePool.count event (tailLayer oracles n body).eventCost =
      ResourcePool.count event body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost body]
  rw [tailLayer, UnitaryCircuit.placeAt_eventTrace]

private lemma noSwap_count (n : Nat) :
    ResourcePool.count event (noSwap oracles n).eventCost =
      n * (if .gate .hadamard = event then 1 else 0) +
        n.choose 2 * (if .gate .controlledPhase = event then 1 else 0) := by
  induction n with
  | zero => simp [noSwap]
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        leadingHadamard_count, phaseLayer, phasePrefix_count, tailLayer_count, ih]
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      ring

private lemma reversePrefix_count (n count : Nat) (bounded : count ≤ n / 2) :
    ResourcePool.count event (reversePrefix oracles n count bounded).eventCost =
      count * (if .gate .swap = event then 1 else 0) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, reversePrefix_eventTrace]
  by_cases same : Resource.Event.gate
      (model := .quantum FourierGate.model oracles) .swap = event <;>
    simp [ResourcePool.count_ofList, List.count_replicate, same]

/-- The three exact source counts come from actual native instruction occurrences. -/
public lemma qftSource_circuit_event_count (n : Nat) :
    ResourcePool.count event (circuit oracles n).eventCost =
      n * (if .gate .hadamard = event then 1 else 0) +
        n.choose 2 * (if .gate .controlledPhase = event then 1 else 0) +
          (n / 2) * (if .gate .swap = event then 1 else 0) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, ResourcePool.count_add, noSwap_count,
    bitReverse, reversePrefix_count]

/-- Complete native source ledger, including zero occurrences of every other event. -/
public lemma qftSource_circuit_eventCost (n : Nat) :
    (circuit oracles n).eventCost =
      ResourcePool.singleton (model := .quantum FourierGate.model oracles) (.gate .hadamard) n +
        ResourcePool.singleton (model := .quantum FourierGate.model oracles)
          (.gate .controlledPhase) (n.choose 2) +
          ResourcePool.singleton (model := .quantum FourierGate.model oracles)
            (.gate .swap) (n / 2) := by
  apply Multiset.ext.mpr
  intro coordinate
  change ResourcePool.count coordinate (circuit oracles n).eventCost = _
  rw [qftSource_circuit_event_count]
  simp [ResourcePool.singleton, Multiset.count_replicate, eq_comm]

end
end QuantumAlg.QuantumFourierTransform.Source

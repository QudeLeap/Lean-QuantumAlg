/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.Swap.Controlled.Register
import all QuantumAlg.Components.Gates.Swap.Controlled.Physical
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Native event multiplicities of the actual controlled register exchange

Every selected pair contributes exactly two CNOTs and one Toffoli. Counts come
from the executed sequence; no macro label supplies a cost or a workspace bound.
-/

namespace QuantumAlg.Gate.ControlledRegisterSwap

noncomputable section

private lemma pair_events (oracles : OracleModel) (width : Nat) (index : Fin width) :
    (pairCircuit oracles width index).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) 2 + ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, pairCircuit,
    ControlledSwap.controlledSwap_circuitAt_events]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  change ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) +
      (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) + ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot)) =
    (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) + ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot)) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli)
  ac_rfl

private lemma sequence_cost (oracles : OracleModel) (width : Nat) (indices : List (Fin width)) :
    (sequence oracles width indices).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) (2 * indices.length) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [sequence, UnitaryCircuit.seq_eventCost, pair_events, ih, List.length_cons]
      have twice : 2 * (rest.length + 1) = 2 + 2 * rest.length := by omega
      rw [twice]
      change (_ + _) + (_ + _) =
        Multiset.replicate (2 + 2 * rest.length) _ + Multiset.replicate (rest.length + 1) _
      rw [Multiset.replicate_add, Multiset.replicate_add]
      simp only [ResourcePool.singleton]
      ac_rfl

/-- Exact native gate pool for the actual all-position controlled exchange. -/
public lemma controlledRegisterSwap_eventCost (oracles : OracleModel) (width : Nat) :
    (circuit oracles width).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .cnot) (2 * width) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) width := by
  change (sequence oracles width (List.finRange width)).eventCost = _
  rw [sequence_cost, List.length_finRange]

end

end QuantumAlg.Gate.ControlledRegisterSwap

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Elementary.Construction
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Components.Oracle.Common

/-!
# The elementary Grover circuit's own independent event and depth formulas

Every iteration contains one actual predicate query, two parallel Hadamard
layers and the selected elementary positive zero reflection. The independent
formulas preserve those H layers as parallel layers. The same actual source
program and its retained work suffix prove all ledger and depth equalities.
-/

namespace QuantumAlg.GroverSearch.Elementary

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- Width-only layer duration of the original parallel Hadamards. -/
def hadamardDepth (n : Nat) : Nat := if n = 0 then 0 else 1

/-- Independent native occurrences for the complete search unitary. -/
def unitaryEventPool (n k : Nat) : ResourcePool .quantum :=
  n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
    k • (ResourcePool.singleton (.quantumSubroutine (phaseOracleSubroutineLabel n).quantum) +
      (n • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        (ZeroReflection.elementaryEventPool n +
          n • ResourcePool.singleton (.gate (.builtin "hadamard")))))

/-- Independent depth keeps each source Hadamard tensor as one nonempty parallel layer. -/
def unitaryDepth (n k : Nat) : Nat :=
  hadamardDepth n + k * (1 + (hadamardDepth n +
    (ZeroReflection.elementaryGateCount n + hadamardDepth n)))

/-- Independent total elementary gate count excludes the separately charged source queries. -/
def unitaryGateCount (n k : Nat) : Nat :=
  n + k * (2 * n + ZeroReflection.elementaryGateCount n)

private theorem hadamards_eventCost (n k : Nat) :
    (hadamards n k).eventCost = n • ResourcePool.singleton (.gate (.builtin "hadamard")) := by
  rw [hadamards, UnitaryCircuit.idleSuffix_eventCost, initialPreparationCircuit,
    WalshHadamard.hadamardLayer_eventCost]
  apply Multiset.ext.mpr
  intro event
  simp only [ResourcePool.singleton, WalshHadamard.hadamardEvent,
    Multiset.count_replicate, Multiset.count_nsmul]
  split <;> simp_all

private theorem hadamards_unitDepth (n k : Nat) :
    (hadamards n k).evaluatedEventDepth (fun _ => 1) = hadamardDepth n := by
  rw [hadamards, UnitaryCircuit.idleSuffix_evaluatedEventDepth]
  change DepthExpr.depthEval (fun _ => 1) (WalshHadamard.hadamardLayer n).eventDepth = _
  rw [WalshHadamard.hadamardLayer_eventDepth,
    WalshHadamard.parallelHadamardEventDepth_unit_depth]
  rfl

private theorem oracle_eventCost {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (oracle marked k).eventCost =
      ResourcePool.singleton (.quantumSubroutine (phaseOracleSubroutineLabel n).quantum) := by
  have within : (phaseOracleCircuit marked).physical_idx ⊆ List.range n :=
    List.Subset.refl _
  exact (UnitaryCircuit.idleSuffix_eventCost (phaseOracleCircuit marked) within
    (helperWidth n k)).trans (phaseOracleCircuit_eventCost marked)

private theorem oracle_unitDepth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (oracle marked k).evaluatedEventDepth (fun _ => 1) = 1 := by
  have within : (phaseOracleCircuit marked).physical_idx ⊆ List.range n :=
    List.Subset.refl _
  calc
    _ = (phaseOracleCircuit marked).evaluatedEventDepth (fun _ => 1) :=
      UnitaryCircuit.idleSuffix_evaluatedEventDepth (phaseOracleCircuit marked) within
        (helperWidth n k) (fun _ => 1)
    _ = _ := by
      rw [UnitaryCircuit.evaluatedEventDepth, phaseOracleCircuit_eventDepth]
      rfl

/-- The actual complete elementary search unitary has exactly the independent native ledger. -/
theorem circuit_eventCost {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).eventCost = unitaryEventPool n k := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero]
  by_cases zero : k = 0
  · subst k
    rw [body, dif_pos rfl, hadamards_eventCost]
    simp only [unitaryEventPool, zero_nsmul, add_zero]
  · simp only [body, dif_neg zero, step, diffusion, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.iterate_eventCost, UnitaryCircuit.dagger_eventCost,
      hadamards_eventCost, oracle_eventCost, reflection_eventCost]
    rfl

/-- Unit-event depth is derived from the actual parallel H syntax and sequential reflection. -/
theorem circuit_unitDepth {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).evaluatedEventDepth (fun _ => 1) = unitaryDepth n k := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq]
  have finalIdentity :
      (UnitaryCircuit.identity (Qubits (totalQubits n k))
        (List.range (totalQubits n k)) List.nodup_range).evaluatedEventDepth (fun _ => 1) = 0 := rfl
  rw [finalIdentity, add_zero]
  by_cases zero : k = 0
  · subst k
    rw [body, dif_pos rfl, hadamards_unitDepth]
    simp only [unitaryDepth, Nat.zero_mul, Nat.add_zero]
  · simp only [body, dif_neg zero, step, diffusion, UnitaryCircuit.evaluatedEventDepth_seq,
      UnitaryCircuit.evaluatedEventDepth_iterate, UnitaryCircuit.evaluatedEventDepth_dagger,
      hadamards_unitDepth, oracle_unitDepth, reflection_unitDepth]
    rfl

/-- The actual elementary gate total follows from its own native ledger. -/
theorem circuit_gateCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (circuit marked k).eventCost = unitaryGateCount n k := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (circuit marked k).eventCost = _
  have reflected : ResourcePool.weightedCount weight (ZeroReflection.elementaryEventPool n) =
      ZeroReflection.elementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_gateCount n)
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool n))
    funext event
    cases event <;> rfl
  rw [circuit_eventCost]
  simp only [unitaryEventPool, unitaryGateCount, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight]
  ring

/-- All source-query occurrences in this same elementary execution are the original k queries. -/
theorem circuit_queryCount {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .quantumSubroutine _ => 1 | _ => 0) (circuit marked k).eventCost = k := by
  let weight : Resource.Event .quantum → Nat := fun event => match event with
    | .quantumSubroutine _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (circuit marked k).eventCost = _
  have reflected :
      ResourcePool.weightedCount weight (ZeroReflection.elementaryEventPool n) = 0 := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_queryCount n)
    apply congrArg (fun assignment : Resource.Event .quantum → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool n))
    funext event
    cases event <;> rfl
  rw [circuit_eventCost]
  simp only [unitaryEventPool, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight]
  ring

end

end QuantumAlg.GroverSearch.Elementary

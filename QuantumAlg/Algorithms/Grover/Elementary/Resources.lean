/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Elementary.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Weighted

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
def unitaryEventPool (n : Nat) (k : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (oracles n)) :=
  n • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n)) (.gate .singleQubit) +
    k • (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n)) (.oracle .ordinary) +
      ((n • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model (oracles n)) (.gate .singleQubit) +
        ZeroReflection.elementaryEventPool (oracles n) n) +
          n • ResourcePool.singleton
            (model := .quantum AlgorithmGate.model (oracles n)) (.gate .singleQubit)))

/-- Independent depth keeps each source Hadamard tensor as one nonempty parallel layer. -/
def unitaryDepth (n k : Nat) : Nat :=
  hadamardDepth n + k * (1 + (hadamardDepth n +
    (ZeroReflection.elementaryGateCount n + hadamardDepth n)))

/-- Independent total elementary gate count excludes the separately charged source queries. -/
def unitaryGateCount (n k : Nat) : Nat :=
  n + k * (2 * n + ZeroReflection.elementaryGateCount n)

private lemma hadamards_eventCost (queries : OracleModel) (n k : Nat) :
    (hadamards queries n k).eventCost = n • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model queries) (.gate .singleQubit) := by
  rw [hadamards, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost]
  exact Gate.HadamardLayer.hadamardLayer_circuit_eventCost queries n

private lemma inverseHadamards_eventCost (queries : OracleModel) (n k : Nat) :
    (inverseHadamards queries n k).eventCost = n • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model queries) (.gate .singleQubit) := by
  rw [inverseHadamards, AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    hadamards_eventCost, map_nsmul]
  rfl

private lemma hadamards_unitDepth (queries : OracleModel) (n k : Nat) :
    (hadamards queries n k).evaluatedEventDepth (fun _ => 1) = hadamardDepth n := by
  rw [hadamards, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_unit_depth]
  exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth queries n

private lemma inverseHadamards_unitDepth (queries : OracleModel) (n k : Nat) :
    (inverseHadamards queries n k).evaluatedEventDepth (fun _ => 1) = hadamardDepth n := by
  rw [inverseHadamards, AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth,
    hadamards_unitDepth]

private lemma oracle_eventCost (n : Nat) (k : Nat) :
    (oracle n k).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (oracles n)) (.oracle .ordinary) := rfl

private lemma oracle_unitDepth (n : Nat) (k : Nat) :
    (oracle n k).evaluatedEventDepth (fun _ => 1) = 1 := rfl

/-- The complete elementary search unitary has exactly the independent native ledger. -/
lemma circuit_eventCost (n : Nat) (k : Nat) :
    (circuit n k).eventCost = unitaryEventPool n k := by
  by_cases zero : k = 0
  · subst k
    rw [circuit, dif_pos rfl, hadamards_eventCost]
    simp only [unitaryEventPool, zero_nsmul, add_zero]
  · simp only [circuit, dif_neg zero, step, diffusion, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.iterate_eventCost, inverseHadamards_eventCost,
      hadamards_eventCost, oracle_eventCost, reflection_eventCost]
    rfl

/-- Depth is derived from the actual parallel H syntax and sequential reflection. -/
lemma circuit_unitDepth (n : Nat) (k : Nat) :
    (circuit n k).evaluatedEventDepth (fun _ => 1) = unitaryDepth n k := by
  have repeated (count : Nat)
      (body : UnitaryCircuit AlgorithmGate.model (oracles n)
        (QuantumSignature.qubits (totalQubits n k)).canonicalPlacement.layout) :
      (UnitaryCircuit.iterate count body).evaluatedEventDepth (fun _ => 1) =
        count * body.evaluatedEventDepth (fun _ => 1) := rfl
  by_cases zero : k = 0
  · subst k
    rw [circuit, dif_pos rfl, hadamards_unitDepth]
    simp only [unitaryDepth, Nat.zero_mul, Nat.add_zero]
  · simp only [circuit, dif_neg zero, step, diffusion, UnitaryCircuit.evaluatedEventDepth_seq,
      repeated, inverseHadamards_unitDepth, hadamards_unitDepth, oracle_unitDepth,
      reflection_unitDepth]
    simp only [unitaryDepth, Nat.add_assoc]

/-- The actual elementary gate total follows from its own native ledger. -/
lemma circuit_gateCount (n : Nat) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) (circuit n k).eventCost = unitaryGateCount n k := by
  let weight : Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat :=
    fun event => match event with
    | .gate _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (circuit n k).eventCost = _
  have reflected : ResourcePool.weightedCount weight
      (ZeroReflection.elementaryEventPool (oracles n) n) =
      ZeroReflection.elementaryGateCount n := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_gateCount (oracles n) n)
    apply congrArg (fun assignment :
        Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool (oracles n) n))
    funext event
    cases event <;> rfl
  rw [circuit_eventCost]
  simp only [unitaryEventPool, unitaryGateCount, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton]
  rw [reflected]
  dsimp only [weight]
  ring

/-- All source-query occurrences in this same elementary execution are the original k queries. -/
lemma circuit_queryCount (n : Nat) (k : Nat) :
    ResourcePool.weightedCount (fun event => match event with
      | .oracle _ => 1 | _ => 0) (circuit n k).eventCost = k := by
  let weight : Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat :=
    fun event => match event with
    | .oracle _ => 1 | _ => 0
  change ResourcePool.weightedCount weight (circuit n k).eventCost = _
  have reflected :
      ResourcePool.weightedCount weight
        (ZeroReflection.elementaryEventPool (oracles n) n) = 0 := by
    refine Eq.trans ?_ (ZeroReflection.elementaryEventPool_queryCount (oracles n) n)
    apply congrArg (fun assignment :
        Resource.Event (.quantum AlgorithmGate.model (oracles n)) → Nat =>
      ResourcePool.weightedCount assignment (ZeroReflection.elementaryEventPool (oracles n) n))
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

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary

/-!
# Opaque-subroutine exclusion for concrete finite-cyclic unitaries

This module derives the original conditional opaque-subroutine exclusion
from the actual unitary range preparation, Fourier readout and oracle.
It imposes no condition on the native discrete-logarithm endpoint.
-/

section

namespace QuantumAlg

noncomputable section

namespace FiniteCyclicDLP
namespace ConcreteCircuitAccess

universe u

variable {G : Type u} [Group G]

/-- A circuit's actual event pool has no opaque quantum-subroutine coordinate. -/
private abbrev QuantumSubroutineFree {R : Register} (circuit : UnitaryCircuit R) : Prop :=
  ∀ label : Resource.QuantumSubroutineLabel,
    ResourcePool.count (.quantumSubroutine label) circuit.eventCost = 0

private theorem quantumSubroutineFree_seq {R : Register}
    {left right : UnitaryCircuit R}
    (hleft : QuantumSubroutineFree left)
    (hright : QuantumSubroutineFree right) :
    QuantumSubroutineFree (UnitaryCircuit.seq left right) := by
  intro label
  simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    hleft label, hright label, Nat.zero_add]

private theorem dagger_eventCost {R : Register} (circuit : UnitaryCircuit R) :
    circuit.dagger.eventCost = circuit.eventCost :=
  rfl

private theorem quantumSubroutineFree_dagger {R : Register}
    {circuit : UnitaryCircuit R} (hcircuit : QuantumSubroutineFree circuit) :
    QuantumSubroutineFree circuit.dagger := by
  intro label
  rw [dagger_eventCost]
  exact hcircuit label

private theorem quantumSubroutineFree_pairConsecutiveCircuit
    {n : Nat} (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n)
    (hbody : QuantumSubroutineFree body) :
    QuantumSubroutineFree (pairConsecutiveCircuit body hphysical) := by
  intro label
  simp only [pairConsecutiveCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.shiftPhysicalIdx_eventCost, ResourcePool.count_add,
    hbody label, Nat.zero_add]

private theorem quantumSubroutineFree_extendWithTail
    {P : KnownOrderProblem G} {n : Nat} (A : ConcreteCircuitAccess P)
    (body : UnitaryCircuit (Qubits n))
    (hphysical : body.physical_idx = List.range n)
    (hbody : QuantumSubroutineFree body) :
    QuantumSubroutineFree (A.extendWithTail body hphysical) := by
  intro label
  simp only [extendWithTail, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex_eventCost, UnitaryCircuit.tensor_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add,
    hbody label, ResourcePool.count_zero, Nat.add_zero]

private theorem rangePreparationCircuit_quantumSubroutine_count_zero
    {P : KnownOrderProblem G} (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
        (rangePreparationCircuit P).eventCost = 0 := by
  simp only [rangePreparationCircuit, UnitaryCircuit.leaf_eventCost,
    rangePreparationLeaf, Gate.finiteCyclicRangePreparationLeafAt,
    UnitaryLeaf.gate_event]
  exact ResourcePool.count_singleton_of_ne (by
    intro equality
    cases equality) 1

private theorem qftPhaseLayerPrefix_quantumSubroutine_count_zero
    (label : Resource.QuantumSubroutineLabel) (n count : Nat)
    (hcount : count ≤ n) :
    ResourcePool.count (.quantumSubroutine label)
        (qftPhaseLayerPrefix n count hcount).eventCost = 0 := by
  induction count with
  | zero => simp [qftPhaseLayerPrefix]
  | succ count ih =>
      rw [qftPhaseLayerPrefix, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add, ih (by omega)]
      change ResourcePool.count (.quantumSubroutine label)
          (ResourcePool.singleton (.gate qftControlledPhaseLabel)) = 0
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        cases equality) 1

private theorem qftBitReversePrefix_quantumSubroutine_count_zero
    (label : Resource.QuantumSubroutineLabel) (n count : Nat)
    (hcount : count ≤ n / 2) :
    ResourcePool.count (.quantumSubroutine label)
        (qftBitReversePrefix n count hcount).eventCost = 0 := by
  induction count with
  | zero => simp [qftBitReversePrefix]
  | succ count ih =>
      rw [qftBitReversePrefix, UnitaryCircuit.seq_eventCost,
        ResourcePool.count_add, ih (by omega)]
      change ResourcePool.count (.quantumSubroutine label)
          (ResourcePool.singleton (.gate (.builtin "swap"))) = 0
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        cases equality) 1

private theorem qftNoSwapCircuit_quantumSubroutine_count_zero
    (label : Resource.QuantumSubroutineLabel) (n : Nat) :
    ResourcePool.count (.quantumSubroutine label)
        (qftNoSwapCircuit n).eventCost = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ResourcePool.count (.quantumSubroutine label)
          ((qftLeadingHadamard n).eventCost +
            ((qftPhaseLayer n).eventCost +
              (qftTailLayer n (qftNoSwapCircuit n)
                (qftNoSwapCircuit_physical_idx n)).eventCost)) = 0
      rw [ResourcePool.count_add, ResourcePool.count_add]
      have leading : ResourcePool.count (.quantumSubroutine label)
          (qftLeadingHadamard n).eventCost = 0 := by
        change ResourcePool.count (.quantumSubroutine label)
            (ResourcePool.singleton (.gate (.builtin "hadamard"))) = 0
        exact ResourcePool.count_singleton_of_ne (by
          intro equality
          cases equality) 1
      have phase : ResourcePool.count (.quantumSubroutine label)
          (qftPhaseLayer n).eventCost = 0 :=
        qftPhaseLayerPrefix_quantumSubroutine_count_zero label n n le_rfl
      have tail : ResourcePool.count (.quantumSubroutine label)
          (qftTailLayer n (qftNoSwapCircuit n)
            (qftNoSwapCircuit_physical_idx n)).eventCost = 0 := by
        simpa [qftTailLayer] using ih
      rw [leading, phase, tail]

private theorem qftCircuit_quantumSubroutine_count_zero
    (label : Resource.QuantumSubroutineLabel) (n : Nat) :
    ResourcePool.count (.quantumSubroutine label) (QFTCircuit n).eventCost = 0 := by
  have noSwap := qftNoSwapCircuit_quantumSubroutine_count_zero label n
  have reverse :=
    qftBitReversePrefix_quantumSubroutine_count_zero label n (n / 2) le_rfl
  rw [QFTCircuit, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  simpa [qftBitReverseCircuit] using congrArg₂ Nat.add noSwap reverse

private theorem quantumSubroutineFree_exponentPreparationCircuit
    {P : KnownOrderProblem G} :
    QuantumSubroutineFree (exponentPreparationCircuit P) := by
  simpa only [exponentPreparationCircuit] using
    quantumSubroutineFree_pairConsecutiveCircuit (rangePreparationCircuit P)
      (by rfl) (fun label =>
        rangePreparationCircuit_quantumSubroutine_count_zero label)

private theorem quantumSubroutineFree_exponentReadoutCircuit
    {P : KnownOrderProblem G} :
    QuantumSubroutineFree (exponentReadoutCircuit P) := by
  have qft : QuantumSubroutineFree (QFTCircuit (orderWidth P)) :=
    fun label => qftCircuit_quantumSubroutine_count_zero label _
  have inverseQft : QuantumSubroutineFree
      (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))) :=
    quantumSubroutineFree_dagger qft
  simpa only [exponentReadoutCircuit] using
    quantumSubroutineFree_pairConsecutiveCircuit
      (UnitaryCircuit.dagger (QFTCircuit (orderWidth P))) (by simp) inverseQft

private theorem quantumSubroutineFree_preparationCircuit
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P) :
    QuantumSubroutineFree A.preparationCircuit := by
  simpa only [preparationCircuit] using
    quantumSubroutineFree_extendWithTail A (exponentPreparationCircuit P)
      (exponentPreparationCircuit_physical_idx P)
      quantumSubroutineFree_exponentPreparationCircuit

private theorem quantumSubroutineFree_readoutCircuit
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P) :
    QuantumSubroutineFree A.readoutCircuit := by
  simpa only [readoutCircuit] using
    quantumSubroutineFree_extendWithTail A (exponentReadoutCircuit P)
      (exponentReadoutCircuit_physical_idx P)
      quantumSubroutineFree_exponentReadoutCircuit

private theorem quantumSubroutineFree_oracleCircuit
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    [OracleCircuitQuantumSubroutineFree A] :
    QuantumSubroutineFree A.oracleCircuit :=
  fun label => A.oracleCircuit_quantumSubroutine_count_zero label

private theorem quantumSubroutineFree_fullCircuit
    {P : KnownOrderProblem G} (A : ConcreteCircuitAccess P)
    [OracleCircuitQuantumSubroutineFree A] :
    QuantumSubroutineFree A.fullCircuit := by
  simpa only [fullCircuit] using
    quantumSubroutineFree_seq
      (quantumSubroutineFree_preparationCircuit A)
      (quantumSubroutineFree_seq
        (quantumSubroutineFree_oracleCircuit A)
        (quantumSubroutineFree_readoutCircuit A))


end ConcreteCircuitAccess
end FiniteCyclicDLP

end

end QuantumAlg

end

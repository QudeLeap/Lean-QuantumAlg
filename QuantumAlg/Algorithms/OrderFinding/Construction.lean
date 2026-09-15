/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard

/-!
# The actual phase preparation, source query and inverse QFT

One sealed query acts between phase-register Hadamards and the inverse QFT
[dW19, qcnotes.tex:2203-2225]. The circuit's actual sequence owns its
permutation, placements and query/gate events. It contains no measurement.
-/

namespace QuantumAlg

open NormalizedVector Gate

noncomputable section

namespace OrderFinding

/-! ## Complete circuit -/

/-- Canonical disjoint placement of the phase and target registers. -/
theorem phaseTargetLayout (t m : Nat) (phase : UnitaryCircuit (Qubits t))
    (hphase : phase.physical_idx = List.range t) :
    PhysicalLayout.DisjointMerge phase.physical_idx (List.range' t m) :=
  { left_nodup := phase.physical_idx_nodup
    right_nodup := List.nodup_range'
    disjoint := by
      rw [hphase, List.disjoint_left]
      intro index hleft hright
      have hlt := List.mem_range.mp hleft
      have hle := List.left_le_of_mem_range' hright
      omega }

theorem phaseTargetRange (t m : Nat) :
    List.range t ++ List.range' t m = List.range (t + m) := by
  simpa [List.range_eq_range'] using
    (List.range'_append_1 (s := 0) (m := t) (n := m))

/-- Hadamards on the phase register and identity on the target register. -/
def orderFindingPreparationCircuit (t m : Nat) : UnitaryCircuit (Qubits (t + m)) :=
  let target := UnitaryCircuit.identity (Qubits m) (List.range' t m) List.nodup_range'
  UnitaryCircuit.tensorQubits (WalshHadamard.hadamardLayer t) target
    (phaseTargetLayout t m _ (WalshHadamard.hadamardLayer_physical_idx t))

@[simp]
theorem orderFindingPreparationCircuit_physical_idx (t m : Nat) :
    (orderFindingPreparationCircuit t m).physical_idx = List.range (t + m) := by
  simp only [orderFindingPreparationCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex, UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append,
    WalshHadamard.hadamardLayer_physical_idx]
  exact phaseTargetRange t m

/-- Strict event label for the modular-exponentiation subroutine. -/
def modExpSubroutineLabel (N x t m : Nat) : Resource.SubroutineLabel :=
  { family := "order-finding"
    name := "order-finding-modular-exponentiation"
    parameters := [N, x, t, m] }

/-- Strict resource coordinate for the single modular-exponentiation call. -/
public def modExpEvent (N x t m : Nat) : Resource.Event .quantum :=
  .quantumSubroutine (modExpSubroutineLabel N x t m).quantum

namespace EndpointDeclarations

/-- Declared modular-exponentiation endpoint at a caller-supplied placement. -/
def orderFindingOracleLeafAt {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) (systemIdx : List Nat) :
    UnitaryLeaf (Qubits (t + m)) :=
  UnitaryLeaf.subroutine (modExpSubroutineLabel N x t m)
    systemIdx (modExpOracle A)

end EndpointDeclarations

/-- The real oracle as one sealed opaque-subroutine leaf. -/
def orderFindingOracleLeaf {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    UnitaryLeaf (Qubits (t + m)) :=
  EndpointDeclarations.orderFindingOracleLeafAt A (List.range (t + m))

/-- The sealed modular-exponentiation oracle circuit. -/
def orderFindingOracleCircuit {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    UnitaryCircuit (Qubits (t + m)) :=
  UnitaryCircuit.ofLeaf (orderFindingOracleLeaf A) List.nodup_range

@[simp]
theorem orderFindingOracleCircuit_physical_idx {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingOracleCircuit A).physical_idx = List.range (t + m) :=
  rfl

@[simp] theorem orderFindingOracleCircuit_eventCost {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingOracleCircuit A).eventCost =
      ResourcePool.singleton (modExpEvent N x t m) := by
  rfl

/-- Inverse QFT on the phase register and identity on the target register. -/
def orderFindingReadoutCircuit (t m : Nat) : UnitaryCircuit (Qubits (t + m)) :=
  let target := UnitaryCircuit.identity (Qubits m) (List.range' t m) List.nodup_range'
  UnitaryCircuit.tensorQubits (UnitaryCircuit.dagger (QFTCircuit t)) target
    (phaseTargetLayout t m _ (by simp))

@[simp]
theorem orderFindingReadoutCircuit_physical_idx (t m : Nat) :
    (orderFindingReadoutCircuit t m).physical_idx = List.range (t + m) := by
  simp only [orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits,
    UnitaryCircuit.reindex, UnitaryCircuit.tensor, PhysicalLayout.DisjointMerge.merged_eq_append,
    UnitaryCircuit.dagger_physical_idx, QFTCircuit_physical_idx]
  exact phaseTargetRange t m

/-- Tensoring the inverse-QFT readout with an identity target preserves the
shared QFT strict event pool. -/
@[simp]
theorem orderFindingReadoutCircuit_eventCost (t m : Nat) :
    (orderFindingReadoutCircuit t m).eventCost = (QFTCircuit t).eventCost := by
  simp [orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits]

/-- Exact strict gate-coordinate multiplicities of the order-finding
inverse-QFT readout, from the same shared QFT event ledger. -/
theorem orderFindingReadoutCircuit_exact_event_gate_counts (t m : Nat) :
    ResourcePool.count (.gate (.builtin "hadamard"))
        (orderFindingReadoutCircuit t m).eventCost = t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel)
          (orderFindingReadoutCircuit t m).eventCost = t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap"))
          (orderFindingReadoutCircuit t m).eventCost = t / 2 := by
  rw [orderFindingReadoutCircuit_eventCost]
  exact QFTCircuit_exact_event_gate_counts t

/-- Complete access circuit used by both order-finding algorithms. -/
def orderFindingCircuit {N x t m : Nat} (A : ModExpOracleAccess N x t m) :
    UnitaryCircuit (Qubits (t + m)) :=
  UnitaryCircuit.seq (orderFindingPreparationCircuit t m)
    (UnitaryCircuit.seq (orderFindingOracleCircuit A) (orderFindingReadoutCircuit t m))

/-- Literal source order of preparation, modular exponentiation, and inverse
QFT readout in the circuit executed by the typed endpoint. -/
@[simp] theorem orderFindingCircuit_eventTrace {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingCircuit A).eventTrace =
      (orderFindingPreparationCircuit t m).eventTrace ++
        (orderFindingOracleCircuit A).eventTrace ++
          (orderFindingReadoutCircuit t m).eventTrace := by
  rw [orderFindingCircuit, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.seq_eventTrace]
  rw [List.append_assoc]

@[simp] theorem orderFindingCircuit_physical_idx {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingCircuit A).physical_idx = List.range (t + m) :=
  by simp [orderFindingCircuit, UnitaryCircuit.seq]

/-- Strict event envelope of the same three structural circuit segments. -/
@[simp] theorem orderFindingCircuit_eventCost {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingCircuit A).eventCost =
      ResourcePool.singleton WalshHadamard.hadamardEvent t +
        (ResourcePool.singleton (modExpEvent N x t m) +
          (QFTCircuit t).eventCost) := by
  have hdagger :
      (UnitaryCircuit.dagger (QFTCircuit t)).eventCost = (QFTCircuit t).eventCost := rfl
  simp [orderFindingCircuit, orderFindingPreparationCircuit,
    orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits, hdagger]

/-- Basis action of the typed modular-exponentiation component. -/
theorem orderFindingOracleCircuit_apply_ket {N x t m : Nat}
    (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    UnitaryCircuit.applyNormalized (orderFindingOracleCircuit A)
        (NormalizedVector.ket (R := Qubits (t + m)) (prodEquiv (a, y))) =
      NormalizedVector.ket (R := Qubits (t + m))
        (prodEquiv (a, modExpOracleTarget A a y)) := by
  change (modExpOracle A).apply
      (NormalizedVector.ket (R := Qubits (t + m)) (prodEquiv (a, y))) = _
  exact modExpOracle_apply_ket A a y

/-! ## Exact same-circuit counts -/

private theorem qftPhaseLayerPrefix_modExpCount_zero
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

private theorem qftBitReversePrefix_modExpCount_zero
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

private theorem qftNoSwapCircuit_modExpCount_zero
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
            (ResourcePool.singleton WalshHadamard.hadamardEvent) = 0
        exact ResourcePool.count_singleton_of_ne (by
          intro equality
          cases equality) 1
      have phase : ResourcePool.count (.quantumSubroutine label)
          (qftPhaseLayer n).eventCost = 0 :=
        qftPhaseLayerPrefix_modExpCount_zero label n n le_rfl
      have tail : ResourcePool.count (.quantumSubroutine label)
          (qftTailLayer n (qftNoSwapCircuit n)
            (qftNoSwapCircuit_physical_idx n)).eventCost = 0 := by
        simpa [qftTailLayer] using ih
      rw [leading, phase, tail]

private theorem qftCircuit_modExpCount_zero
    (label : Resource.QuantumSubroutineLabel) (t : Nat) :
    ResourcePool.count (.quantumSubroutine label)
        (QFTCircuit t).eventCost = 0 := by
  have noSwap := qftNoSwapCircuit_modExpCount_zero label t
  have reverse := qftBitReversePrefix_modExpCount_zero
    label t (t / 2) le_rfl
  rw [QFTCircuit, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  simpa [qftBitReverseCircuit] using congrArg₂ Nat.add noSwap reverse

/-- Exactly one modular-exponentiation event occurs in the complete circuit;
the preparation and inverse-QFT readout cannot contribute that coordinate. -/
theorem orderFindingCircuit_modExpMultiplicity {N x t m : Nat}
    (A : ModExpOracleAccess N x t m) :
    ResourcePool.count (modExpEvent N x t m)
        (orderFindingCircuit A).eventCost = 1 := by
  have preparation : ResourcePool.count (modExpEvent N x t m)
      (ResourcePool.singleton WalshHadamard.hadamardEvent t) = 0 := by
    exact ResourcePool.count_singleton_of_ne (by
      intro equality
      cases equality) t
  have readout : ResourcePool.count (modExpEvent N x t m)
      (QFTCircuit t).eventCost = 0 := by
    exact qftCircuit_modExpCount_zero
      (modExpSubroutineLabel N x t m).quantum t
  rw [orderFindingCircuit_eventCost, ResourcePool.count_add,
    ResourcePool.count_add, preparation, readout]
  simp [ResourcePool.count, ResourcePool.singleton]
end OrderFinding

end

end QuantumAlg

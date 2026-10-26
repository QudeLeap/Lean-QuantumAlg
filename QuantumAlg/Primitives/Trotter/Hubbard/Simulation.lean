/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Hubbard.Blocks
public import QuantumAlg.Primitives.Trotter.Hubbard.NativeCost
public import QuantumAlg.Analysis.Trotter.Hubbard
import all QuantumAlg.Primitives.Trotter.Hubbard.Blocks
import all QuantumAlg.Primitives.Trotter.Hubbard.NativeCost
import all QuantumAlg.Primitives.Trotter.Circuit.Blocks
import all QuantumAlg.Components.Pauli.FermiHubbard.Grouping
import all QuantumAlg.Analysis.Trotter.Hubbard
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Components.Gates.GlobalPhase
import all QuantumAlg.Components.Gates

/-!
# Native second-order Hubbard simulation

The original I, P, G factories are exact. Each symmetric step retains the
forward and reverse half passes, including both central visits. Iteration
therefore has only the outer second-order error. The full chemical shift,
zero-angle entries and all per-site scalar phases remain in the circuit.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- Repeated, unmerged symmetric execution of the three original exact blocks. -/
@[expose] def trotterSecond (L : ℕ) [NeZero L] (τ u μ t : ℝ) (r : ℕ) :
    Trotter.NativeCircuit (2 * L ^ 2) :=
  Trotter.secondBlocks (plaqCircuits L τ u μ) t r

lemma trotterSecond_matrix {L : ℕ} [NeZero L] (hL : Even L) (τ u μ t : ℝ) (r : ℕ) :
    (trotterSecond L τ u μ t r).binaryOperator =
      Trotter.secondOrderStep (plaqFamily L τ u μ) (t / (r : ℝ)) ^ r :=
  Trotter.secondBlocks_matrix _ _ (plaqCircuits_matrix hL τ u μ) t r

/-- Actual full-phase realization in the default model on the complete physical layout. -/
@[expose] def trotterSecondRealization {L : ℕ} [NeZero L] (hL : Even L) (τ u μ t : ℝ)
    (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (Trotter.nativeLayout (2 * L ^ 2))
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (2 * L ^ 2)).symm
        (timeEvolution (hamiltonian L τ u μ) t)) (trotterSecondError L τ u μ t r) :=
  Trotter.NativeCircuit.approximate (trotterSecond L τ u μ t r) _ _ (by
    rw [trotterSecond_matrix hL, ← plaqFamily_sum hL]
    exact Trotter.secondOrder_repeated_error_bound (plaqFamily L τ u μ) t ht r hr)

/-- The same complete circuit obeys the local, chemical-independent commutator bound. -/
lemma trotterSecond_matrix_error_le {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    HilbertOperator.opNorm
      (((trotterSecond L τ u μ t r).binaryOperator : HilbertOperator (Qubits (2 * L ^ 2))) -
        (timeEvolution (hamiltonian L τ u μ) t : HilbertOperator (Qubits (2 * L ^ 2)))) ≤
      (t ^ 3 / (12 * (r : ℝ) ^ 2)) * commutatorBound L τ u := by
  have hb : HilbertOperator.opNorm
      (((trotterSecond L τ u μ t r).binaryOperator : HilbertOperator (Qubits (2 * L ^ 2))) -
        (timeEvolution (hamiltonian L τ u μ) t : HilbertOperator (Qubits (2 * L ^ 2)))) ≤
      trotterSecondError L τ u μ t r := by
    rw [trotterSecond_matrix hL, ← plaqFamily_sum hL]
    exact Trotter.secondOrder_repeated_error_bound (plaqFamily L τ u μ) t ht r hr
  exact hb.trans (trotterSecondError_le hL hsize τ u μ t ht r)

/-- The actual full-phase word has the local quadratic-area error coefficient. -/
lemma trotterSecond_localError_le {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    HilbertOperator.opNorm
      (((trotterSecond L τ u μ t r).binaryOperator : HilbertOperator (Qubits (2 * L ^ 2))) -
        (timeEvolution (hamiltonian L τ u μ) t : HilbertOperator (Qubits (2 * L ^ 2)))) ≤
      (t ^ 3 / (r : ℝ) ^ 2) * localErrorCoefficient L τ u := by
  rw [← trotterSecondError_bound_eq_local L τ u t r]
  exact trotterSecond_matrix_error_le hL hsize τ u μ t ht r hr

/-- Physical-layout realization with the explicit local coefficient and original chemical shift. -/
@[expose] def trotterSecondLocalRealization {L : ℕ} [NeZero L]
    (hL : Even L) (hsize : 4 ≤ L) (τ u μ t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (Trotter.nativeLayout (2 * L ^ 2))
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (2 * L ^ 2)).symm
        (timeEvolution (hamiltonian L τ u μ) t))
      ((t ^ 3 / (r : ℝ) ^ 2) * localErrorCoefficient L τ u) :=
  Trotter.NativeCircuit.approximate (trotterSecond L τ u μ t r) _ _
    (trotterSecond_localError_le hL hsize τ u μ t ht r hr)

/-- Closed native counts on the physical even torus. Zero rotations retain their visits. -/
lemma trotterSecond_eventCost {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (r : ℕ) :
    (trotterSecond L τ u μ t r).eventCost = r • (
      (32 * L * (L - 1) * (L + 1) + 4 * L ^ 2) • {.gate .cnot} +
      (22 * L ^ 2) • {.gate .singleQubit} +
      (64 * L ^ 2) • {.gate .singleQubit} +
      (64 * L ^ 2) • {.gate .singleQubit} +
      (2 * L ^ 2) • {.gate .singleQubit}) := by
  rw [trotterSecond, Trotter.secondBlocks_eventCost]
  simp only [plaqCircuits_eventCost]
  rw [plaqGroups_passPool hL, pauliSum_passPool (by omega)]
  simp only [nativePassPool, nsmul_add, smul_smul]
  have hc : 2 * (16 * L * (L - 1) * (L + 1) + 2 * L ^ 2) =
      32 * L * (L - 1) * (L + 1) + 4 * L ^ 2 := by ring
  have hrz : 2 * (11 * L ^ 2) = 22 * L ^ 2 := by ring
  have hh : 2 * (32 * L ^ 2) = 64 * L ^ 2 := by ring
  rw [hc, hrz, hh]

/-- Exact CNOT count of the actual unmerged Hubbard word. -/
lemma trotterSecond_cnot_count {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (r : ℕ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (trotterSecond L τ u μ t r).eventCost =
      r * (32 * L * (L - 1) * (L + 1) + 4 * L ^ 2) := by
  rw [trotterSecond_eventCost hL hsize]
  simp [ResourcePool.count]

/-- Every retained local basis change, rotation and scalar phase is one single-qubit event. -/
lemma trotterSecond_singleQubit_count {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (r : ℕ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (trotterSecond L τ u μ t r).eventCost =
      r * (152 * L ^ 2) := by
  rw [trotterSecond_eventCost hL hsize]
  simp [ResourcePool.count]
  ring

/-- Independent quantum-time ceiling from the retained literal native visits. -/
lemma trotterSecond_depth_le {L : ℕ} [NeZero L] (hL : Even L) (hsize : 4 ≤ L)
    (τ u μ t : ℝ) (r : ℕ) :
    (trotterSecond L τ u μ t r).evaluatedEventDepth (fun _ => 1) ≤
      r * (32 * L * (L - 1) * (L + 1) + 156 * L ^ 2) := by
  have bound := DepthExpr.depthEval_le_costEval
    (fun _ : Resource.Event (.quantum AlgorithmGate.model .empty) => 1)
    (trotterSecond L τ u μ t r).eventDepth
  rw [DepthExpr.costEval_eq_weightedCount] at bound
  change (trotterSecond L τ u μ t r).evaluatedEventDepth (fun _ => 1) ≤
    ResourcePool.weightedCount (fun _ => 1)
      (trotterSecond L τ u μ t r).resourcesFromEventDepth at bound
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost,
    trotterSecond_eventCost hL hsize] at bound
  simp only [ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add] at bound
  simp only [ResourcePool.weightedCount, Multiset.map_singleton,
    Multiset.sum_singleton, mul_one] at bound
  convert bound using 1
  ring

end
end QuantumAlg.FermiHubbard

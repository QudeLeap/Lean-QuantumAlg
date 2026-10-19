/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Canonical
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Canonical
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution.Minimum

public import QuantumAlg.Algorithms.OrderFinding.Oracle.Canonical
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Projections
public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Counts
public import QuantumAlg.Util.Nat.ChooseTwo
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Specification
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint

/-! # Exact dyadic sampling at the minimum target width -/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint.Canonical

noncomputable section

/-- The complete canonical sample has the exact-grid success guarantee of one. -/
public lemma canonicalExactOrderFinding_problem_successLB
    (N x t : Nat) (environment : (Sampling.Native.model t (targetWidth N)).Environment)
    (witness : Witness N x t (targetWidth N)) :
    ((problem N x t).successLB environment witness).value = 1 := rfl

/-- Canonical target sizing preserves the full exact-grid execution contract. -/
public lemma canonicalExactOrderFinding_algorithm_solves (N x t : Nat) :
    Algorithm.Solves (algorithm N t) (problem N x t) :=
  complete_correct N x t

/-- The acceptance predicate retains the sampled index and the witness's true order. -/
public lemma canonicalExactOrderFinding_accepts_iff
    (N x t : Nat) (environment : (Sampling.Native.model t (targetWidth N)).Environment)
    (witness : Witness N x t (targetWidth N))
    (before : Execution.Store Sampling.Native.pre) (word : Fin (2 ^ t)) :
    (problem N x t).accepts environment witness before (.unsignedWord word) ↔
      ∃ sample : Fin witness.order,
        word.val = sample.val * (2 ^ t / witness.order) := by
  rfl

/-- The complete sample uses only the phase and minimum target registers. -/
public lemma canonicalExactOrderFinding_problem_qubits (N x t : Nat) :
    (problem N x t).resources.resident (.quantumSystems 2) = t + targetWidth N := by
  simpa [problem] using
    (exactOrderFinding_problem_quantum_systems N x t (targetWidth N) 2).1

/-- Standard gate and query counts belong to the same complete exact-grid execution. -/
public lemma canonicalExactOrderFinding_algorithm_nativeCounts (N t : Nat)
    (path : (algorithm N t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.model t (targetWidth N))
        (.oracle UnitarySource.Coordinate.ordinary)
        ((algorithm N t).run.code.resourcePool path) = 1 ∧
    ResourcePool.count (model := Sampling.Native.model t (targetWidth N)) (.gate .cnot)
        ((algorithm N t).run.code.resourcePool path) =
      t * (t - 1) + 3 * (t / 2) ∧
    ResourcePool.count (model := Sampling.Native.model t (targetWidth N)) (.gate .singleQubit)
        ((algorithm N t).run.code.resourcePool path) =
      t * (3 * t + 1) / 2 := by
  have counts := exactOrderFinding_algorithm_nativeCounts t (targetWidth N) path
  refine ⟨counts.2.2.2.1, ?_, ?_⟩
  · simpa only [algorithm, ChooseTwo.twice_choose_two] using counts.2.1
  · simpa only [algorithm, ChooseTwo.two_mul_add_three_mul_choose_two] using counts.1

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint.Canonical

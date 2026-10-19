/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution.Minimum
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

/-- **Input.** A nonnegative modular base, its least positive order, a modulus
at least two, and a positive phase width whose power of two is divisible by
the order. The target width is the ceiling of the modulus's binary logarithm.

**Output.** A retained index `j = s * (2 ^ t / r)` for an index `s < r`.

**Resource budget.** Independent native gate, quantum and classical storage,
and complete-execution depth budgets for the source sample and retained decoder.

**Success.** The output lies on the exact grid with probability one.

**Source.** [dW19, qcnotes.tex:2243-2251]. -/
@[expose] public def problem (N x t : Nat) :=
  NativeEndpoint.problem N x t (targetWidth N)

/-- Canonical target sizing preserves the full interpretation-quantified contract. -/
private lemma complete_correct (N x t : Nat) :
    Algorithm.Solves (algorithm N t) (problem N x t) :=
  NativeEndpoint.algorithm_solves N x t (targetWidth N)

/-- One canonical-width execution solves every admitted true order. -/
public theorem main (N x t : Nat) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate (problem N x t) :=
  ⟨algorithm N t, complete_correct N x t⟩

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint.Canonical

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Real.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Real.Execution

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Protocol
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Events
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete Shor factoring for arbitrary real failure targets

One actual machine supplies original factoring success, every full joint
output/reference fiber, borrowed restoration and all event, space and depth
obligations. Initialization and every reused round belong to the same code.
Unknown distinct primes are theorem-side data, never executable inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.RealTarget

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- Complete declared-query factoring at the original real failure target.

**Input.** The known product N of unknown distinct primes, a positive real
failure target eta, ordinary modular-exponentiation access, and any original
classical caller with an external reference. No prepared quantum bank or
factor witness is an executable input.
**Output.** An optional prime factor, all actual retained source results,
the predetermined zero bank in every output fiber, and restored borrowed
correlations with the caller and reference.
**Resource budget.** Write n=ceil(log2 N) and choose the direct logarithmic
count k from failure complement 1-1/(48n). The same run uses 3n qubits,
at most k queries, k(4n^2+n) CNOTs, k(6n^2+4n) single-qubit gates,
k(22n+1)+70n+42 classical bits and k(56n^2+222n+316)+2 classical operations.
Quantum time is bounded by the independent complete-run allowance
`Scalar.wholeRunDepth N k`; this allowance also counts classical operations,
preparation and readout.
**Success.** A declared prime factor is returned with probability at least
1-eta; eta=1 selects a genuine initialization-and-packing terminal run.
**Source.** [Sho95, source.tex:1124-1169,1183-1245];
[dW19, qcnotes.tex:2203-2225]. Native resource bounds are derived from the
actual execution rather than supplied as source-side cost premises.
-/
public def problem (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η) :
    Problem (ShorStyle.executionModel N) pre (post N η) (OutputShape N) :=
  Machine.RealTarget.problem pre pre_quantumWires N input η positive

/-- The ordinary named algorithm meets all seven obligations from every original caller. -/
private lemma complete_correct (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (positive : 0 < η) :
    (algorithm N input η).Solves (problem N input η positive) :=
  Machine.RealTarget.shorRealTarget_machine_solves pre pre_quantumWires N input η positive

/-- One complete execution solves the independent original real-target factoring problem. -/
public theorem main (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η) :
    ∃ candidate, Algorithm.Solves (allowAllocation := true) candidate
      (problem N input η positive) :=
  ⟨algorithm N input η, complete_correct N input η positive⟩

end

end QuantumAlg.Factoring.ShorStyle.RealTarget

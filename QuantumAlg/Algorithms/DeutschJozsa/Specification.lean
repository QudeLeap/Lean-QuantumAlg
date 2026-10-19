/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.DeutschJozsa.Construction
public import QuantumAlg.Primitives.WalshHadamard.Readout.Context
public import QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Algorithms.DeutschJozsa.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# The independent complete Deutsch-Jozsa problem

The oracle domain and constant-versus-balanced promise are unchanged
[dW19, qcnotes.tex:1179,1181,1182]. The result remains the entire measured
query-register bit string: zero denotes the constant case. The complete
context also retains the target system and all actual classical result cells.

The budgets below are explicit formulas in n. They are not projected from
the circuit, its interpreter, a mathematical outcome PMF, or a resource
witness supplied by the solver.
-/

namespace QuantumAlg.DeutschJozsa

open WalshHadamard.Readout

noncomputable section

/-- Explicit native counts, independent of the candidate circuit. -/
public def eventBudget (n : Nat) : ResourcePool (model n) :=
  (n + 1) • ResourcePool.singleton (model := model n)
      (.preparation (2 : ℕ+)) +
    ((2 * n + 2) • ResourcePool.singleton (model := model n)
      (.gate AlgorithmGate.Coordinate.singleQubit) +
      ResourcePool.singleton (model := model n)
      (.oracle XorOracle.Coordinate.xor)) +
    (n • ResourcePool.singleton (model := model n)
      (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model n)
      (.classicalOperation (Resource.ClassicalOpLabel.nominalEncoding (.packFiniteBits n))))

/-- All prepared systems and both actual classical result representations remain live. -/
public def spaceBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n + 1 else 0

/-- Preparation, the query circuit, n sequential measurements, and one actual packing step. -/
public def depthBudget (n : Nat) : Nat := 1 + (if n = 0 then 3 else 4) + n + 1

/-- The accepted actual bit string makes the original constant-versus-balanced decision. -/
public def accepts {n : Nat} (f : WalshHadamard.Oracle n)
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => CorrectDecision f outcome

end

end QuantumAlg.DeutschJozsa

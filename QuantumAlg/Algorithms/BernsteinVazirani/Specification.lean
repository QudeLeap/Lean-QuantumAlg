/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.BernsteinVazirani.Construction
public import QuantumAlg.Primitives.WalshHadamard.Readout.Context
public import QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Algorithms.BernsteinVazirani.Construction
import all QuantumAlg.Primitives.WalshHadamard.Readout.Geometry
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# The independent complete Bernstein-Vazirani problem

Every hidden n-bit string is admitted, with no Deutsch-Jozsa promise. The
accepted result is its exact big-endian encoding. The complete context retains
the prepared target and query systems and every actual classical result cell.
The following explicit resource limits do not depend on a supplied run,
interpreter, output distribution or accounting witness.
-/

namespace QuantumAlg.BernsteinVazirani

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

/-- The actual packed result must encode precisely the hidden string. -/
public def accepts {n : Nat} (hidden : Fin (2 ^ n))
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => outcome = measurementOutcome n hidden

end

end QuantumAlg.BernsteinVazirani

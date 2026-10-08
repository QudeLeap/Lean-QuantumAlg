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
def eventBudget {n : Nat} (f : WalshHadamard.Oracle n) : ResourcePool (model f) :=
  (n + 1) • ResourcePool.singleton (model := model f)
      (.preparation (2 : ℕ+)) +
    ((2 * n + 2) • ResourcePool.singleton (model := model f)
      (.gate AlgorithmGate.Coordinate.singleQubit) +
      ResourcePool.singleton (model := model f)
      (.oracle XorOracle.Coordinate.xor)) +
    (n • ResourcePool.singleton (model := model f)
      (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model f)
      (.classicalOperation (Resource.ClassicalOpLabel.nominalEncoding (.packFiniteBits n))))

/-- All prepared systems and both actual classical result representations remain live. -/
def spaceBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n + 1 else 0

/-- Preparation, the query circuit, n sequential measurements, and one actual packing step. -/
def depthBudget (n : Nat) : Nat := 1 + (if n = 0 then 3 else 4) + n + 1

/-- The accepted actual bit string makes the original constant-versus-balanced decision. -/
def accepts {n : Nat} (f : WalshHadamard.Oracle n)
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => CorrectDecision f outcome

/-- Independent complete Deutsch-Jozsa decision contract.

**Input.** For every natural width n, an oracle on all 2^n binary inputs,
promised constant or balanced. The runtime input is the original borrowed
unit cell, with no supplied quantum systems. Every normalized external
reference extension of this local input is admitted.
**Output.** The actual n-bit measured query result is zero exactly when the
oracle is constant. All n+1 prepared quantum systems, n finite binary result
cells, the final n-bit string, and the borrowed unit remain in complete Output.
The target quantum system is not measured or released. At n = 0 the result is
the unique empty bit string and there are zero measurement instructions.
**Resource budget.** Fixed zero preparation of all n+1 qubits, followed by
one target X and 2n+1 Hadamards, charged as 2n+2 native single-qubit gates.
One declared n-input XOR-oracle call, n binary Z measurements,
and one width-tagged finite-bit packing operation. Resident and auxiliary
space are at most n+1 dimension-two systems and 2n classical bits, with zero
systems of other dimensions. Unit-event depth is at most
1+(if n=0 then 3 else 4)+n+1; packing still executes at n=0.
**Success.** Probability one under the original promise, with mandatory joint
restoration of the borrowed input and arbitrary external reference.
**Source.** The promise, phase-query construction, signed amplitude and exact
decision in [dW19, qcnotes.tex:1179,1193,1245,1251,1253,1255]; the single XOR
query with its target factor in [CEMM98, cemm6.tex:326,342,379,403]. The native
execution additionally accounts for its actual preparation, measurement
storage and final classical packing instructions.
-/
public def problem {n : Nat} (f : WalshHadamard.Oracle n) :
    Problem (model f) pre (post n) (.bits n) where
  valid := fun _ => Promise f
  initialization := fun _ => True
  accepts := accepts f
  successLB := ⟨1, le_rfl⟩
  states := []
  resources := { events := eventBudget f, resident := spaceBudget n, auxiliary := spaceBudget n }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget n
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.DeutschJozsa

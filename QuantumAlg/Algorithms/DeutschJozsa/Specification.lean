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
import all QuantumAlg.Components.Oracle.Common

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

/-- The independent basis-preparation coordinate: n zeros followed by target one. -/
def preparationEvent (n : Nat) : Resource.Event .quantum :=
  .preparation
    { family := "builtin"
      name := "computational-basis"
      parameters := (n + 1) ::
        (List.replicate (n + 1) 2 ++ (List.replicate n 0 ++ [1])) }

/-- Explicit event multiplicities for preparation, the query circuit, measurement, and packing. -/
def eventBudget (n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (preparationEvent n) +
    ((2 * n + 1) • ResourcePool.singleton (.gate (.builtin "hadamard")) +
      ResourcePool.singleton (.quantumSubroutine (xorOracleSubroutineLabel n).quantum)) +
    (n • ResourcePool.singleton
      (.measurement { family := "builtin", name := "z", parameters := [2] }) +
      ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits n))))

/-- All prepared systems and both actual classical result representations remain live. -/
def spaceBudget (n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * n
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then n + 1 else 0

/-- Preparation, the query circuit, n sequential measurements, and one actual packing step. -/
def depthBudget (n : Nat) : Nat := 1 + (if n = 0 then 2 else 3) + n + 1

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
**Resource budget.** One preparation of n zero query qubits and target one,
2n+1 Hadamards, one declared n-input XOR-oracle call, n binary Z measurements,
and one width-tagged finite-bit packing operation. Resident and auxiliary
space are at most n+1 dimension-two systems and 2n classical bits, with zero
systems of other dimensions. Unit-event depth is at most
1+(if n=0 then 2 else 3)+n+1; packing still executes at n=0.
**Success.** Probability one under the original promise, with mandatory joint
restoration of the borrowed input and arbitrary external reference.
**Source.** The promise, phase-query construction, signed amplitude and exact
decision in [dW19, qcnotes.tex:1179,1193,1245,1251,1253,1255]; the single XOR
query with its target factor in [CEMM98, cemm6.tex:326,342,379,403]. The native
execution additionally accounts for its actual preparation, measurement
storage and final classical packing instructions.
-/
public def problem {n : Nat} (f : WalshHadamard.Oracle n) :
    Problem .quantum pre (post n) (.bits n) where
  valid := fun _ => Promise f
  accepts := accepts f
  successLB := ⟨1, le_rfl⟩
  states := []
  resources := { events := eventBudget n, resident := spaceBudget n, auxiliary := spaceBudget n }
  depth := .quantum (fun _ => 1) (depthBudget n)

end

end QuantumAlg.DeutschJozsa

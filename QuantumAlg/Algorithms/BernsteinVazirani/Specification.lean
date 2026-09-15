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
import all QuantumAlg.Components.Oracle.Common

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

/-- The actual packed result must encode precisely the hidden string. -/
def accepts {n : Nat} (hidden : Fin (2 ^ n))
    (_initial : Execution.Store pre) (result : CShape.Value (.bits n)) : Prop :=
  match result with
  | .bits outcome => outcome = measurementOutcome n hidden

/-- Independent complete Bernstein-Vazirani recovery contract.

**Input.** Every natural width n and every hidden string s in Fin (2^n), with
quantum access to its mod-two inner-product XOR oracle. There is no additional
promise. The input context is one borrowed unit cell and no quantum systems;
every normalized external-reference extension is admitted. Query and target
systems are prepared by the code itself.
**Output.** The actual n-bit result is the big-endian encoding
`fun index => s.val.testBit (n-1-index.val)`, with probability one. Complete
Output retains the borrowed unit, n+1 prepared quantum systems, n finite
binary measurement cells and the final n-bit string. The target remains
unmeasured. At n=0 the result is the unique empty bit string.
**Resource budget.** One computational-basis preparation of n zero query
qubits and target one, 2n+1 Hadamards, one n-input XOR-oracle call, n binary
Z measurements, and one width-tagged finite-bit packing operation. Both
resident and auxiliary space are at most n+1 dimension-two systems and 2n
classical bits, with no systems at other dimensions. Unit-event depth is at
most `1+(if n=0 then 2 else 3)+n+1`. At n=0 no measurement is performed and
packing still emits one actual event.
**Success.** Exact recovery with probability one, together with mandatory
joint restoration of the borrowed classical input and external reference.
**Source.** The hidden inner-product problem and exact one-query recovery in
[dW19, qcnotes.tex:1282,1283,1288,1293,1294,1296,1297]. The source explicitly
uses the same query circuit as Deutsch-Jozsa. Native preparation, individual
measurement writes and classical packing are additionally accounted for.
-/
public def problem {n : Nat} (hidden : Fin (2 ^ n)) :
    Problem .quantum pre (post n) (.bits n) where
  valid := fun _ => True
  accepts := accepts hidden
  successLB := ⟨1, le_rfl⟩
  states := []
  resources := { events := eventBudget n, resident := spaceBudget n, auxiliary := spaceBudget n }
  depth := .quantum (fun _ => 1) (depthBudget n)

end

end QuantumAlg.BernsteinVazirani

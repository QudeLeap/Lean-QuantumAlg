/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Algorithms.OrderFinding.Exact.Context
public import QuantumAlg.Util.Order.Finding
import all QuantumAlg.Algorithms.OrderFinding.Exact.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.Exact.Budget
import all QuantumAlg.Algorithms.OrderFinding.Exact.Context

/-!
# Independent exact-dyadic order-finding specification

The original positive-width number-theoretic domain and exact-grid success
predicate are unchanged. The empty runtime input admits every normalized
external reference. Bounds include actual preparation, all stored readouts,
packing, and the real decoder; every resulting resource remains in Output.
-/

namespace QuantumAlg.OrderFinding

noncomputable section

/-- Complete exact-dyadic order sampling with an actually materialized unsigned result.

**Input.**
- Natural $N,x,r$ with $N\ge2$, $x$ coprime to $N$, and $r$ the least positive
  exponent satisfying $x^r\equiv1\pmod N$. The original phase width $t$ is
  positive and $r\mid2^t$.
- The original modular-exponentiation XOR oracle acts on a $t$-qubit phase
  and $n$-qubit target register. Runtime input is empty; every normalized
  external-reference extension is admitted. Both registers are prepared internally.
**Output.**
- A retained unsigned $t$-bit word $j=s(2^t/r)$ for some $s\in\{0,\ldots,r-1\}$.
  This is an exact Fourier sample. Recovery of $r=2^t/\gcd(j,2^t)$ additionally
  requires $s$ coprime to $r$, as in the unchanged dyadic recovery theorem.
- Complete Output retains all $t+n$ quantum systems, $t$ binary measurement
  cells, the packed $t$-bit sample, and the decoded $t$-bit word.
**Resource budget.**
- One all-zero basis preparation, $t$ preparation Hadamards, one modular-exponentiation
  query, and inverse-QFT readout with $t$ Hadamards, $t(t-1)/2$ controlled phases
  and $\lfloor t/2\rfloor$ SWAPs.
- There are $t$ actual binary Z measurements, one finite-bit packing instruction,
  $t$ word shifts and at most $t$ value-selected increments.
- Both resident and auxiliary space are bounded by $t+n$ dimension-two systems
  and $3t$ classical bits, with zero systems at other dimensions.
- On the valid positive-width domain, unit-event depth is at most
  $4+4t+t(t-1)/2+\lfloor t/2\rfloor$.
**Success.**
- Exact-grid output with probability one on the original valid domain, with
  mandatory joint restoration of the full external reference.
**Source.**
- The original periodic sampling circuit and exact dyadic support
  [dW19, qcnotes.tex:2203-2258]; coprime-numerator recovery is explained at
  [dW19, qcnotes.tex:2259-2267]. Native stored readouts and their actual
  fixed-width decoder are additionally accounted for.
-/
public def problem {N x t n : Nat} (_A : ModExpOracleAccess N x t n) (r : Nat) :
    Problem .quantum Sampling.pre (Exact.post t n) (.unsignedWord t) where
  valid := fun _ => 0 < t ∧ OrderFinding.Input N x r ∧ r ∣ 2 ^ t
  accepts := fun _ output => SuccessfulOutcome r output
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := Exact.eventBudget N x t n
      resident := Exact.spaceBudget t n
      auxiliary := Exact.spaceBudget t n }
  depth := .quantum (fun _ => 1) (Exact.depthBudget t)

end

end QuantumAlg.OrderFinding

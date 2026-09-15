/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Util.NumberTheory.Factoring
public import Mathlib.Data.Nat.Prime.Defs
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.State
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Probability
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent complete native Shor factoring contract

The original semiprime and rational failure domains determine the same source
retry count. The actual circuit supplies its own samples and quantum bank.
Native resources include the complete arithmetic recovery tail, and every
output observes the restored bank jointly with the original reference.
-/

namespace QuantumAlg.Factoring.ShorStyle

noncomputable section

/-- The original borrowed unit anchor, containing no base, factor or quantum input. -/
@[reducible] public def pre : RuntimeCtx .quantum := Canonical.NativeEndpoint.pre

/-- The original optional modulus-width factor word. -/
@[reducible] public def OutputShape (N : Nat) : CShape := Canonical.NativeEndpoint.outputShape N

/-- Complete output retains the single quantum bank, every sample and the final factor cell. -/
@[reducible] public def post {N : Nat} (_model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) : RuntimeCtx .quantum :=
  Canonical.NativeEndpoint.post N (Canonical.retryCount N budget)

/-- The sole actual input store contains its original zero-width unit anchor. -/
public def inputStore : Execution.Store pre := ⟨(.unit, ())⟩

/-- The semiprime proof does not supply a factor to the executable store. -/
public def semiprimeModelOfDistinctPrimes {N p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hN : N = p * q) : NumberTheory.Factoring.SemiprimeFactorModel N := by
  subst N
  exact NumberTheory.Factoring.SemiprimeFactorModel.ofDistinctPrimes hp hq hpq

private def successBound (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ProbabilityLowerBound where
  value := FailureBudget.successThreshold budget
  le_one := by
    unfold FailureBudget.successThreshold
    apply ENNReal.ofReal_le_one.mpr
    have nonnegative := FailureBudget.value_nonneg budget wellFormed
    linarith

/-- Closed Shor factoring with actual sampling, modular arithmetic and factor recovery.

**Input.**
- Distinct unknown primes $p,q$, their known product $N=pq$, and an encoded
  rational failure target $0<\eta\le1$. The executable store is the original
  unit anchor; arbitrary normalized external references are admitted.
- The same source widths are $m=\lceil\log_2N\rceil$ and $t=2m$. The retry
  count is the original $k=\max\{1,\lceil\log(1/\eta)/
  \log(48m/(48m-1))\rceil\}$.
**Output.**
- An optional modulus-width factor word, accepted when it names $p$ or $q$.
- Complete Output retains the one quantum bank, every sampled parameter,
  actual measurement bit, packed phase word and final result cell.
**Resource budget.**
- The bank is prepared once and uses $4m$ qubits. Every original source
  round uses actual compiled modular powers, Hadamards, inverse QFT, Z
  measurement, packing and complete bank reset and reload.
- Resident and auxiliary classical storage are bounded by
  $k(22m+1)+39m+26$ bits, including the full live recovery scratch.
- The native event ledger and unit-depth bound include every real sampler,
  order recovery, modular half-power, GCD, guard, first-success selection and
  packaging instruction. Their independent formulas are indexed by $N,k$.
**Success.**
- A declared prime factor is returned with probability at least $1-\eta$.
  Each output block restores the bank seed jointly with the incoming
  reference; borrowed resources must separately retain all joint correlations.
**Source.**
- The original sampling and recovery analysis [Sho95, source.tex:1124-1169,1183-1245].
- The actual modular arithmetic uses the Gidney construction
  [G17, paper.tex:276-293,319-334,380-389] and its native adder components
  [TTK09, qic-loglogaddition-quant.tex:285-318,330-352]. The complete event,
  depth and storage bounds are proved for their project composition.
-/
public def problem {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Problem .quantum pre (post model budget) (OutputShape N) where
  valid := fun state => ∀ store, 0 < (state.block store).mass → store = inputStore
  accepts := fun _ output => Canonical.Probability.ReturnedDeclaredFactor model output
  successLB := successBound budget wellFormed
  states := [Canonical.NativeEndpoint.stateRequirement N (Canonical.retryCount N budget)]
  resources :=
    { events := Canonical.NativeEndpoint.eventBudget N (Canonical.retryCount N budget)
      resident := Canonical.NativeEndpoint.spaceBudget N (Canonical.retryCount N budget)
      auxiliary := Canonical.NativeEndpoint.spaceBudget N (Canonical.retryCount N budget) }
  depth := .quantum (fun _ => 1)
    (Canonical.NativeEndpoint.depthBudget N (Canonical.retryCount N budget))

/-- Exact resident classical coordinate of the independently specified complete native budget. -/
public def residentClassicalBitLimit (N : Nat) (budget : FailureBudget) : Nat :=
  Canonical.retryCount N budget * (22 * Canonical.modulusBits N + 1) +
    39 * Canonical.modulusBits N + 26

/-- The borrowed input has zero width, so the auxiliary classical allowance is identical. -/
public def auxiliaryClassicalBitLimit (N : Nat) (budget : FailureBudget) : Nat :=
  Canonical.retryCount N budget * (22 * Canonical.modulusBits N + 1) +
    39 * Canonical.modulusBits N + 26

/-- Lossless IEC display of the actual native resident classical budget. -/
public def residentClassicalMemoryIEC (unit : IECUnit) (N : Nat)
    (budget : FailureBudget) : Nat × Nat :=
  unit.decomposeBits (residentClassicalBitLimit N budget)

end

end QuantumAlg.Factoring.ShorStyle

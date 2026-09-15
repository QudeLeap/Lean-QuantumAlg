/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.OrderFinding.General.Input
public import QuantumAlg.Util.Order.Finding
import all QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.General.Resources
import all QuantumAlg.Algorithms.OrderFinding.General.Space
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# Independent native general order-finding specification

The original canonical borrowed base, Fourier register window and success
criterion are retained. The budget includes the actual source measurement,
classical decoding, finite continued-fraction scan and modular validation.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

/-- Complete original input, sampled systems and retained optional recovery result. -/
public def post (t width : Nat) : RuntimeCtx .quantum := NativeEndpoint.post t width

/-- The source output is successful exactly when its stored optional word is the true order. -/
def SuccessfulOutcome (r : Nat) {t : Nat}
    (output : CShape.Value (.option (.unsignedWord (t + 1)))) : Prop :=
  output = .optionSome (.unsignedWord
    (ClassicalAlgorithms.OrderRecovery.candidateWord t r))

/-- The original source lower bound lies in the closed unit interval. -/
def successLB (r : Nat) : ProbabilityLowerBound where
  value := ENNReal.ofReal (orderFindingOutputSuccessLowerBound r)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    cases r with
    | zero => simp [orderFindingOutputSuccessLowerBound]
    | succ r =>
        have totientLe : (Nat.totient (r + 1) : Real) ≤ r + 1 := by
          exact_mod_cast Nat.totient_le (r + 1)
        have denominatorPositive : (0 : Real) < 3 * ((r + 1 : Nat) : Real) := by positivity
        have rNonnegative : (0 : Real) ≤ r := by positivity
        unfold orderFindingOutputSuccessLowerBound
        apply (div_le_one denominatorPositive).2
        norm_num [Nat.cast_add, Nat.cast_one] at totientLe ⊢
        nlinarith

/-- General non-dyadic order finding with actual stored-bit continued-fraction recovery.

**Input.**
- The original $N\ge2$, a base coprime to $N$, and its least positive order $r$.
  The phase width satisfies $0<t$ and $N^2\le2^t<2N^2$.
- The caller's canonical-residue cell contains the original reduced base.
  The original modular-exponentiation XOR oracle has a $t$-qubit phase register
  and a $w$-qubit target register, both prepared internally. Arbitrary normalized
  external references are admitted.
**Output.**
- An optional $(t+1)$-bit order candidate, accepted exactly when it equals $r$.
- Complete Output retains the borrowed base, every quantum system, individual
  measurement cells, packed phase bits and the final optional word.
**Resource budget.**
- The original one-query sampling budget, with its Hadamards, inverse QFT,
  actual Z writes and packing, followed by the fixed native recovery allowance.
- Recovery decodes and initializes real fields, visits at most $2(t+1)$ candidates,
  performs native modular validation, and packs the resulting option.
- Recovery adds no quantum systems. Its extra classical scratch is
  $9(t+1)+2w+4+\max\{t+1,8w+2\}$ bits beyond its actual entry context.
  The retained result adds $t+2$ bits; sampling retains both $t$-bit representations.
- Unit depth is the original source depth plus
  $4(t+1)+4+2(t+1)(2w+16+6(t+1))$.
**Success.**
- The true order is returned with probability at least $\varphi(r)/(3r)$.
  Borrowed resources and their full external-reference correlations must be restored.
**Source.**
- The original order-recovery register window and success analysis
  [Sho95, source.tex:1614-1663]. Native execution and storage costs are proved separately.
-/
public def problem {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    Problem .quantum (pre width) (post t width) (.option (.unsignedWord (t + 1))) where
  valid := fun state => HasCanonicalBase hinput A state ∧
    0 < t ∧ N ^ 2 ≤ 2 ^ t ∧ 2 ^ t < 2 * N ^ 2
  accepts := fun _ output => SuccessfulOutcome r output
  successLB := successLB r
  states := []
  resources :=
    { events := NativeEndpoint.eventBudget N x t width
      resident := NativeEndpoint.spaceBudget t width + (pre width).residentSpace
      auxiliary := NativeEndpoint.spaceBudget t width + (pre width).auxiliarySpace }
  depth := .quantum (fun _ => 1) (NativeEndpoint.depthBudget t width)

end

end QuantumAlg.OrderFinding.ShorSourceJoint

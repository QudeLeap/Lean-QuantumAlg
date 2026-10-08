/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native.Run
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion

/-!
# Actual elliptic-curve recovery at subgroup order one

The public order-one case uses the original actual zero-recovery circuit and
retains its optional candidate. Its input context is the same original
exponent endpoint context. The unique secret is zero, so the actual output
recovers it with probability one for every certified input and external
reference, without requiring a nonidentity accumulator offset.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

open Execution FiniteCyclicDLP
open Canonical.Probability
open ScalarMultiplication.MeasuredPlacement.Allocation

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Same original input context with the actual retained order-one optional candidate. -/
def trivialRecoveryContext (p width : Nat) : RuntimeCtx .quantum :=
  let ctx := before p (2 * width)
  ctx.addRetained ctx.canonicalFreshKey (.option (.unsignedWord width))
    ctx.canonicalFreshKey_fresh

/-- The original deterministic order-one circuit acts on the original endpoint input context. -/
def trivialRecoveryRun (problem : KnownOrderProblem E.GroupPoint) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (before p.size (2 * orderWidth problem))
      (trivialRecoveryContext p.size (orderWidth problem))
      (.option (.unsignedWord (orderWidth problem))) :=
  ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroRun
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (before p.size (2 * orderWidth problem)) (orderWidth problem)
    (before p.size (2 * orderWidth problem)).canonicalFreshKey
    (before p.size (2 * orderWidth problem)).canonicalFreshKey_fresh

/-- The actual order-one endpoint certainly returns the unique original secret. -/
theorem trivialRecoveryRun_probability_one (problem : KnownOrderProblem E.GroupPoint)
    (orderOne : problem.order = 1) (input : SecretInput problem) {Reference : Register}
    (initial : OracleInput ClassicalOracleModel.empty
      (before p.size (2 * orderWidth problem)) Reference) :
    (trivialRecoveryRun problem).outputDistribution initial
      (.optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)) = 1 := by
  have secretZero : input.secret.val = 0 := by
    have bounded : input.secret.val < problem.order :=
      (residueIndex problem input.secret).isLt
    omega
  rw [secretZero]
  exact ClassicalRoutines.FiniteCyclicDLP.Trivial.Native.zeroRun_output_probability
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    _ _ _ _ initial

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Depth

/-!
# Seven actual complete native factoring cycles at RSA-2048 widths

The finite-cycle certificate specializes the original seven-batch execution,
with one completed sixteen-round trial and full classical recovery per cycle.
Its actual reused bank is physically measured and returned to the same fixed
seed between completed trials. The real chronological selector remains part
of the complete execution and its unchanged whole-run resource accounting.

The decimal cycle ceiling is derived from independent complete-batch formulas.
It bounds the maximum of the first and reused batch allowances; it neither
counts the seven batches serially nor claims a per-round optimized depth.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- Independent unit-event ceiling for the maximum complete sixteen-round factoring cycle. -/
def maximumCycleDepthBound : Nat := 2_399_834_962_524_657_350

attribute [local irreducible] RSA.ShortLogWidths.coordinateWidth
attribute [local irreducible] NativeFiniteRetry.roundDepthWidthBound
  NativeFiniteRetry.recoveryDepthWidthBound

/-- The cycle decimal is the exact evaluation of the independent complete-batch scalar ceiling. -/
theorem model_batchDepthScalarBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeCycles.Finite.batchDepthScalarBound N = maximumCycleDepthBound := by
  unfold NativeCycles.Finite.batchDepthScalarBound
  rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
    model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  change 44 * 2_048 + 163 +
    16 * NativeFiniteRetry.roundDepthWidthBound 1_025 513 2_048 +
      NativeFiniteRetry.recoveryDepthWidthBound 2_048 1_025 513 7_522_484_226 = _
  rw [roundDepthWidthBound_eq, recoveryDepthWidthBound_eq]
  norm_num [roundDepthBound, recoveryDepthBound, maximumCycleDepthBound]

/-- The maximum first/reused complete-batch budget obeys the fixed RSA ceiling. -/
theorem model_batchDepthBound_le {N : Nat} (model : FixedWidthModel N) :
    NativeCycles.Finite.batchDepthBound N ≤ maximumCycleDepthBound :=
  (NativeCycles.Finite.batchDepthBound_le_scalar N).trans_eq
    (model_batchDepthScalarBound_eq model)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The seven completed scientific trials and actual selector are fixed
independently of execution. -/
def cyclePlan (model : FixedKeyModel N) :
    CyclePlan RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeCycles.Finite.plan base noQuantum model.1 rounds

/-- The original finite scientific outcome together with its seven complete-batch caller plan. -/
def cycleProblem (model : FixedKeyModel N) :
    CycleProblem RuntimeRound.model base (NativeFiniteRetry.context base noQuantum N rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeCycles.Finite.problem base noQuantum model.1 rounds

-- Keep the already certified seven-batch path carrier abstract in this specialization.
attribute [local irreducible] NativeFiniteRetry.algorithm NativeFiniteRetry.run
  NativeFiniteRetry.code NativeFiniteRetry.context

/-- The same actual seven-batch algorithm meets its original outcome and complete-cycle plan. -/
def cycleCertificate (model : FixedKeyModel N) :
    Algorithm.CycleSolves (NativeFiniteRetry.algorithm base noQuantum model.1.input rounds)
      (cycleProblem base noQuantum model) :=
  NativeCycles.Finite.certificate base noQuantum model.1 rounds

/-- Every actual RSA-2048 path has maximum complete-cycle depth below the independent ceiling. -/
theorem cycle_maximumDepth_le (model : FixedKeyModel N)
    (path : (NativeFiniteRetry.algorithm base noQuantum model.1.input rounds).run.code.Path) :
    (cycleCertificate base noQuantum model).maximumCycleDepth (fun _ => 1) path ≤
      maximumCycleDepthBound := by
  exact (NativeCycles.Finite.maximumCycleDepth_le base noQuantum model.1 rounds path).trans
    (model_batchDepthBound_le model.widthModel)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

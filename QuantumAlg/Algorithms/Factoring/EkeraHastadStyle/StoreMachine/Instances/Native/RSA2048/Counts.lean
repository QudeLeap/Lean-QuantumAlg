/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Counts

/-!
# Independent native count ceilings for seven RSA-2048 batches

These decimal ceilings are kernel-normalized evaluations of the current
native width formulas. The complete event allowance and its classical-only
observation remain distinct. Both apply to each path of the same actual
seven-batch run, including all 112 measured members and complete recovery.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Cardinality ceiling for the compiled member's independent native-coordinate pool. -/
def memberEventCountBound : Nat := 12_998_238_507_871_758

/-- Complete round ceiling includes terminal readout, packing, bank correction and seed reload. -/
def roundEventCountBound : Nat := 12_998_238_507_892_251

/-- Complete classical-recovery native-coordinate ceiling, including all candidate slots. -/
def recoveryEventCountBound : Nat := 2_191_863_151_158_329_395

/-- Full seven-batch native-event ceiling, including actual preparation and selection. -/
def eventCountBound : Nat := 16_798_844_770_992_869_825

/-- Full seven-batch ceiling for literal classical-operation coordinates. -/
def classicalOperationBound : Nat := 15_343_042_058_108_937_824

/-- The compiled-member number follows from the independent native-coordinate width formula. -/
lemma memberEventCountWidthBound_eq :
    polynomialPrimitiveWidthBound 1_025 513 2_048 = memberEventCountBound := by
  norm_num [polynomialPrimitiveWidthBound, groupActionPrimitiveWidthBound,
    exponentiationPrimitiveWidthBound, MAU.Exponentiation.Gidney.eventBound,
    MAU.Exponentiation.Gidney.stageEventBound, MAU.Multiplication.Gidney.eventBound,
    MAU.Multiplication.Accumulate.Gidney.stageEventBound,
    MAU.Addition.Gidney.modularOffsetEventBound, MAU.Addition.Gidney.pivotEventBound,
    MAU.Addition.Gidney.biFlipEventBound, MAU.Addition.Gidney.comparisonEventBound,
    MAU.Addition.Gidney.constantOffsetEventBound, qftPrimitiveBound, Nat.choose_two_right,
    memberEventCountBound]

/-- The complete-round decimal is obtained from its independent scalar formula. -/
lemma roundEventCountWidthBound_eq :
    RuntimeRound.eventCountWidthBound 1_025 513 2_048 = roundEventCountBound := by
  rw [RuntimeRound.eventCountWidthBound, memberEventCountWidthBound_eq, totalQubits_eq]
  norm_num [memberEventCountBound, roundEventCountBound, RuntimeRound.resultBits,
    ShortDLP.CompiledMAU.registerParameters, ShortDLP.firstBits]

/-- The complete-recovery decimal evaluates scalar widths and the original finite scan count. -/
lemma recoveryEventCountWidthBound_eq :
    LatticeFixedBatchRecoveryMachine.eventCountBound 2_048 1_025 513 7_522_484_226 =
      recoveryEventCountBound := by
  norm_num [LatticeFixedBatchRecoveryMachine.eventCountBound,
    LatticeFixedBatchRecoveryMachine.nearestPlaneEnvelopeBound, RSA.shortLogRecoveryFuel,
    LatticeRecoveryResources.modularSetupCardBound, LatticeRecoveryResources.candidateScanCardBound,
    LatticeRecoveryResources.candidateScanWork, LatticeRecoveryResources.candidateSlotCardBound,
    LatticeRecoveryResources.quadraticGuardedCardBound, LatticeRecoveryResources.natSqrtCardBound,
    QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
    recoveryEventCountBound]

-- Substitute the proved scalar coordinate width before considering the complete formulas.
attribute [local irreducible] RSA.ShortLogWidths.coordinateWidth
attribute [local irreducible] RuntimeRound.eventCountWidthBound
  LatticeFixedBatchRecoveryMachine.eventCountBound

/-- Every original fixed key has the stated independent full-run native-event ceiling. -/
lemma model_scalarEventCountBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.scalarEventCountBound N rounds = eventCountBound := by
  change 7 * (44 * Canonical.modulusBits N + 166 +
    16 * RuntimeRound.eventCountWidthBound (shortLogBits N) (tradeoffBits N)
      (arithmeticBits N) + LatticeFixedBatchRecoveryMachine.eventCountBound
        (Canonical.modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 2 = _
  rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
    model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  change 7 * (44 * 2_048 + 166 + 16 * RuntimeRound.eventCountWidthBound 1_025 513 2_048 +
    LatticeFixedBatchRecoveryMachine.eventCountBound 2_048 1_025 513 7_522_484_226) + 2 = _
  rw [roundEventCountWidthBound_eq, recoveryEventCountWidthBound_eq]
  norm_num [roundEventCountBound, recoveryEventCountBound, eventCountBound]

/-- The same fixed key has the stated independent classical-only ceiling. -/
lemma model_scalarClassicalOperationBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.scalarClassicalOperationBound N rounds = classicalOperationBound := by
  change 7 * (44 * Canonical.modulusBits N + 182 +
    LatticeFixedBatchRecoveryMachine.eventCountBound
      (Canonical.modulusBits N) (shortLogBits N) (tradeoffBits N)
        (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1 = _
  rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
    model_shortLogBits_eq model, model_tradeoffBits_eq model]
  change 7 * (44 * 2_048 + 182 +
    LatticeFixedBatchRecoveryMachine.eventCountBound 2_048 1_025 513 7_522_484_226) + 1 = _
  rw [recoveryEventCountWidthBound_eq]
  norm_num [recoveryEventCountBound, classicalOperationBound]

-- Reuse same-path bounds without unfolding the dependent seven-batch execution tree.
attribute [local irreducible] NativeFiniteRetry.run NativeFiniteRetry.code NativeFiniteRetry.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every seven-batch path obeys the native-event ceiling with its literal control labels. -/
lemma run_eventCount_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    ((NativeFiniteRetry.run base noQuantum input rounds).code.eventTrace path).length ≤
      eventCountBound :=
  (NativeFiniteRetry.run_eventCount_le_widthBound base noQuantum input rounds path).trans_eq
    (model_scalarEventCountBound_eq model)

/-- Every literal classical operation on the same complete run path obeys its own fixed ceiling. -/
lemma run_classicalOperation_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((NativeFiniteRetry.run base noQuantum input rounds).code.resourcePool path) ≤
      classicalOperationBound :=
  (NativeFiniteRetry.run_classicalOperation_le_widthBound
    base noQuantum input rounds path).trans_eq (model_scalarClassicalOperationBound_eq model)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

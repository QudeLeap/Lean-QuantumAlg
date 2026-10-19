/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Depth

/-!
# Independent serial depth bounds for seven actual RSA-2048 batches

The circuit-only member, complete measured round, complete classical batch
recovery and full seven-batch run have distinct scalar ceilings. The final
bound charges all 112 measured members and all classical dependencies, and
applies to each path of the same actual finite run.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent unit-duration ceiling for one selected compiled circuit alone. -/
def memberCircuitDepthBound : Nat := 12_998_238_507_211_787

/-- Complete measured-round ceiling includes measurements, packing, bank correction and reload. -/
def roundDepthBound : Nat := 12_998_238_507_232_280

/-- Complete classical batch ceiling includes initialization, all 120 pairs and output packing. -/
def recoveryDepthBound : Nat := 2_191_863_146_408_850_595

/-- Full serial ceiling for seven sampled and recovered batches followed by actual selection. -/
def unitDepthBound : Nat := 16_798_844_737_672_601_459

/-- The circuit-only scalar is proved from the independent MAU width envelope. -/
lemma memberCircuitDepthWidthBound_eq :
    compiledCircuitEventUnitDepthWidthBound 1_025 513 2_048 = memberCircuitDepthBound := by
  norm_num [compiledCircuitEventUnitDepthWidthBound, groupActionPrimitiveWidthBound,
    exponentiationPrimitiveWidthBound, MAU.Exponentiation.Gidney.eventBound,
    MAU.Exponentiation.Gidney.stageEventBound, MAU.Multiplication.Gidney.eventBound,
    MAU.Multiplication.Accumulate.Gidney.stageEventBound,
    MAU.Addition.Gidney.modularOffsetEventBound, MAU.Addition.Gidney.pivotEventBound,
    MAU.Addition.Gidney.biFlipEventBound, MAU.Addition.Gidney.comparisonEventBound,
    MAU.Addition.Gidney.constantOffsetEventBound, qftPrimitiveBound, Nat.choose_two_right,
    memberCircuitDepthBound]

/-- The complete measured-round number is obtained from its independent scalar formula. -/
lemma roundDepthWidthBound_eq :
    NativeFiniteRetry.roundDepthWidthBound 1_025 513 2_048 = roundDepthBound := by
  rw [NativeFiniteRetry.roundDepthWidthBound, memberCircuitDepthWidthBound_eq]
  norm_num [memberCircuitDepthBound, roundDepthBound]

/-- The classical number evaluates only scalar widths and finite scan cardinalities. -/
lemma recoveryDepthWidthBound_eq :
    NativeFiniteRetry.recoveryDepthWidthBound 2_048 1_025 513 7_522_484_226 =
      recoveryDepthBound := by
  norm_num [NativeFiniteRetry.recoveryDepthWidthBound, recoveryDepthBound]

-- Substitute the proved scalar coordinate width before considering the complete formula.
attribute [local irreducible] RSA.ShortLogWidths.coordinateWidth
attribute [local irreducible] NativeFiniteRetry.roundDepthWidthBound
  NativeFiniteRetry.recoveryDepthWidthBound

/-- Every original fixed key has the stated complete independent seven-batch scalar allowance. -/
lemma model_scalarDepthBound_eq {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.scalarDepthBound N rounds = unitDepthBound := by
  change 7 * (44 * Canonical.modulusBits N + 164 +
    16 * NativeFiniteRetry.roundDepthWidthBound (shortLogBits N) (tradeoffBits N)
      (arithmeticBits N) + NativeFiniteRetry.recoveryDepthWidthBound
        (Canonical.modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 2 = _
  rw [model_coordinateWidth_eq model, model_modulusBits_eq model,
    model_shortLogBits_eq model, model_tradeoffBits_eq model, model_arithmeticBits_eq model]
  change 7 * (44 * 2_048 + 164 +
    16 * NativeFiniteRetry.roundDepthWidthBound 1_025 513 2_048 +
      NativeFiniteRetry.recoveryDepthWidthBound 2_048 1_025 513 7_522_484_226) + 2 = _
  rw [roundDepthWidthBound_eq, recoveryDepthWidthBound_eq]
  norm_num [roundDepthBound, recoveryDepthBound, unitDepthBound]

/-- The original native dependency envelope is below the independently proved fixed number. -/
lemma model_depthBound_le {N : Nat} (model : FixedWidthModel N) :
    NativeFiniteRetry.depthBound N rounds ≤ unitDepthBound :=
  (NativeFiniteRetry.depthBound_le_scalarDepthBound N rounds).trans_eq
    (model_scalarDepthBound_eq model)

-- Reuse same-path bounds without unfolding the seven-batch dependent execution tree.
attribute [local irreducible] NativeFiniteRetry.run NativeFiniteRetry.code NativeFiniteRetry.context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every path of the actual seven-batch code obeys the full serial bound. -/
lemma code_unitDepth_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.code base noQuantum input rounds).Path) :
    (NativeFiniteRetry.code base noQuantum input rounds).depth (fun _ => 1) path ≤
      unitDepthBound :=
  (NativeFiniteRetry.code_depth_le_scalar base noQuantum input rounds path).trans_eq
    (model_scalarDepthBound_eq model)

/-- Every complete actual run path includes all quantum and classical serial dependencies. -/
lemma run_unitDepth_le (model : FixedWidthModel N) (input : Canonical.Input N)
    (path : (NativeFiniteRetry.run base noQuantum input rounds).code.Path) :
    (NativeFiniteRetry.run base noQuantum input rounds).code.depth (fun _ => 1) path ≤
      unitDepthBound :=
  (NativeFiniteRetry.run_depth_le_scalar base noQuantum input rounds path).trans_eq
    (model_scalarDepthBound_eq model)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRSA2048

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Events
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Cardinality
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources

/-!
# Kernel-normalized native arithmetic allowances at the original P-256 width

Only scalar resource formulas are evaluated. No circuit, selector list,
input state or execution tree is expanded. The original shared EEA uses a
finite-selector construction, whose deliberately conservative allowance is
retained. These numbers describe that implementation's certified budgets,
not a claimed paper leading constant or an attained worst-case path.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured

noncomputable section

open MAU.Inversion.SharedEEA MAU.Multiplication
open PrimeFieldShortWeierstrass ECDLP.Measured

/-- The original complete in-place EEA allowance evaluates its width-only formula. -/
theorem p256_inPlaceForwardBound_eq :
    ForwardResources.inPlaceBound 256 = 27087960089229645585 := by
  have widthSize : Nat.size 256 = 9 := by decide
  norm_num [widthSize, ForwardResources.inPlaceBound, ForwardResources.correctedBound,
    InitializationResources.bound, InitializationResources.lengthBound,
    MicrostepResources.bound, MicrostepResources.instructionBound,
    MicrostepResources.signQuotientBound, MicrostepResources.zeroShiftBound,
    ArithmeticScheduleResources.selectorBound, ArithmeticSelectionLayout.sourceCount,
    ArithmeticInstruction.includeSign, ArithmeticInstruction.operation,
    ArithmeticWindowPreservation.readsSign, ShiftResources.guardedBound,
    ShiftResources.incrementCount, NativeControl.conditionCount, NativePredicate.gateCount,
    TerminalBoundaryResources.boundaryBound, TerminalBoundaryResources.predicateBound,
    ControlledLengthResources.refreshBound, ControlledLengthResources.predicateBound,
    ClockDecodeResources.count, MAU.Addition.Gidney.biFlipEventBound,
    MAU.Addition.Gidney.comparisonEventBound, MAU.Addition.Gidney.constantOffsetEventBound]

/-- The original variable product's scalar native-occurrence bound at width 256. -/
theorem p256_variableProductBound_eq : VariableGidney.eventBound 256 = 98688172032 := by
  norm_num [VariableGidney.eventBound, Accumulate.Gidney.stageEventBound,
    MAU.Addition.Gidney.modularOffsetEventBound, MAU.Addition.Gidney.pivotEventBound,
    MAU.Addition.Gidney.biFlipEventBound, MAU.Addition.Gidney.comparisonEventBound,
    MAU.Addition.Gidney.constantOffsetEventBound]

private theorem controlled_card (dimension : Nat) (pool : ResourcePool .quantum) :
    (ResourcePool.controlForDimension dimension pool).card = pool.card :=
  Multiset.card_map _ _

private theorem primitive_card : EncodedBit.GateSpec.primitiveAlphabet.card = 3 := rfl

private theorem multiplier_card (width : Nat) :
    (Gidney.nativeBudget width).card =
      12 * (width * Accumulate.Gidney.stageEventBound width) + 3 * width := by
  simp only [Gidney.nativeBudget, Gidney.wordSwapBudget, Accumulate.Gidney.nativeBudget,
    Accumulate.Gidney.nativeAlphabet, MAU.Addition.Gidney.offsetAlphabet,
    Multiset.card_add, Multiset.card_nsmul, controlled_card, primitive_card,
    ResourcePool.ofList, Multiset.coe_card, List.length_replicate]
  ring

/-- Both native MAC pools and the real three-CNOT word swap have this allowance cardinality. -/
theorem p256_multiplierBudget_card : (Gidney.nativeBudget 256).card = 4626008832 := by
  rw [multiplier_card]
  norm_num [Accumulate.Gidney.stageEventBound, MAU.Addition.Gidney.modularOffsetEventBound,
    MAU.Addition.Gidney.pivotEventBound, MAU.Addition.Gidney.biFlipEventBound,
    MAU.Addition.Gidney.comparisonEventBound, MAU.Addition.Gidney.constantOffsetEventBound]

/-- The original multiplier unit-depth allowance uses actual occurrences, not all pool entries. -/
theorem p256_multiplierDepthBound_eq : Gidney.eventBound 256 = 771002112 := by
  norm_num [Gidney.eventBound, Accumulate.Gidney.stageEventBound,
    MAU.Addition.Gidney.modularOffsetEventBound, MAU.Addition.Gidney.pivotEventBound,
    MAU.Addition.Gidney.biFlipEventBound, MAU.Addition.Gidney.comparisonEventBound,
    MAU.Addition.Gidney.constantOffsetEventBound]

/-- All five original measured point stages retain their complete native-coordinate allowance. -/
theorem p256_pointBudget_card :
    (MeasuredPointAddition.events 256).card = 650111046286472970826 := by
  rw [MeasuredPointAddition.measuredPointAddition_budget_card,
    p256_inPlaceForwardBound_eq, p256_variableProductBound_eq]
  norm_num [MAU.Addition.Gidney.modularOffsetEventBound,
    MAU.Addition.Gidney.pivotEventBound, MAU.Addition.Gidney.biFlipEventBound,
    MAU.Addition.Gidney.comparisonEventBound, MAU.Addition.Gidney.constantOffsetEventBound]

/-- The original point-addition serial allowance retains its two parallel Hadamard layers. -/
theorem p256_pointDepthBound_eq :
    MeasuredPointAddition.depthBound 256 = 650111045792983742154 := by
  rw [MeasuredPointAddition.measuredPointAddition_depthBound_eq,
    p256_inPlaceForwardBound_eq, p256_variableProductBound_eq]
  norm_num [MAU.Addition.Gidney.modularOffsetEventBound,
    MAU.Addition.Gidney.pivotEventBound, MAU.Addition.Gidney.biFlipEventBound,
    MAU.Addition.Gidney.comparisonEventBound, MAU.Addition.Gidney.constantOffsetEventBound]

/-- Reset, preparation, conversions, 520 point calls and both readouts remain in the same round. -/
theorem p256_samplingRoundEventBound_eq (I : DomainParameters.PublicKeyInstance) :
    samplingRoundEventBound (DomainParameters.curve I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) = 338057744068984448937498 := by
  rw [samplingRoundEventBound_eq, p256_multiplierBudget_card, p256_pointBudget_card]

/-- The same sampling-round depth is normalized without changing the original parallel stages. -/
theorem p256_samplingRoundUnitDepth_eq (I : DomainParameters.PublicKeyInstance) :
    samplingRoundUnitDepth (DomainParameters.curve I.curveCert)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) = 338057743812354629967117 := by
  rw [samplingRoundUnitDepth_eq, p256_multiplierDepthBound_eq, p256_pointDepthBound_eq]

end

end QuantumAlg.EllipticCurve.P256.Measured

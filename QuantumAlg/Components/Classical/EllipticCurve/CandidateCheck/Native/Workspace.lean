/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Resources
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds

/-!
# Generic native checked-recovery workspace coordinates

These exact arbitrary-width coordinates belong to the actual native checking
components. Both the declared-query and measured arithmetic algorithms apply
them without depending on one another. Persistent destinations and lexical
scratch retain their complete original dimensions.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution QuantumAlg.ClassicalRoutines QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.ClassicalRoutines.NumberTheory QuantumAlg.ClassicalRoutines.FiniteCyclicDLP
open Checked.SignedReduction

private theorem raw_space {kind : ProblemKind} (width : Nat) :
    XGCD.Native.rawScratchSpace kind width = SpacePool.ofShape
      (.bits (5 * width +
        7 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth width + 1)) := by
  ext axis
  cases axis with
  | classicalBits =>
      simp [XGCD.Native.rawScratchSpace, XGCD.Native.stateShapes, XGCD.Native.activeScratchShapes,
        SpacePool.ofShape, XGCD.PureXGCD.executionCoefficientWidth, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [XGCD.Native.rawScratchSpace, XGCD.Native.stateShapes, XGCD.Native.activeScratchShapes,
        SpacePool.ofShape, XGCD.PureXGCD.executionCoefficientWidth]

private theorem signed_space_le {kind : ProblemKind} (width : Nat) :
    Checked.SignedReduction.Native.signedReductionSpaceLimit kind width ≤
      SpacePool.ofShape (.bits (6 * width + 7 * signedWidth width + 7)) := by
  intro axis
  cases axis with
  | classicalBits =>
      simp [Checked.SignedReduction.Native.signedReductionSpaceLimit,
        Checked.SignedReduction.Native.signedReductionScratchSpace,
        Checked.SignedReduction.Native.signedReductionArithmeticSpace,
        Checked.SignedReduction.Native.negativeCorrectionScratchSpace,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Checked.SignedReduction.Native.signedReductionSpaceLimit,
        Checked.SignedReduction.Native.signedReductionScratchSpace,
        Checked.SignedReduction.Native.signedReductionArithmeticSpace,
        Checked.SignedReduction.Native.negativeCorrectionScratchSpace,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max]

private theorem coefficient_active {kind : ProblemKind} (width : Nat) :
    Field.Native.coefficientActiveSpace kind width =
      SpacePool.ofShape (.bits (6 * width + 7 * signedWidth width + 7)) := by
  have bounded := signed_space_le (kind := kind) width
  rw [Field.Native.coefficientActiveSpace, raw_space]
  ext axis
  have bound := bounded axis
  cases axis with
  | classicalBits =>
      simp_all [SpacePool.ofShape, SpacePool.max, Nat.max_eq_max, signedWidth, xgcdWidth,
        XGCD.PureXGCD.executionCoefficientWidth, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp_all [SpacePool.ofShape, SpacePool.max, signedWidth, xgcdWidth,
        XGCD.PureXGCD.executionCoefficientWidth]

private theorem checked_active {kind : ProblemKind} (width : Nat) :
    Checked.Native.checkedInverseActiveSpace kind width =
      SpacePool.ofShape (.bits (6 * width + 7 * signedWidth width + 7)) := by
  have bounded := signed_space_le (kind := kind) width
  rw [Checked.Native.checkedInverseActiveSpace, raw_space]
  ext axis
  have bound := bounded axis
  cases axis with
  | classicalBits =>
      simp_all [Checked.Native.checkedSelectionSpaceLimit, SpacePool.ofShape, SpacePool.max,
        Nat.max_eq_max,
        signedWidth, xgcdWidth, XGCD.PureXGCD.executionCoefficientWidth, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp_all [Checked.Native.checkedSelectionSpaceLimit, SpacePool.ofShape, SpacePool.max,
        signedWidth, xgcdWidth, XGCD.PureXGCD.executionCoefficientWidth]

private theorem affine_active {kind : ProblemKind} (width : Nat) :
    Add.Native.affineActiveSpace kind width =
      SpacePool.ofShape (.bits (8 * width + 9 * signedWidth width + 9)) := by
  have positive := signedWidth_pos width
  rw [Add.Native.affineActiveSpace, coefficient_active]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Field.Native.coefficientShapes, Field.Native.multiplicationScratchSpace,
        Field.Native.subtractionShapes, Field.Native.subtractionReductionSpace,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Field.Native.coefficientShapes, Field.Native.multiplicationScratchSpace,
        Field.Native.subtractionShapes, Field.Native.subtractionReductionSpace,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max]

private theorem generic_active {kind : ProblemKind} (width : Nat) :
    Add.Native.genericActiveSpace kind width =
      SpacePool.ofShape (.bits (16 * width + 9 * signedWidth width + 10)) := by
  rw [Add.Native.genericActiveSpace, affine_active]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Field.Native.subtractionShapes, Field.Native.subtractionReductionSpace,
        Add.Native.affineShapes, Modular.Reduce.Native.divisionShape, SpacePool.ofShape,
        SpacePool.max, Nat.max_eq_max, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Field.Native.subtractionShapes, Field.Native.subtractionReductionSpace,
        Add.Native.affineShapes, Modular.Reduce.Native.divisionShape, SpacePool.ofShape,
        SpacePool.max]

private theorem doubling_active {kind : ProblemKind} (width : Nat) :
    Add.Native.doublingActiveSpace kind width =
      SpacePool.ofShape (.bits (16 * width + 9 * signedWidth width + 10)) := by
  rw [Add.Native.doublingActiveSpace, affine_active]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Field.Native.multiplicationScratchSpace, Field.Native.additionShapes,
        Field.Native.additionReductionSpace, Add.Native.affineShapes,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Field.Native.multiplicationScratchSpace, Field.Native.additionShapes,
        Field.Native.additionReductionSpace, Add.Native.affineShapes,
        Modular.Reduce.Native.divisionShape, SpacePool.ofShape, SpacePool.max]

private theorem addition_scratch {kind : ProblemKind} (width : Nat) :
    Add.Native.additionScratchSpace kind width =
      SpacePool.ofShape (.bits (27 * width + 9 * signedWidth width + 15)) := by
  simp only [Add.Native.additionScratchSpace, Add.Native.additionActiveSpace,
    Add.Native.caseMaximum, Add.Native.additionArmSpace, doubling_active, generic_active]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Add.Native.classifierShapes, Add.Native.infinityShapes, Add.Native.doublingShapes,
        Add.Native.genericShapes, PointEquality.RawPointShape, SpacePool.ofShape,
        SpacePool.max, Nat.max_eq_max, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Add.Native.classifierShapes, Add.Native.infinityShapes, Add.Native.doublingShapes,
        Add.Native.genericShapes, PointEquality.RawPointShape, SpacePool.ofShape,
        SpacePool.max]

private theorem verification_scratch {kind : ProblemKind} (width : Nat) :
    verificationScratchSpace kind width =
      SpacePool.ofShape (.bits (27 * width + 9 * signedWidth width + 15)) := by
  rw [verificationScratchSpace, ScalarMul.Native.scalarScratchSpace,
    addition_scratch]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Add.Native.infinityShapes, PointEquality.Native.scratchShapes,
        PointEquality.RawPointShape, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Add.Native.infinityShapes, PointEquality.Native.scratchShapes,
        PointEquality.RawPointShape, SpacePool.ofShape, SpacePool.max]

private theorem checked_recovery {kind : ProblemKind} (width : Nat) :
    RawRecovery.Native.checkedRecoveryActiveSpace kind width =
      SpacePool.ofShape (.bits (8 * width + 9 * signedWidth width + 9)) := by
  rw [RawRecovery.Native.checkedRecoveryActiveSpace, checked_active]
  simp only [RawRecovery.Native.selectedRecoveryScratchSpace, if_true,
    NormalizedRecovery.Native.recoveryScratchSpace_eq_bits]
  ext axis
  cases axis with
  | classicalBits =>
      simp [Checked.Native.checkedInverseShapes, FiniteCyclicDLP.OutputShape,
        SpacePool.ofShape, SpacePool.max, Nat.max_eq_max, CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [Checked.Native.checkedInverseShapes, FiniteCyclicDLP.OutputShape,
        SpacePool.ofShape, SpacePool.max]

private theorem exposure_active {kind : ProblemKind} (width : Nat) :
    RawRecovery.Native.singleExposureActiveSpace kind width =
      SpacePool.ofShape (.bits (9 * width + 9 * signedWidth width + 10)) := by
  rw [RawRecovery.Native.singleExposureActiveSpace,
    RawRecovery.Native.checkedExposurePersistentSpace, checked_recovery]
  ext axis
  cases axis with
  | classicalBits =>
      simp [RawRecovery.Native.checkedResultShapes, SpacePool.ofShape, SpacePool.max,
        Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [RawRecovery.Native.checkedResultShapes, SpacePool.ofShape, SpacePool.max]

/-- The original successive scratch scopes retain only the necessary field/sample maximum. -/
theorem recoveryTailScratchSpace_eq_bits (kind : ProblemKind)
    (fieldWidth sampleWidth : Nat) :
    recoveryTailScratchSpace kind fieldWidth sampleWidth =
      SpacePool.ofShape (.bits (max
        (25 * sampleWidth + 9 * signedWidth sampleWidth + 16)
        (27 * fieldWidth + 9 * signedWidth fieldWidth + 15))) := by
  rw [recoveryTailScratchSpace, attemptScratchSpace,
    exposure_active, verification_scratch]
  ext axis
  cases axis with
  | classicalBits =>
      simp [RawRecovery.Native.preparationShapes, RawRecovery.Native.scaleDivisionShape,
        FirstAccepted.selectionScratchSpace, SpacePool.ofShape, SpacePool.max, Nat.max_eq_max,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [RawRecovery.Native.preparationShapes, RawRecovery.Native.scaleDivisionShape,
        FirstAccepted.selectionScratchSpace, SpacePool.ofShape, SpacePool.max]

/-- The seven actual persistent cells contribute two scalar words, one point and four bits. -/
theorem persistentCellSpace_eq_bits (kind : ProblemKind) (fieldWidth sampleWidth : Nat) :
    persistentCellSpace kind fieldWidth sampleWidth =
      SpacePool.ofShape (.bits (2 * fieldWidth + 2 * sampleWidth + 5)) := by
  ext axis
  cases axis with
  | classicalBits =>
      simp [persistentCellSpace, PointShape, SpacePool.ofShape,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [persistentCellSpace, PointShape, SpacePool.ofShape]



end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

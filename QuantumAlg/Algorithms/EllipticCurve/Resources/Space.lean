/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Resources

/-!
# Explicit native space coordinates of actual repeated elliptic-curve recovery

Write `w = p.size`, `f = Canonical.Layout.fieldWidth E`, `t = orderWidth problem`
and `c(u) = executionCoefficientWidth (u + 1)`. The original widened XGCD
coefficient width is retained exactly. Successive recovery and point-verification
scopes require `max (25*t + 9*c(t) + 16) (27*f + 9*c(f) + 15)` classical bits.

The full resident allowance adds `6*f + 4*t + w + 7` bits, and its auxiliary
allowance adds `2*f + 4*t + w + 5` bits. Both have exactly
`3*w + 4*w.size + 12 + 2*t` qubits and zero systems of every other dimension.
These are coordinates of independent allowances, not definitions using execution
peaks. Seven persistent cells and the recovery scratch are charged only once.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

open Execution ClassicalRoutines ClassicalRoutines.EllipticCurve
open ClassicalRoutines.NumberTheory ClassicalRoutines.FiniteCyclicDLP
open Checked.SignedReduction
open PrimeFieldShortWeierstrass QuantumAlg.FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured
open ScalarMultiplication.MeasuredPlacement

noncomputable section

private theorem clog_two : Nat.clog 2 2 = 1 := by decide

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
    CandidateCheck.Native.verificationScratchSpace kind width =
      SpacePool.ofShape (.bits (27 * width + 9 * signedWidth width + 15)) := by
  rw [CandidateCheck.Native.verificationScratchSpace, ScalarMul.Native.scalarScratchSpace,
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
  rw [RawRecovery.Native.singleExposureActiveSpace, checked_recovery]
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
theorem recoveryTailScratchSpace_eq_bits (kind : ProblemKind) (fieldWidth sampleWidth : Nat) :
    CandidateCheck.Native.recoveryTailScratchSpace kind fieldWidth sampleWidth =
      SpacePool.ofShape (.bits (max
        (25 * sampleWidth + 9 * signedWidth sampleWidth + 16)
        (27 * fieldWidth + 9 * signedWidth fieldWidth + 15))) := by
  rw [CandidateCheck.Native.recoveryTailScratchSpace, CandidateCheck.Native.attemptScratchSpace,
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
    CandidateCheck.Native.persistentCellSpace kind fieldWidth sampleWidth =
      SpacePool.ofShape (.bits (2 * fieldWidth + 2 * sampleWidth + 5)) := by
  ext axis
  cases axis with
  | classicalBits =>
      simp [CandidateCheck.Native.persistentCellSpace, PointShape, SpacePool.ofShape,
        CShape.bitWidth]
      omega
  | quantumSystems dimension =>
      simp [CandidateCheck.Native.persistentCellSpace, PointShape, SpacePool.ofShape]

/-- The original ready context has exactly its measured finite-two classical bank. -/
theorem readySpace_classicalBits (width count : Nat) :
    SpacePool.count .classicalBits (readySpace width count) = width := by
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space, CShape.bitWidth,
    clog_two]

/-- Every original ready quantum system is a qubit, with its physical count retained. -/
theorem readySpace_quantumSystems (width count : Nat) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (readySpace width count) =
      if 2 = dimension then 3 * width + 4 * width.size + 12 + count else 0 := by
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)

/-- Terminal classical result cells and both public borrowed point values remain resident. -/
theorem terminal_residentSpace (width : Nat) :
    (PublicInput.terminal E width).residentSpace =
      (2 * width) • SpacePool.ofShape (.finite 2) + readySpace p.size (2 * width) +
        2 • SpacePool.ofShape (ECDLP.Canonical.Runtime.Context.PointShape E) := by
  rw [PublicInput.terminal, RuntimeCtx.residentSpace_disjointUnion,
    exponentMeasurementContext_resident, Allocation.after_resident, PublicInput.frame_resident]

/-- Public borrowed points add no auxiliary storage to the retained measurement context. -/
theorem terminal_auxiliarySpace (width : Nat) :
    (PublicInput.terminal E width).auxiliarySpace =
      (2 * width) • SpacePool.ofShape (.finite 2) + readySpace p.size (2 * width) := by
  rw [PublicInput.terminal, RuntimeCtx.auxiliarySpace_disjointUnion,
    exponentMeasurementContext_auxiliary, Allocation.after_auxiliary,
    PublicInput.frame_auxiliary, add_zero]

/-- Exact classical bits of the independent complete resident allowance. -/
theorem residentAllowance_classicalBits (problem : KnownOrderProblem E.GroupPoint) :
    SpacePool.count .classicalBits
      (CandidateCheck.Native.recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        CandidateCheck.Native.persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) + (PublicInput.terminal E (orderWidth problem)).residentSpace) =
      max (25 * orderWidth problem + 9 * signedWidth (orderWidth problem) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * signedWidth (ECDLP.Canonical.Layout.fieldWidth E) + 15) +
        6 * ECDLP.Canonical.Layout.fieldWidth E + 4 * orderWidth problem + p.size + 7 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits, terminal_residentSpace]
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space,
    ECDLP.Canonical.Runtime.Context.PointShape, PointShape, CShape.bitWidth, clog_two]
  omega

/-- Exact classical bits of the independent complete auxiliary allowance. -/
theorem auxiliaryAllowance_classicalBits (problem : KnownOrderProblem E.GroupPoint) :
    SpacePool.count .classicalBits
      (CandidateCheck.Native.recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        CandidateCheck.Native.persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) + (PublicInput.terminal E (orderWidth problem)).auxiliarySpace) =
      max (25 * orderWidth problem + 9 * signedWidth (orderWidth problem) + 16)
        (27 * ECDLP.Canonical.Layout.fieldWidth E +
          9 * signedWidth (ECDLP.Canonical.Layout.fieldWidth E) + 15) +
        2 * ECDLP.Canonical.Layout.fieldWidth E + 4 * orderWidth problem + p.size + 5 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits, terminal_auxiliarySpace]
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space, CShape.bitWidth,
    clog_two]
  omega

/-- The independent resident allowance retains every original qubit and no other dimension. -/
theorem residentAllowance_quantumSystems (problem : KnownOrderProblem E.GroupPoint)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (CandidateCheck.Native.recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        CandidateCheck.Native.persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) + (PublicInput.terminal E (orderWidth problem)).residentSpace) =
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 12 + 2 * orderWidth problem else 0 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits, terminal_residentSpace]
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space]

/-- Auxiliary space has the same quantum coordinates, as both public inputs are classical. -/
theorem auxiliaryAllowance_quantumSystems (problem : KnownOrderProblem E.GroupPoint)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (CandidateCheck.Native.recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) +
        CandidateCheck.Native.persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem) + (PublicInput.terminal E (orderWidth problem)).auxiliarySpace) =
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 12 + 2 * orderWidth problem else 0 := by
  rw [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits, terminal_auxiliarySpace]
  simp [readySpace, SpacePool.count, SpacePool.ofShape, OwnedQubits.space]

end

end QuantumAlg.EllipticCurve.LogicalResources

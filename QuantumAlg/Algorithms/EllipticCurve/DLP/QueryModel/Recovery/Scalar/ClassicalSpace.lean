/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
public import QuantumAlg.Core.Base.Accounting.Space



import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Workspace
import all QuantumAlg.Util.Classical.NumberTheory.Extended.Bounds
import all QuantumAlg.Core.Base.Accounting.Shape
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Complete classical storage coordinates of the actual declared ECDLP run

All retained results, the dedicated reset cell, borrowed point inputs and reused
checking scratch remain in their original storage roles. The original arbitrary
operand coefficient implementation is bounded symbolically by its generic width
lemma; no operand domain or fixed instance is evaluated.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open ClassicalRoutines.NumberTheory.Checked.SignedReduction

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local irreducible] ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth

private theorem finite_two_width : Nat.clog 2 2 = 1 := by decide

private theorem original_resident (I : ECDLPInstance E) :
    (Sampling.pre I).residentSpace =
      2 • SpacePool.ofShape (.ellipticCurvePoint (fieldWidth E)) := by
  simp only [Sampling.pre, Runtime.Context.pre, Runtime.Context.baseInputCtx,
    RuntimeCtx.residentSpace_addBorrowedInput, RuntimeCtx.residentSpace_empty]
  change SpacePool.ofShape (.ellipticCurvePoint (fieldWidth E)) +
    (SpacePool.ofShape (.ellipticCurvePoint (fieldWidth E)) + 0) = _
  simp only [add_zero, two_nsmul]

private theorem original_auxiliary (I : ECDLPInstance E) :
    (Sampling.pre I).auxiliarySpace = 0 := by
  simp only [Sampling.pre, Runtime.Context.pre, Runtime.Context.baseInputCtx,
    RuntimeCtx.auxiliarySpace_addBorrowedInput, RuntimeCtx.auxiliarySpace_empty]

/-- Both actual live classical allowances include every retained result and borrowed point. -/
theorem whole_memory_classical_coordinates (I : ECDLPInstance E) :
    SpacePool.count .classicalBits (tailResidentBudget I) =
        max (25 * scalarWidth I + 9 * signedWidth (scalarWidth I) + 16)
          (27 * fieldWidth E + 9 * signedWidth (fieldWidth E) + 15) +
            6 * fieldWidth E + 4 * scalarWidth I + 8 ∧
    SpacePool.count .classicalBits (tailAuxiliaryBudget I) =
        max (25 * scalarWidth I + 9 * signedWidth (scalarWidth I) + 16)
          (27 * fieldWidth E + 9 * signedWidth (fieldWidth E) + 15) +
            2 * fieldWidth E + 4 * scalarWidth I + 6 := by
  simp only [tailResidentBudget, tailAuxiliaryBudget, recoveryTailScratchSpace_eq_bits,
    persistentCellSpace_eq_bits, Sampling.Reuse.ecdlpReuse_context_resident,
    Sampling.Reuse.ecdlpReuse_context_auxiliary, Sampling.post_residentSpace,
    Sampling.post_auxiliarySpace, original_resident, original_auxiliary]
  simp [SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    CShape.bitWidth, Sampling.sampleWidth, scalarWidth, finite_two_width]
  omega

/-- The original coefficient implementation has a width-only bound without operand enumeration. -/
theorem original_signed_width_scalar (width : Nat) :
    signedWidth width ≤ (width + 1) * (2 * (width + 1) + 1) + 3 :=
  ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_le_quadratic (width + 1)

/-- Parameter-only ceilings bound both original classical storage inventories. -/
public theorem whole_memory_classical_scalar (I : ECDLPInstance E) :
    SpacePool.count .classicalBits (tailResidentBudget I) ≤
        Scalar.residentBits (fieldWidth E) (scalarWidth I) ∧
      SpacePool.count .classicalBits (tailAuxiliaryBudget I) ≤
        Scalar.auxiliaryBits (fieldWidth E) (scalarWidth I) := by
  rw [(whole_memory_classical_coordinates I).1, (whole_memory_classical_coordinates I).2]
  have scalarBound := original_signed_width_scalar (scalarWidth I)
  have fieldBound := original_signed_width_scalar (fieldWidth E)
  dsimp [Scalar.residentBits, Scalar.auxiliaryBits, Scalar.scratchBits, Scalar.coefficientBits]
  constructor <;> omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

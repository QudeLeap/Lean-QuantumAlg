/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Space
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Schedule
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Classical.Retained.Bounds
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Space of the actual allocation and signed preparation initialization

The real bank, 520 results and ten table cells remain live around the signed
preparation scratch. Every bound preserves the original caller's resident or
auxiliary pool explicitly, independently of any later sampler.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open WindowTables.Outer.Preparation

attribute [local irreducible] RuntimeCtx.residentSpace RuntimeCtx.auxiliarySpace
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace
  WindowTables.Outer.coefficientScratchSpace WindowTables.Outer.sharedSpace
  RetainedCells.context MeasurementCells.context
  SpacePool.ofShape SpacePool.ofQuantumLayout

variable {services : ClassicalOracleModel}
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private lemma retained_result_residentSpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) (shapes : List CShape) :
    (RetainedCells.context (MeasurementCells.context ctx dimension count) shapes).residentSpace =
      (shapes.map (SpacePool.ofShape (kind := kind))).sum +
        (count • SpacePool.ofShape (.finite dimension) + ctx.residentSpace) :=
  (RetainedCells.context_residentSpace _ _).trans
    (congrArg (fun pool => (shapes.map SpacePool.ofShape).sum + pool)
      (MeasurementCells.context_residentSpace ctx dimension count))

private lemma retained_result_auxiliarySpace {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) (shapes : List CShape) :
    (RetainedCells.context (MeasurementCells.context ctx dimension count) shapes).auxiliarySpace =
      (shapes.map (SpacePool.ofShape (kind := kind))).sum +
        (count • SpacePool.ofShape (.finite dimension) + ctx.auxiliarySpace) :=
  (RetainedCells.context_auxiliarySpace _ _).trans
    (congrArg (fun pool => (shapes.map SpacePool.ofShape).sum + pool)
      (MeasurementCells.context_auxiliarySpace ctx dimension count))

/-- The exact post-allocation resident pool contains all three real allocations. -/
lemma tableContext_residentSpace :
    (tableContext base noQuantum).residentSpace =
      WindowTables.Outer.sharedSpace .quantum 256 +
        (520 • SpacePool.ofShape (.finite 2) +
          (SpacePool.ofQuantumLayout (QubitLayout.canonical encoding.width).toQuantum +
            base.residentSpace)) := by
  simpa only [WindowTables.Outer.sharedSpace, tableContext, resultContext] using
    (retained_result_residentSpace (bankContext base noQuantum) 2 520
    (WindowTables.Outer.sharedShapes 256)).trans
      (congrArg (fun pool : SpacePool .quantum =>
        ((WindowTables.Outer.sharedShapes 256).map SpacePool.ofShape).sum +
          (520 • SpacePool.ofShape (.finite 2) + pool))
          (RuntimeCtx.residentSpace_addOwnedLayout base base.canonicalFreshKey
            (QubitLayout.canonical encoding.width).toQuantum
            base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)))

/-- Both real retained banks and the owned physical bank also count as auxiliary space. -/
lemma tableContext_auxiliarySpace :
    (tableContext base noQuantum).auxiliarySpace =
      WindowTables.Outer.sharedSpace .quantum 256 +
        (520 • SpacePool.ofShape (.finite 2) +
          (SpacePool.ofQuantumLayout (QubitLayout.canonical encoding.width).toQuantum +
            base.auxiliarySpace)) := by
  simpa only [WindowTables.Outer.sharedSpace, tableContext, resultContext] using
    (retained_result_auxiliarySpace (bankContext base noQuantum) 2 520
    (WindowTables.Outer.sharedShapes 256)).trans
      (congrArg (fun pool : SpacePool .quantum =>
        ((WindowTables.Outer.sharedShapes 256).map SpacePool.ofShape).sum +
          (520 • SpacePool.ofShape (.finite 2) + pool))
          (RuntimeCtx.auxiliarySpace_addOwnedLayout base base.canonicalFreshKey
            (QubitLayout.canonical encoding.width).toQuantum
            base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)))

private lemma allocated_count (caller : SpacePool .quantum) (width count : Nat)
    {systems : Nat} (layout : QuantumLayout systems) (axis : SpaceAxis .quantum) :
    SpacePool.count axis (WindowTables.Outer.sharedSpace .quantum width +
      (count • SpacePool.ofShape (.finite 2) + (SpacePool.ofQuantumLayout layout + caller))) =
      WindowTables.Outer.sharedSpace .quantum width axis +
        (count * SpacePool.ofShape (.finite 2) axis +
          (SpacePool.ofQuantumLayout layout axis + caller axis)) := by
  simp only [SpacePool.count, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply]
  rfl

private lemma allocated_classical (caller : SpacePool .quantum) :
    SpacePool.count .classicalBits (WindowTables.Outer.sharedSpace .quantum 256 +
      (520 • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (QubitLayout.canonical encoding.width).toQuantum + caller))) =
      19977 + caller .classicalBits := by
  rw [allocated_count, WindowTables.Outer.sharedSpace_classicalBits]
  simp only [SpacePool.ofShape, SpacePool.ofQuantumLayout, CShape.bitWidth]
  rw [Nat.clog_eq_one (by decide) (by decide)]
  omega

private lemma allocated_quantum (caller : SpacePool .quantum) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      (WindowTables.Outer.sharedSpace .quantum 256 +
        (520 • SpacePool.ofShape (.finite 2) +
          (SpacePool.ofQuantumLayout (QubitLayout.canonical encoding.width).toQuantum + caller))) =
      (if (2 : ℕ+) = dimension then 854 else 0) + caller (.quantumSystems dimension) := by
  rw [allocated_count, WindowTables.Outer.sharedSpace_quantumSystems]
  simp only [SpacePool.ofShape, Nat.mul_zero, Nat.zero_add, SpacePool.ofQuantumLayout]
  change (QubitLayout.canonical encoding.width).toQuantumLayout.dimensionCount dimension +
    caller (.quantumSystems dimension) = _
  rw [QubitLayout.toQuantumLayout_dimensionCount, encoding_width]

/-- Exact live classical bits after all real allocations, including the caller. -/
lemma tableContext_resident_classicalBits :
    (tableContext base noQuantum).residentSpace .classicalBits =
      19977 + base.residentSpace .classicalBits :=
  (congrArg (SpacePool.count .classicalBits) (tableContext_residentSpace base noQuantum)).trans
    (allocated_classical base.residentSpace)

/-- Exact auxiliary classical bits preserve the caller's original role. -/
lemma tableContext_auxiliary_classicalBits :
    (tableContext base noQuantum).auxiliarySpace .classicalBits =
      19977 + base.auxiliarySpace .classicalBits :=
  (congrArg (SpacePool.count .classicalBits) (tableContext_auxiliarySpace base noQuantum)).trans
    (allocated_classical base.auxiliarySpace)

/-- The actual owned bank contributes only its 854 dimension-two systems. -/
lemma tableContext_resident_quantumSystems (dimension : ℕ+) :
    (tableContext base noQuantum).residentSpace (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then 854 else 0) +
        base.residentSpace (.quantumSystems dimension) :=
  (congrArg (SpacePool.count (.quantumSystems dimension))
    (tableContext_residentSpace base noQuantum)).trans
      (allocated_quantum base.residentSpace dimension)

/-- The same owned bank also contributes to the auxiliary coordinate. -/
lemma tableContext_auxiliary_quantumSystems (dimension : ℕ+) :
    (tableContext base noQuantum).auxiliarySpace (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then 854 else 0) +
        base.auxiliarySpace (.quantumSystems dimension) :=
  (congrArg (SpacePool.count (.quantumSystems dimension))
    (tableContext_auxiliarySpace base noQuantum)).trans
      (allocated_quantum base.auxiliarySpace dimension)

private lemma allocate_retained_resident_le {model : ExecutionModel}
    {before current : RuntimeCtx model.kind} (initialization : Circuit model before current)
    (prefixBound : ∀ path, initialization.peakResidentSpace path ≤ current.residentSpace)
    (dimension : ℕ+) (count : Nat) (shapes : List CShape)
    (path : ((initialization.seq (MeasurementCells.allocate current dimension count)).seq
      (RetainedCells.allocate (MeasurementCells.context current dimension count) shapes)).Path) :
    Circuit.peakResidentSpace
      ((initialization.seq (MeasurementCells.allocate current dimension count)).seq
        (RetainedCells.allocate (MeasurementCells.context current dimension count) shapes)) path ≤
      (RetainedCells.context
        (MeasurementCells.context current dimension count) shapes).residentSpace := by
  have first : current.residentSpace ≤
      (MeasurementCells.context current dimension count).residentSpace := by
    rw [MeasurementCells.context_residentSpace]
    exact le_add_of_nonneg_left zero_le
  have second : (MeasurementCells.context current dimension count).residentSpace ≤
      (RetainedCells.context
        (MeasurementCells.context current dimension count) shapes).residentSpace := by
    rw [RetainedCells.context_residentSpace]
    exact le_add_of_nonneg_left zero_le
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact (prefixBound path.1.1).trans (first.trans second)
    · exact (MeasurementCells.allocate_peakResidentSpace
        current dimension count path.1.2).trans second
  · exact RetainedCells.allocate_peakResidentSpace _ shapes path.2

private lemma allocate_retained_auxiliary_le {model : ExecutionModel}
    {before current : RuntimeCtx model.kind} (initialization : Circuit model before current)
    (prefixBound : ∀ path, initialization.peakAuxiliarySpace path ≤ current.auxiliarySpace)
    (dimension : ℕ+) (count : Nat) (shapes : List CShape)
    (path : ((initialization.seq (MeasurementCells.allocate current dimension count)).seq
      (RetainedCells.allocate (MeasurementCells.context current dimension count) shapes)).Path) :
    Circuit.peakAuxiliarySpace
      ((initialization.seq (MeasurementCells.allocate current dimension count)).seq
        (RetainedCells.allocate (MeasurementCells.context current dimension count) shapes)) path ≤
      (RetainedCells.context
        (MeasurementCells.context current dimension count) shapes).auxiliarySpace := by
  have first : current.auxiliarySpace ≤
      (MeasurementCells.context current dimension count).auxiliarySpace := by
    rw [MeasurementCells.context_auxiliarySpace]
    exact le_add_of_nonneg_left zero_le
  have second : (MeasurementCells.context current dimension count).auxiliarySpace ≤
      (RetainedCells.context
        (MeasurementCells.context current dimension count) shapes).auxiliarySpace := by
    rw [RetainedCells.context_auxiliarySpace]
    exact le_add_of_nonneg_left zero_le
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact (prefixBound path.1.1).trans (first.trans second)
    · exact (MeasurementCells.allocate_peakAuxiliarySpace
        current dimension count path.1.2).trans second
  · exact RetainedCells.allocate_peakAuxiliarySpace _ shapes path.2

/-- Every actual allocation fits its complete resident post-context. -/
lemma prepareWithTables_resident_le
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    (prepareWithTables (services := services) base noQuantum).peakResidentSpace path ≤
      (tableContext base noQuantum).residentSpace := by
  exact allocate_retained_resident_le
    (Circuit.prepareZero base base.canonicalFreshKey
      (QubitLayout.canonical encoding.width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum))
    (fun selected => (Circuit.prepare_peakResidentSpace _ _ _ _ _ selected).le)
    2 520 (WindowTables.Outer.sharedShapes 256) path

/-- The same actual allocations fit their complete auxiliary post-context. -/
lemma prepareWithTables_auxiliary_le
    (path : (prepareWithTables (services := services) base noQuantum).Path) :
    (prepareWithTables (services := services) base noQuantum).peakAuxiliarySpace path ≤
      (tableContext base noQuantum).auxiliarySpace := by
  exact allocate_retained_auxiliary_le
    (Circuit.prepareZero base base.canonicalFreshKey
      (QubitLayout.canonical encoding.width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum))
    (fun selected => (Circuit.prepare_peakAuxiliarySpace _ _ _ _ _ selected).le)
    2 520 (WindowTables.Outer.sharedShapes 256) path

private lemma signed_additional_classical (width : Nat) :
    Signed.additionalSpace .quantum width .classicalBits =
      5 * width + 2 + Nat.max (8 * width + 10)
        (WindowTables.Outer.coefficientScratchSpace .quantum width .classicalBits) := by
  have subtraction := Field.Native.subtractionScratch_classicalBits
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (width := width)
  change Signed.subtractionSpace .quantum width .classicalBits = 8 * width + 10 at subtraction
  simp only [Signed.additionalSpace, Signed.arithmeticSpace, Pi.add_apply, SpacePool.max,
    subtraction]
  simp [Signed.scratchShapes, PointEquality.RawPointShape, SpacePool.ofShape, CShape.bitWidth]
  omega

private lemma signed_fixed_limit {coefficient : Nat} (bounded : coefficient ≤ 1193279) :
    5 * 256 + 2 + Nat.max (8 * 256 + 10) coefficient ≤ 1194561 := by
  have combined : Nat.max (8 * 256 + 10) coefficient ≤ 1193279 :=
    max_le (by decide) bounded
  omega

private lemma signed_additional_classical_le :
    Signed.additionalSpace .quantum 256 .classicalBits ≤ 1194561 := by
  rw [signed_additional_classical]
  exact signed_fixed_limit
    (WindowTables.Outer.coefficientScratchSpace256_classicalBits_le .quantum)

private lemma signed_additional_quantum (dimension : ℕ+) :
    Signed.additionalSpace .quantum 256 (.quantumSystems dimension) = 0 := by
  have original := WindowTables.Outer.roundAdditionalSpace_quantumSystems dimension
  have coefficient : WindowTables.Outer.coefficientScratchSpace .quantum 256
      (.quantumSystems dimension) = 0 := by
    simp only [WindowTables.Outer.roundAdditionalSpace, Pi.add_apply,
      WindowTables.Outer.sharedSpace_quantumSystems,
      WindowTables.Outer.tableSpace_quantumSystems, Nat.zero_add] at original
    exact original
  simp [Signed.additionalSpace, Signed.arithmeticSpace, Signed.subtractionSpace,
    Signed.scratchShapes, Field.Native.subtractionShapes, Field.Native.subtractionReductionSpace,
    SpacePool.max, SpacePool.ofShape, coefficient]

private lemma signed_additional_le :
    Signed.additionalSpace .quantum 256 ≤ SpacePool.ofShape (.bits 1194561) := by
  intro axis
  cases axis with
  | classicalBits => exact signed_additional_classical_le.trans (by norm_num [SpacePool.ofShape])
  | quantumSystems dimension => simp only [signed_additional_quantum, SpacePool.ofShape, le_refl]

variable (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256))

/-- Actual signed preparation adds its proved scratch peak over the real retained context. -/
lemma paidPrefix_space
    (path : (paidPrefix (services := services) base noQuantum I basePoint targetPoint).Path) :
    (paidPrefix (services := services) base noQuantum I basePoint targetPoint).peakResidentSpace
        path ≤ SpacePool.ofShape (.bits 1194561) + (tableContext base noQuantum).residentSpace ∧
      (paidPrefix (services := services) base noQuantum I basePoint targetPoint).peakAuxiliarySpace
        path ≤ SpacePool.ofShape (.bits 1194561) +
          (tableContext base noQuantum).auxiliarySpace := by
  have preparation := Signed.prepare_space
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (tableFrame base noQuantum) (actualCurveSpec I).field (actualCurveSpec I).curve.a.val
    (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint) path.2
  unfold paidPrefix at path ⊢
  rw [Circuit.peakResidentSpace_seq, Circuit.peakAuxiliarySpace_seq]
  exact ⟨SpacePool.max_le
    ((prepareWithTables_resident_le base noQuantum path.1).trans
      (le_add_of_nonneg_left zero_le))
    (preparation.1.trans (add_le_add signed_additional_le le_rfl)),
    SpacePool.max_le
      ((prepareWithTables_auxiliary_le base noQuantum path.1).trans
        (le_add_of_nonneg_left zero_le))
      (preparation.2.trans (add_le_add signed_additional_le le_rfl))⟩


end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

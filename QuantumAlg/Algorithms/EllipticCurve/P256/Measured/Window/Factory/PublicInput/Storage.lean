/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Support

/-! # Original borrowed point storage through the paid factory allocations -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open Execution Execution.ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve ClassicalAlgorithms.EllipticCurve

noncomputable section

private lemma storage_width_cast {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first second : Nat} (same : first = second)
    (ref : CStorageRef ctx (PointShape first)) :
    ∃ result : CStorageRef ctx (PointShape second),
      cast (congrArg (fun width => CInputRef ctx (PointShape width)) same)
        (.storage ref) = .storage result := by
  cases same
  exact ⟨ref, rfl⟩

/-- The width cast retains the original borrowed base storage cell. -/
lemma publicBaseRef_storage (I : DomainParameters.PublicKeyInstance) :
    ∃ ref : CStorageRef (publicFrame I) (PointShape 256),
      publicBaseRef I = .storage ref := by
  unfold publicBaseRef ECDLP.Measured.Recovery.PublicInput.baseRef
  exact storage_width_cast (originalFieldWidth_eq_256 I) _

/-- The width cast retains the original borrowed target storage cell. -/
lemma publicTargetRef_storage (I : DomainParameters.PublicKeyInstance) :
    ∃ ref : CStorageRef (publicFrame I) (PointShape 256),
      publicTargetRef I = .storage ref := by
  unfold publicTargetRef ECDLP.Measured.Recovery.PublicInput.targetRef
  exact storage_width_cast (originalFieldWidth_eq_256 I) _

private lemma measurement_lift_storage {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (dimension : ℕ+) (ref : CStorageRef ctx shape) (count : Nat) :
    ∃ result : CStorageRef (MeasurementCells.context ctx dimension count) shape,
      MeasurementCells.liftInput dimension (.storage ref) count = .storage result := by
  induction count with
  | zero => exact ⟨ref, rfl⟩
  | succ count induction =>
      obtain ⟨result, same⟩ := induction
      refine ⟨result.underRetained
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh, ?_⟩
      rw [MeasurementCells.liftInput, same]
      rfl

private lemma originalInputAfterTables_storage (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {shape : CShape} (ref : CStorageRef base shape) :
    ∃ result : CStorageRef (tableContext base noQuantum) shape,
      originalInputAfterTables base noQuantum (.storage ref) = .storage result := by
  obtain ⟨result, same⟩ := measurement_lift_storage 2
    (ref.underOwnedLayout base.canonicalFreshKey
      (QubitLayout.canonical encoding.width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum)) 520
  refine ⟨(RetainedCells.transport (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256)).liftStorage result, ?_⟩
  unfold originalInputAfterTables originalInput CInputRef.underOwnedLayout
  rw [same]
  rfl

private lemma inputs_base_port {ctx : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (results : Fourier.Results ctx)
    (frame : WindowTables.Outer.Frame ctx 256)
    (basePoint targetPoint : CInputRef ctx (PointShape 256)) :
    (inputs I sameWires results frame basePoint targetPoint).base = basePoint := rfl

private lemma inputs_target_port {ctx : RuntimeCtx .quantum}
    (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (results : Fourier.Results ctx)
    (frame : WindowTables.Outer.Frame ctx 256)
    (basePoint targetPoint : CInputRef ctx (PointShape 256)) :
    (inputs I sameWires results frame basePoint targetPoint).target = targetPoint := rfl

private lemma retainedInputs_base (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256)) :
    (retainedInputs base noQuantum I basePoint targetPoint).base =
      originalInputAfterTables base noQuantum basePoint := by
  exact @inputs_base_port (tableContext base noQuantum) I
    (tableContext_wires base noQuantum) (resultsAfterTables base noQuantum)
    (tableFrame base noQuantum) (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint)

private lemma retainedInputs_target (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : DomainParameters.PublicKeyInstance)
    (basePoint targetPoint : CInputRef base (PointShape 256)) :
    (retainedInputs base noQuantum I basePoint targetPoint).target =
      originalInputAfterTables base noQuantum targetPoint := by
  exact @inputs_target_port (tableContext base noQuantum) I
    (tableContext_wires base noQuantum) (resultsAfterTables base noQuantum)
    (tableFrame base noQuantum) (originalInputAfterTables base noQuantum basePoint)
    (originalInputAfterTables base noQuantum targetPoint)

/-- The actual retained public points satisfy the sampler's internal preparation contract. -/
lemma public_retainedInputs_internal_preparation (I : DomainParameters.PublicKeyInstance)
    {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).InternalPreparation environment
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib
        I.publicKey.toMathlib := by
  obtain ⟨baseStorage, baseSame⟩ := publicBaseRef_storage I
  obtain ⟨targetStorage, targetSame⟩ := publicTargetRef_storage I
  obtain ⟨retainedBase, retainedBaseSame⟩ :=
    originalInputAfterTables_storage (publicFrame I) (publicFrame_noQuantum I) baseStorage
  obtain ⟨retainedTarget, retainedTargetSame⟩ :=
    originalInputAfterTables_storage (publicFrame I) (publicFrame_noQuantum I) targetStorage
  have baseCorrect :
      (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I)).base = .storage retainedBase := by
    rw [retainedInputs_base, baseSame]
    exact retainedBaseSame
  have targetCorrect :
      (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I)).target = .storage retainedTarget := by
    rw [retainedInputs_target, targetSame]
    exact retainedTargetSame
  exact @Sampling.Storage.Inputs.internal_preparation_of_stored_points
    _ services
    (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)) retainedBase retainedTarget baseCorrect targetCorrect
    (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib environment

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

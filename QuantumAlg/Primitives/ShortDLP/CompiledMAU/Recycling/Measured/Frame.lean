/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Context
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# The complete original parent Store below the actual measured arithmetic frame

The structural transport retains each original key and role below the sole
owned quantum allocation and all real result and vent cells. Its restriction
is a mathematical observation, without a copy, empty-cell assumption or
runtime release [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

private def measurementLiftStorage {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (dimension : ℕ+) (ref : CStorageRef ctx shape) :
    (count : Nat) → CStorageRef (MeasurementCells.context ctx dimension count) shape
  | 0 => ref
  | count + 1 =>
      (measurementLiftStorage dimension ref count).underRetained
        (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
        (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh

private lemma measurementLiftStorage_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (dimension : ℕ+) (ref : CStorageRef ctx shape) (count : Nat) :
    (measurementLiftStorage dimension ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

private lemma measurementLiftStorage_role {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (dimension : ℕ+) (ref : CStorageRef ctx shape) (count : Nat) :
    (measurementLiftStorage dimension ref count).role = ref.role := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

private lemma measurementLiftStorage_input {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (dimension : ℕ+) (ref : CStorageRef ctx shape) (count : Nat) :
    MeasurementCells.liftInput dimension (.storage ref) count =
      .storage (measurementLiftStorage dimension ref count) := by
  induction count with
  | zero => rfl
  | succ count induction => rw [MeasurementCells.liftInput, induction]; rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

include noQuantum in
private lemma parentFrameDisjoint :
    List.Disjoint (Physical.qubits width).toQuantum.identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- Every parent storage leaf retains its real identity and ownership below the complete frame. -/
def parentTransport : ClassicalWorkspace.Transport base (context base noQuantum m ell width) where
  liftStorage ref := measurementLiftStorage 2
    (ref.underOwnedLayout base.canonicalFreshKey (Physical.qubits width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (parentFrameDisjoint base noQuantum width))
    (resultBits m ell + (width - 2))
  liftStorage_key _ := measurementLiftStorage_key 2 _ _
  liftStorage_role _ := measurementLiftStorage_role 2 _ _

/-- Observe the entire original parent Store while retaining its actual typed values. -/
def parentStore (store : Store (context base noQuantum m ell width)) : Store base :=
  (parentTransport base noQuantum m ell width).restrict store

/-- Every complete parent observation is exactly a read of the same original physical cell. -/
lemma measuredParentStore_read (store : Store (context base noQuantum m ell width))
    {shape : CShape} (ref : CStorageRef base shape) :
    (parentStore base noQuantum m ell width store).read (.storage ref) =
      store.read (.storage ((parentTransport base noQuantum m ell width).liftStorage ref)) :=
  ((parentTransport base noQuantum m ell width).workspaceTransport_restrict_readsAs store
    (.storage ref)).symm

/-- Every real result or vent cell is separate from every original parent storage reference. -/
lemma measuredParentTransport_cell_distinct {shape : CShape} (ref : CStorageRef base shape)
    (index : Fin (resultBits m ell + (width - 2))) :
    (cells base noQuantum m ell width index).key ≠
      ((parentTransport base noQuantum m ell width).liftStorage ref).key := by
  let bankRef := ref.underOwnedLayout base.canonicalFreshKey (Physical.qubits width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (parentFrameDisjoint base noQuantum width)
  have separate := MeasurementCells.reference_not_mem_liftInput 2 (.storage bankRef)
    (resultBits m ell + (width - 2)) index
  rw [measurementLiftStorage_input] at separate
  intro same
  exact separate (List.mem_singleton.mpr same)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Assembly
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Execution

/-!
# Complete actual scalar measurement-cell initialization

Every retained numerator cell is physically allocated by the existing
interpreter and initialized by its actual store push. The exact result keeps
the entire old quantum-reference matrix and every old history value. The
record below is only the classical image of that existing retain sequence.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open MeasuredUncompute MeasurementCells

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def framedAllocationRecord (ctx frame : RuntimeCtx .quantum) (dimension : ℕ+)
    (History : Type) : (count : Nat) →
    (separate : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count) frame) →
    Store (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate)) ×
      (ClassicalOracleModel.empty.HiddenState × History) →
    Store ((MeasurementCells.context ctx dimension count).disjointUnion frame separate) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (allocateFramed (model := .quantum AlgorithmGate.model .empty)
          ctx frame dimension count separate).Path))
  | 0, _, record => (record.1, (record.2.1, (record.2.2, ())))
  | count + 1, separate, record =>
      let middle := MeasurementCells.context ctx dimension count
      let earlierSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      let earlier := framedAllocationRecord ctx frame dimension History count earlierSeparate record
      (earlier.1.pushRetained middle.canonicalFreshKey (.finite dimension)
        (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh separate),
          (earlier.2.1, (earlier.2.2.1, (earlier.2.2.2, ()))))

private theorem framedAllocation_execute (ctx frame : RuntimeCtx .quantum)
    (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count) frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate))
      Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (allocateFramed (model := .quantum AlgorithmGate.model .empty)
      ctx frame dimension count separate).execute Reference state =
      (state.reindex
        (S := Register.prod
          ((MeasurementCells.context ctx dimension count).disjointUnion frame separate).register
          Reference)
        (framedJointBasisEquiv ctx frame dimension count separate Reference)).mapClassical
          (framedAllocationRecord ctx frame dimension History count separate) := by
  induction count with
  | zero =>
      have basis : framedJointBasisEquiv ctx frame dimension 0 separate Reference =
          Equiv.refl _ := rfl
      rw [basis, ExecutionState.reindex_refl]
      change (Circuit.id (model := .quantum AlgorithmGate.model .empty)
        (ctx.disjointUnion frame separate)).execute Reference state = _
      rw [Circuit.execute_id]
      exact ExecutionState.executionState_mapClassical_congr state rfl
  | succ count induction =>
      let middle := MeasurementCells.context ctx dimension count
      let earlierSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      change (Circuit.seq
        (allocateFramed (model := .quantum AlgorithmGate.model .empty)
          ctx frame dimension count earlierSeparate)
        (.retain (model := .quantum AlgorithmGate.model .empty)
          (middle.disjointUnion frame earlierSeparate)
          middle.canonicalFreshKey (.finite dimension)
          (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
            middle.canonicalFreshKey_fresh separate))).execute Reference state = _
      rw [Circuit.execute_seq, Circuit.execute_retain, induction earlierSeparate state]
      simp only [State.mapHistory,
        ExecutionState.executionState_mapClassical_comp_instances, Function.comp_def]
      have sameBasis :
          framedJointBasisEquiv ctx frame dimension count earlierSeparate Reference =
            framedJointBasisEquiv ctx frame dimension (count + 1) separate Reference := rfl
      rw [sameBasis]
      exact ExecutionState.executionState_mapClassical_congr
        (state.reindex
          (framedJointBasisEquiv ctx frame dimension (count + 1) separate Reference))
        (by funext record; rfl)

/-- The actual retained-cell record includes all previous values and its complete unique path. -/
def scalarCellsRecord (width count : Nat) (History : Type) :
    Store ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) ×
        (ClassicalOracleModel.empty.HiddenState × History) →
      Store (withCells width count) ×
        (ClassicalOracleModel.empty.HiddenState ×
          (History × (allocateCells width count).Path)) :=
  framedAllocationRecord (InversePreparation.after width) (exponents width count) 2 History
    width (complete_disjoint width count)

/-- Actual numerator-cell allocation preserves every complete block in the original coordinates. -/
theorem allocateCells_execution (width count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ((InversePreparation.after width).disjointUnion (exponents width count)
      (auxiliary_disjoint width count)) Reference
        (ClassicalOracleModel.empty.HiddenState × History)) :
    (allocateCells width count).execute Reference state =
      (state.reindex (S := Register.prod (withCells width count).register Reference)
        (MeasurementCells.framedJointBasisEquiv (InversePreparation.after width)
          (exponents width count) 2 width (complete_disjoint width count) Reference)).mapClassical
            (scalarCellsRecord width count History) :=
  framedAllocation_execute (InversePreparation.after width) (exponents width count) 2 width
    (complete_disjoint width count) state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Store
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Actual supported public input values

Every positive prescribed input block comes from an original positive block
with exactly the original public point values. The actual quantum program
also preserves the complete borrowed classical observation on supported
records. This follows from the existing interpreter's restoration theorem;
it does not impose values on impossible stores or add an input promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- A positive actual prescribed input block comes from a positive original input block. -/
theorem initialState_supported_original (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference))
    (value : Store (before E exponentWidth))
    (positive : 0 < ((initialState E exponentWidth problem original).block value).mass) :
    ∃ source, initialStore E exponentWidth problem source = value ∧
      0 < (original.block source).mass := by
  rw [initialState, ExecutionState.reindex_block_mass] at positive
  exact (ExecutionState.mapClassical_block_mass_pos_iff original
    (initialStore E exponentWidth problem) value).mp positive

/-- Actual positive input blocks satisfy both original public point interpretations internally. -/
theorem initialState_supported_represents (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference))
    (value : Store (before E exponentWidth))
    (positive : 0 < ((initialState E exponentWidth problem original).block value).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (value.read (initialBaseRef E exponentWidth)) problem.generator.toMathlib ∧
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (value.read (initialTargetRef E exponentWidth)) problem.target.toMathlib := by
  obtain ⟨source, rfl, _positive⟩ :=
    initialState_supported_original E exponentWidth problem original value positive
  exact ⟨initialStore_base_represents E exponentWidth problem source,
    initialStore_target_represents E exponentWidth problem source⟩

private theorem indexed_noBorrowedQuantum (width : Nat) (indices : List Nat) :
    (indices.map (indexedEntry width)).flatMap RuntimeEntry.borrowedQuantumWires = [] := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simpa only [List.map_cons, List.flatMap_cons, indexedEntry,
        RuntimeEntry.borrowedQuantumWires, List.nil_append] using ih

/-- All actual supplied quantum systems are owned; the public borrowed frame is classical. -/
theorem before_noBorrowedQuantum : (before E exponentWidth).borrowedQuantumWires = [] := by
  change (((MAU.Inversion.SharedEEA.InversePreparation.before p.size).entries ++
    (List.range (2 * exponentWidth)).map (indexedEntry p.size)) ++
    (frame E exponentWidth).entries).flatMap RuntimeEntry.borrowedQuantumWires = []
  rw [List.flatMap_append, List.flatMap_append, indexed_noBorrowedQuantum]
  rfl

private theorem run_supported_initial {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    {shape : CShape} (run : AlgorithmRun model pre post shape)
    (noBorrowed : pre.borrowedQuantumWires = []) (Reference : Register)
    (initial : ExecutionState (Store pre × model.HiddenState)
      (Register.prod pre.register Reference))
    (record : run.Record)
    (positive : 0 < ((run.execute Reference initial).block record).mass) :
    ∃ value, 0 < (initial.block value).mass ∧ value.1.readBorrowedClassical =
      run.code.borrowedClassicalValueTransport record.1.readBorrowedClassical := by
  let recorded := initial.mapClassical (fun value => (value.1, (value.2, value.1)))
  have restored := run.code.borrowedRestored_of_noBorrowedQuantum noBorrowed Reference recorded
  obtain ⟨previous, previousPositive, same⟩ := run.code.borrowedRestored_supported_initial
    Reference recorded _ restored record positive
  obtain ⟨value, rfl, valuePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff initial
      (fun value => (value.1, (value.2, value.1))) previous).mp (by
        apply lt_of_lt_of_eq previousPositive
        simp only [recorded, ExecutionState.mapClassical_block_mass])
  exact ⟨value, valuePositive, same⟩

/-- Attach the uniquely empty classical service state to the prescribed public input. -/
def initialRunState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference) :
    ExecutionState (Store (before E exponentWidth) × Unit)
      (Register.prod (before E exponentWidth).register Reference) :=
  (initialInput E exponentWidth problem original).state.mapClassical
    (fun store => (store, ()))

variable [Fact p.Prime]

/-- Execute the original run on the prescribed input with its empty service state. -/
def initialRunExecution (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :=
  (exponentRun E fieldTail odd problem points).execute Reference
    (initialRunState E (orderWidth problem) problem original)

attribute [local irreducible] exponentRun

set_option maxHeartbeats 500000 in
-- The dependent record type of the complete exponent run exceeds the default elaboration budget.
/-- Every supported actual final borrowed value comes from a prescribed positive input block. -/
theorem exponentRun_supported_borrowed (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (record : (exponentRun E fieldTail odd problem points).Record)
    (positive : 0 < ((initialRunExecution E fieldTail odd problem points original).block
      record).mass) :
    ∃ source, 0 < (original.state.block source).mass ∧
      (initialStore E (orderWidth problem) problem source).readBorrowedClassical =
        (exponentRun E fieldTail odd problem points).code.borrowedClassicalValueTransport
          record.1.readBorrowedClassical := by
  obtain ⟨entry, entryPositive, same⟩ := run_supported_initial
    (exponentRun E fieldTail odd problem points)
    (before_noBorrowedQuantum E (orderWidth problem)) Reference
    (initialRunState E (orderWidth problem) problem original) record positive
  obtain ⟨value, rfl, valuePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff
      (initialInput E (orderWidth problem) problem original).state
      (fun store => (store, ())) entry).mp (by
        apply lt_of_lt_of_eq entryPositive
        simp only [initialRunState, ExecutionState.mapClassical_block_mass])
  obtain ⟨source, constructed, sourcePositive⟩ :=
    initialState_supported_original E (orderWidth problem) problem original.state
      value valuePositive
  exact ⟨source, sourcePositive, (congrArg Store.readBorrowedClassical constructed).trans same⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

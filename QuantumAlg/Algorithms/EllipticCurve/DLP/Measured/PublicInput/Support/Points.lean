/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support
import all QuantumAlg.Core.Execution.Borrowed.Classical.Read

/-!
# Original public points in actual supported terminal records

The complete borrowed observation of the measured execution retains both
original point values. The quantum input and its real allocations contain
no borrowed classical cell, so the actual right-store projection reads
exactly the public frame. Every positive terminal block therefore carries
the prescribed original points, including their identity encodings, without
an additional public-input support condition or an intermediate input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem indexed_noBorrowedClassical (width : Nat) (indices : List Nat) :
    (indices.map (indexedEntry width)).flatMap RuntimeEntry.borrowedClassicalCells = [] := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simpa only [List.map_cons, List.flatMap_cons, indexedEntry,
        RuntimeEntry.borrowedClassicalCells, List.nil_append] using ih

private theorem original_before_noBorrowedClassical :
    (Allocation.before p.size (2 * exponentWidth)).borrowedClassicalCells = [] := by
  change ((MAU.Inversion.SharedEEA.InversePreparation.before p.size).entries ++
    (List.range (2 * exponentWidth)).map (indexedEntry p.size)).flatMap
      RuntimeEntry.borrowedClassicalCells = []
  rw [List.flatMap_append, indexed_noBorrowedClassical]
  rfl

private theorem original_terminal_noBorrowedClassical :
    (exponentMeasurementContext p exponentWidth).borrowedClassicalCells = [] :=
  (MeasurementCells.allocate (Allocation.after p.size (2 * exponentWidth))
    2 (2 * exponentWidth)).borrowedClassicalCells_preserved.trans
      ((Allocation.initializeWork p (2 * exponentWidth)).borrowedClassicalCells_preserved.trans
        (original_before_noBorrowedClassical (p := p) exponentWidth))

private theorem frame_store_eq_of_borrowed_eq (first second : Store (frame E exponentWidth))
    (same : first.readBorrowedClassical = second.readBorrowedClassical) : first = second := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  obtain ⟨firstTarget, firstBase, firstUnit⟩ := first
  obtain ⟨secondTarget, secondBase, secondUnit⟩ := second
  cases firstUnit
  cases secondUnit
  change CShape.Value.product firstTarget (.product firstBase .unit) =
    CShape.Value.product secondTarget (.product secondBase .unit) at same
  cases same
  rfl

private theorem borrowed_transport_heq {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (value : post.borrowedClassicalShape.Value) :
    HEq (code.borrowedClassicalValueTransport value) value := by
  exact ((Equiv.cast_eq_iff_heq
    (congrArg CShape.Value code.borrowedClassicalShape_preserved)).mp rfl).symm

variable [Fact p.Prime]

/-- Every positive actual terminal block reads the two originally prescribed public values. -/
theorem exponentRun_supported_points (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (record : (exponentRun E fieldTail odd problem points).Record)
    (positive : 0 < (((exponentRun E fieldTail odd problem points).execute Reference
      (initialInput E (orderWidth problem) problem original).state).block record).mass) :
    record.1.read (terminalBaseRef E (orderWidth problem)) =
        Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      record.1.read (terminalTargetRef E (orderWidth problem)) =
        Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  obtain ⟨source, _sourcePositive, same⟩ :=
    exponentRun_supported_borrowed E fieldTail odd problem points original record positive
  have initialBorrowed := readBorrowedClassical_join_right
    (before_disjoint E (orderWidth problem))
    (original_before_noBorrowedClassical (p := p) (orderWidth problem))
    source (store E (orderWidth problem) problem)
  have finalBorrowed := readBorrowedClassical_split_right
    (terminal_disjoint E (orderWidth problem))
    (original_terminal_noBorrowedClassical (p := p) (orderWidth problem)) record.1
  have transported := borrowed_transport_heq
    (exponentRun E fieldTail odd problem points).code record.1.readBorrowedClassical
  have frames := initialBorrowed.symm.trans
    ((heq_of_eq same).trans (transported.trans finalBorrowed))
  have equalFrame := (frame_store_eq_of_borrowed_eq E (orderWidth problem)
    (store E (orderWidth problem) problem)
    (split (terminal_disjoint E (orderWidth problem)) record.1).2 (eq_of_heq frames)).symm
  have baseRead := contextUnion_read_join_right (terminal_disjoint E (orderWidth problem))
    (split (terminal_disjoint E (orderWidth problem)) record.1).1
    (split (terminal_disjoint E (orderWidth problem)) record.1).2
    (baseRef E (orderWidth problem))
  have targetRead := contextUnion_read_join_right (terminal_disjoint E (orderWidth problem))
    (split (terminal_disjoint E (orderWidth problem)) record.1).1
    (split (terminal_disjoint E (orderWidth problem)) record.1).2
    (targetRef E (orderWidth problem))
  have joined := join_split_store (terminal_disjoint E (orderWidth problem)) record.1
  have actualBase := congrArg (fun value : Store (terminal E (orderWidth problem)) =>
    value.read (terminalBaseRef E (orderWidth problem))) joined
  have actualTarget := congrArg (fun value : Store (terminal E (orderWidth problem)) =>
    value.read (terminalTargetRef E (orderWidth problem))) joined
  have prescribedBase := congrArg (fun value : Store (frame E (orderWidth problem)) =>
    value.read (baseRef E (orderWidth problem))) equalFrame
  have prescribedTarget := congrArg (fun value : Store (frame E (orderWidth problem)) =>
    value.read (targetRef E (orderWidth problem))) equalFrame
  exact ⟨actualBase.symm.trans (baseRead.trans
    (prescribedBase.trans (store_base E (orderWidth problem) problem))),
    actualTarget.symm.trans (targetRead.trans
      (prescribedTarget.trans (store_target E (orderWidth problem) problem)))⟩

/-- Both terminal public-point interpretations follow from actual positive execution support. -/
theorem exponentRun_supported_represents (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (record : (exponentRun E fieldTail odd problem points).Record)
    (positive : 0 < (((exponentRun E fieldTail odd problem points).execute Reference
      (initialInput E (orderWidth problem) problem original).state).block record).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (record.1.read (terminalBaseRef E (orderWidth problem))) problem.generator.toMathlib ∧
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (record.1.read (terminalTargetRef E (orderWidth problem))) problem.target.toMathlib := by
  obtain ⟨baseValue, targetValue⟩ :=
    exponentRun_supported_points E fieldTail odd problem points original record positive
  rw [baseValue, targetValue]
  exact ⟨publicPoint_represents E problem.generator, publicPoint_represents E problem.target⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Allocation

/-!
# Complete measured exponent execution with its original public inputs

The actual preparation, arithmetic allocations, measured cascade, inverse
QFT and terminal readouts compose in the existing interpreter. Exact frame
coordinates retain every public-store block, complete external reference
matrix and original execution path. These unconditional execution identities
add no admissibility, initial workspace or public-value premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP GenericPointAddition.InPlace MAU.Inversion.SharedEEA

attribute [local irreducible] storeFintype
attribute [local irreducible] Nat.size orderWidth

private theorem sequence_execute {model : ExecutionModel}
    {pre mid post framed : RuntimeCtx model.kind}
    (beforeSeparate : RuntimeCtx.StorageDisjoint pre framed)
    (middleSeparate : RuntimeCtx.StorageDisjoint mid framed)
    (afterSeparate : RuntimeCtx.StorageDisjoint post framed)
    (first : Circuit model pre mid) (second : Circuit model mid post)
    (actualFirst : Circuit model (pre.disjointUnion framed beforeSeparate)
      (mid.disjointUnion framed middleSeparate))
    (actualSecond : Circuit model (mid.disjointUnion framed middleSeparate)
      (post.disjointUnion framed afterSeparate))
    (firstPaths : first.Path → actualFirst.Path) (secondPaths : second.Path → actualSecond.Path)
    (firstNatural : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : State (pre.disjointUnion framed beforeSeparate) Reference (model.HiddenState × H)),
      splitServiceState mid framed middleSeparate (actualFirst.execute Reference state) =
        (first.execute (Register.prod framed.register Reference)
          (splitServiceState pre framed beforeSeparate state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, firstPaths record.2.2)))))
    (secondNatural : ∀ (Reference : Register) {H : Type} [Fintype H]
      (state : State (mid.disjointUnion framed middleSeparate) Reference (model.HiddenState × H)),
      splitServiceState post framed afterSeparate (actualSecond.execute Reference state) =
        (second.execute (Register.prod framed.register Reference)
          (splitServiceState mid framed middleSeparate state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2, secondPaths record.2.2)))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre.disjointUnion framed beforeSeparate)
      Reference (model.HiddenState × History)) :
    splitServiceState post framed afterSeparate
      ((actualFirst.seq actualSecond).execute Reference state) =
      ((first.seq second).execute (Register.prod framed.register Reference)
        (splitServiceState pre framed beforeSeparate state)).mapHistory
          (fun record => (record.1,
            (record.2.1.1, (record.2.1.2,
              (firstPaths record.2.2.1, secondPaths record.2.2.2))))) := by
  rw [Circuit.execute_seq]
  have splitMapped := contextUnion_splitServiceState_mapHistory post framed afterSeparate
    (actualSecond.execute Reference (actualFirst.execute Reference state))
    (fun history : (History × actualFirst.Path) × actualSecond.Path =>
      (history.1.1, (history.1.2, history.2)))
  erw [splitMapped]
  rw [secondNatural, firstNatural]
  have secondMapped := Circuit.execute_mapHistory second (Register.prod framed.register Reference)
    (first.execute (Register.prod framed.register Reference)
      (splitServiceState pre framed beforeSeparate state))
    (fun history : (Store framed × History) × first.Path =>
      (history.1.1, (history.1.2, firstPaths history.2)))
  erw [secondMapped]
  rw [Circuit.execute_seq]
  simp only [State.mapHistory_comp, Function.comp_def]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- Both charged preparations and all original retains have exactly corresponding paths. -/
def initializeWorkPathEquiv :
    (Allocation.initializeWork p (2 * exponentWidth)).Path ≃
      (initializeWork E exponentWidth).Path :=
  (Equiv.refl (Unit × Unit)).prodCongr
    ((allocateCellsPathEquiv E exponentWidth).prodCongr (Equiv.refl Unit))

/-- Complete actual initialization retains the original public store in every history block. -/
theorem initializeWork_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (before E exponentWidth) Reference (Unit × History)) :
    splitServiceState (Allocation.after p.size (2 * exponentWidth))
      (frame E exponentWidth) (after_disjoint E exponentWidth)
      ((initializeWork E exponentWidth).execute Reference state) =
      ((Allocation.initializeWork p (2 * exponentWidth)).execute
        (Register.prod (frame E exponentWidth).register Reference)
        (splitServiceState (Allocation.before p.size (2 * exponentWidth))
          (frame E exponentWidth) (before_disjoint E exponentWidth) state)).mapHistory
            (fun record => (record.1,
              (record.2.1.1, (record.2.1.2,
                initializeWorkPathEquiv E exponentWidth record.2.2)))) := by
  have later (Reference : Register) {H : Type} [Fintype H]
      (input : State (withAuxiliary E exponentWidth) Reference (Unit × H)) :=
    sequence_execute (model := .quantum AlgorithmGate.model .empty)
      (pre := (InversePreparation.after p.size).disjointUnion
        (Allocation.exponents p.size (2 * exponentWidth))
        (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
      (mid := Allocation.withCells p.size (2 * exponentWidth))
      (post := Allocation.after p.size (2 * exponentWidth)) (framed := frame E exponentWidth)
      (auxiliary_disjoint E exponentWidth) (cells_disjoint E exponentWidth)
      (after_disjoint E exponentWidth) (Allocation.allocateCells p.size (2 * exponentWidth))
      (Allocation.prepareSelector p.size (2 * exponentWidth))
      (allocateCells E exponentWidth) (prepareSelector E exponentWidth)
      (allocateCellsPathEquiv E exponentWidth) (Equiv.refl Unit)
      (fun _ {_} _ input => allocateCells_execute E exponentWidth input)
      (fun _ {_} _ input => prepareSelector_execute E exponentWidth input) input
  exact sequence_execute (model := .quantum AlgorithmGate.model .empty)
    (pre := Allocation.before p.size (2 * exponentWidth))
    (mid := (InversePreparation.after p.size).disjointUnion
      (Allocation.exponents p.size (2 * exponentWidth))
      (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
    (post := Allocation.after p.size (2 * exponentWidth)) (framed := frame E exponentWidth)
    (before_disjoint E exponentWidth) (auxiliary_disjoint E exponentWidth)
    (after_disjoint E exponentWidth) (Allocation.prepareAuxiliary p (2 * exponentWidth))
    ((Allocation.allocateCells p.size (2 * exponentWidth)).seq
      (Allocation.prepareSelector p.size (2 * exponentWidth)))
    (prepareAuxiliary E exponentWidth)
    ((allocateCells E exponentWidth).seq (prepareSelector E exponentWidth))
    (Equiv.refl (Unit × Unit))
    ((allocateCellsPathEquiv E exponentWidth).prodCongr (Equiv.refl Unit))
    (fun _ {_} _ input => prepareAuxiliary_execute E exponentWidth input) later state

variable [Fact p.Prime]

/-- Actual premeasurement paths retain all original unitary and measured branch records. -/
def preMeasurementPathEquiv (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    (Measured.preMeasurement E fieldTail odd problem points).Path ≃
      (preMeasurement E fieldTail odd problem points).Path :=
  ((frameLocalPathEquiv (beforeExponentPreparation p problem) trivial
      (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem))).prodCongr
    ((initializeWorkPathEquiv E (orderWidth problem)).prodCongr
      (frameLocalPathEquiv
        (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
          (Semantics.radixUnit p fieldTail.succ odd))
        (Encoding.placedConvertedCascade_isLocal E points _ _)
        (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))))).prodCongr
    (frameLocalPathEquiv (afterExponentReadout p problem) trivial
      (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)))

/-- The whole actual premeasurement prefix preserves all public and quantum-reference blocks. -/
theorem preMeasurement_execute (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before E (orderWidth problem)) Reference (Unit × History)) :
    splitServiceState (Allocation.after p.size (2 * orderWidth problem))
      (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))
      ((preMeasurement E fieldTail odd problem points).execute Reference state) =
      ((Measured.preMeasurement E fieldTail odd problem points).execute
        (Register.prod (frame E (orderWidth problem)).register Reference)
        (splitServiceState (Allocation.before p.size (2 * orderWidth problem))
          (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem)) state)).mapHistory
            (fun record => (record.1,
              (record.2.1.1, (record.2.1.2,
                preMeasurementPathEquiv E fieldTail odd problem points record.2.2)))) := by
  let width := orderWidth problem
  let scalar := Encoding.placedConvertedCascade E points (List.finRange (2 * width))
    (Semantics.radixUnit p fieldTail.succ odd)
  let supported := Encoding.placedConvertedCascade_isLocal E points
    (List.finRange (2 * width)) (Semantics.radixUnit p fieldTail.succ odd)
  let scalarPaths := frameLocalPathEquiv scalar supported (frame E width) (after_disjoint E width)
  have middle (Reference : Register) {H : Type} [Fintype H]
      (input : State (before E width) Reference (Unit × H)) :=
    sequence_execute (model := .quantum AlgorithmGate.model .empty)
      (pre := Allocation.before p.size (2 * width))
      (mid := Allocation.after p.size (2 * width)) (post := Allocation.after p.size (2 * width))
      (framed := frame E width) (before_disjoint E width) (after_disjoint E width)
      (after_disjoint E width) (Allocation.initializeWork p (2 * width)) scalar
      (initializeWork E width)
      (frameLocal scalar supported (frame E width) (after_disjoint E width))
      (initializeWorkPathEquiv E width) scalarPaths
      (fun _ {_} _ initial => initializeWork_execute E width initial)
      (fun _ {_} _ initial => convertedCascade_execute E fieldTail odd problem points initial) input
  have earlier (Reference : Register) {H : Type} [Fintype H]
      (input : State (before E width) Reference (Unit × H)) :=
    sequence_execute (model := .quantum AlgorithmGate.model .empty)
      (pre := Allocation.before p.size (2 * width)) (mid := Allocation.before p.size (2 * width))
      (post := Allocation.after p.size (2 * width)) (framed := frame E width)
      (before_disjoint E width) (before_disjoint E width) (after_disjoint E width)
      (beforeExponentPreparation p problem) (Encoding.convertedCircuit E points
        (List.finRange (2 * width)) (Semantics.radixUnit p fieldTail.succ odd))
      (frameLocal (beforeExponentPreparation p problem) trivial
        (frame E width) (before_disjoint E width))
      ((initializeWork E width).seq
        (frameLocal scalar supported (frame E width) (after_disjoint E width)))
      (frameLocalPathEquiv (beforeExponentPreparation p problem) trivial
        (frame E width) (before_disjoint E width))
      ((initializeWorkPathEquiv E width).prodCongr scalarPaths)
      (fun _ {_} _ initial => beforePreparation_execute E problem initial) middle input
  exact sequence_execute (model := .quantum AlgorithmGate.model .empty)
    (pre := Allocation.before p.size (2 * width))
    (mid := Allocation.after p.size (2 * width)) (post := Allocation.after p.size (2 * width))
    (framed := frame E width) (before_disjoint E width) (after_disjoint E width)
    (after_disjoint E width)
    ((beforeExponentPreparation p problem).seq (Encoding.convertedCircuit E points
      (List.finRange (2 * width)) (Semantics.radixUnit p fieldTail.succ odd)))
    (afterExponentReadout p problem)
    ((frameLocal (beforeExponentPreparation p problem) trivial
      (frame E width) (before_disjoint E width)).seq
        ((initializeWork E width).seq
          (frameLocal scalar supported (frame E width) (after_disjoint E width))))
    (frameLocal (afterExponentReadout p problem) trivial (frame E width) (after_disjoint E width))
    ((frameLocalPathEquiv (beforeExponentPreparation p problem) trivial
      (frame E width) (before_disjoint E width)).prodCongr
        ((initializeWorkPathEquiv E width).prodCongr scalarPaths))
    (frameLocalPathEquiv (afterExponentReadout p problem) trivial
      (frame E width) (after_disjoint E width))
    earlier (fun _ {_} _ initial => afterReadout_execute E problem initial) state

/-- The actual full exponent run records the same preparation, allocation and readout outcomes. -/
def exponentRunCodePathEquiv (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    (Measured.exponentRun E fieldTail odd problem points).code.Path ≃
      (exponentRun E fieldTail odd problem points).code.Path :=
  ((preMeasurementPathEquiv E fieldTail odd problem points).prodCongr
    (MeasurementCells.allocateFramedPathEquiv (model := .quantum AlgorithmGate.model .empty)
      (Allocation.after p.size (2 * orderWidth problem))
      (frame E (orderWidth problem)) 2 (2 * orderWidth problem)
      (terminal_disjoint E (orderWidth problem)))).prodCongr
    (frameLocalPathEquiv (exponentMeasurements p (orderWidth problem))
      (Circuit.measurementSequence_isLocal _) (frame E (orderWidth problem))
      (terminal_disjoint E (orderWidth problem)))

/-- The actual complete code retains the full public store and original measured execution. -/
theorem exponentRun_code_execute (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before E (orderWidth problem)) Reference (Unit × History)) :
    splitServiceState (exponentMeasurementContext p (orderWidth problem))
      (frame E (orderWidth problem)) (terminal_disjoint E (orderWidth problem))
      ((exponentRun E fieldTail odd problem points).code.execute Reference state) =
      ((Measured.exponentRun E fieldTail odd problem points).code.execute
        (Register.prod (frame E (orderWidth problem)).register Reference)
        (splitServiceState (Allocation.before p.size (2 * orderWidth problem))
          (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem)) state)).mapHistory
            (fun record => (record.1,
              (record.2.1.1, (record.2.1.2,
                exponentRunCodePathEquiv E fieldTail odd problem points record.2.2)))) := by
  let width := orderWidth problem
  let allocations := MeasurementCells.allocateFramedPathEquiv
      (model := .quantum AlgorithmGate.model .empty)
    (Allocation.after p.size (2 * width)) (frame E width) 2 (2 * width)
    (terminal_disjoint E width)
  let outcomes := frameLocalPathEquiv (exponentMeasurements p width)
    (Circuit.measurementSequence_isLocal _) (frame E width) (terminal_disjoint E width)
  have prepared (Reference : Register) {H : Type} [Fintype H]
      (input : State (before E width) Reference (Unit × H)) :=
    sequence_execute (model := .quantum AlgorithmGate.model .empty)
      (pre := Allocation.before p.size (2 * width)) (mid := Allocation.after p.size (2 * width))
      (post := exponentMeasurementContext p width) (framed := frame E width)
      (before_disjoint E width) (after_disjoint E width) (terminal_disjoint E width)
      (Measured.preMeasurement E fieldTail odd problem points)
      (exponentMeasurementAllocate p width) (preMeasurement E fieldTail odd problem points)
      (allocateTerminal E width) (preMeasurementPathEquiv E fieldTail odd problem points)
      allocations
      (fun _ {_} _ initial => preMeasurement_execute E fieldTail odd problem points initial)
      (fun _ {_} _ initial => allocateTerminal_execute E width initial) input
  exact sequence_execute (model := .quantum AlgorithmGate.model .empty)
    (pre := Allocation.before p.size (2 * width)) (mid := exponentMeasurementContext p width)
    (post := exponentMeasurementContext p width) (framed := frame E width)
    (before_disjoint E width) (terminal_disjoint E width)
    (terminal_disjoint E width)
    ((Measured.preMeasurement E fieldTail odd problem points).seq
      (exponentMeasurementAllocate p width))
    (exponentMeasurements p width)
    ((preMeasurement E fieldTail odd problem points).seq (allocateTerminal E width))
    (measurements E width)
    ((preMeasurementPathEquiv E fieldTail odd problem points).prodCongr allocations) outcomes
    prepared (fun _ {_} _ initial => measurements_execute E width initial) state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

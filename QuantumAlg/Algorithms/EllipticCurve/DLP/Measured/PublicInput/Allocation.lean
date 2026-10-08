/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.State
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Association

/-!
# Original retained allocations with both public inputs resident

The original terminal and arithmetic result cells keep their keys, initial
encodings and literal retain instructions. Context equalities only associate
the already resident exponent and public-input entry lists. Actual recursive
execution records retain every original Unit-valued allocation step.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open MAU.Inversion.SharedEEA

variable {model : ExecutionModel}

attribute [local irreducible] storeFintype

private def pathTransportInput {pre next post : RuntimeCtx model.kind}
    (same : pre = next) (code : Circuit model next post) :
    code.Path ≃ (Eq.mpr (congrArg (fun ctx => Circuit model ctx post) same) code).Path := by
  cases same
  exact Equiv.refl _

private def pathTransportOutput {pre post next : RuntimeCtx model.kind}
    (same : post = next) (code : Circuit model pre next) :
    code.Path ≃ (Eq.mpr (congrArg (fun ctx => Circuit model pre ctx) same) code).Path := by
  cases same
  exact Equiv.refl _

private theorem inputCast_heq {pre next post : RuntimeCtx model.kind}
    (same : pre = next) (code : Circuit model next post) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit model ctx post) same) code) code := by
  cases same
  rfl

private theorem outputCast_heq {pre post next : RuntimeCtx model.kind}
    (same : post = next) (code : Circuit model pre next) :
    HEq (Eq.mpr (congrArg (fun ctx => Circuit model pre ctx) same) code) code := by
  cases same
  rfl


variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

/-- Reassociating the actual resident frames retains the original arithmetic allocation path. -/
def allocateCellsPathEquiv :
    (Allocation.allocateCells p.size (2 * exponentWidth)).Path ≃
      (allocateCells E exponentWidth).Path := by
  let expandedFrame := (Allocation.exponents p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (exponents_disjoint E exponentWidth)
  let complete := union_right_separate
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (numerator_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)
  let original := MeasurementCells.original_disjoint (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have first := union_assoc (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (auxiliary_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) original
  have last := union_assoc (NumeratorMeasurement.context p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
  let originalPaths := MeasurementCells.allocateFramedPathEquiv
    (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after p.size) (Allocation.exponents p.size (2 * exponentWidth))
    2 p.size (Allocation.complete_disjoint p.size (2 * exponentWidth))
  let expanded := MeasurementCells.allocateFramed (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  let expandedPaths := MeasurementCells.allocateFramedPathEquiv
    (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after p.size) expandedFrame 2 p.size complete
  exact ((originalPaths.symm.trans expandedPaths).trans
    (pathTransportOutput (model := .quantum AlgorithmGate.model .empty) last expanded)).trans
    (pathTransportInput (model := .quantum AlgorithmGate.model .empty) first _)

/-- The actual original arithmetic retains preserve the full public store and reference state. -/
theorem allocateCells_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (withAuxiliary E exponentWidth) Reference (Unit × History)) :
    splitServiceState (Allocation.withCells p.size (2 * exponentWidth))
      (frame E exponentWidth) (cells_disjoint E exponentWidth)
      ((allocateCells E exponentWidth).execute Reference state) =
      ((Allocation.allocateCells p.size (2 * exponentWidth)).execute
        (Register.prod (frame E exponentWidth).register Reference)
        (splitServiceState
          ((InversePreparation.after p.size).disjointUnion
            (Allocation.exponents p.size (2 * exponentWidth))
            (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
          (frame E exponentWidth) (auxiliary_disjoint E exponentWidth) state)).mapHistory
            (fun record => (record.1,
              (record.2.1.1, (record.2.1.2,
                allocateCellsPathEquiv E exponentWidth record.2.2)))) := by
  let expandedFrame := (Allocation.exponents p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (exponents_disjoint E exponentWidth)
  let complete := union_right_separate
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (numerator_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)
  let original := MeasurementCells.original_disjoint (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have first := union_assoc (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (auxiliary_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) original
  have last := union_assoc (NumeratorMeasurement.context p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth)
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
  let expanded := MeasurementCells.allocateFramed (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after p.size)
    expandedFrame 2 p.size complete
  have same : HEq (allocateCells E exponentWidth) expanded :=
    (inputCast_heq (model := .quantum AlgorithmGate.model .empty) first _).trans
      (outputCast_heq (model := .quantum AlgorithmGate.model .empty) last expanded)
  exact MeasurementCells.allocateFramed_associated_execute
    (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after p.size)
    (Allocation.exponents p.size (2 * exponentWidth)) (frame E exponentWidth) 2 p.size
    (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth) (exponents_disjoint E exponentWidth) complete
    (auxiliary_disjoint E exponentWidth) (allocateCells E exponentWidth) same
    (allocateCellsPathEquiv E exponentWidth) Reference state

/-- Terminal cell allocation preserves all public blocks, quantum-reference entries and paths. -/
theorem allocateTerminal_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (after E exponentWidth) Reference (Unit × History)) :
    splitServiceState (exponentMeasurementContext p exponentWidth)
      (frame E exponentWidth) (terminal_disjoint E exponentWidth)
      ((allocateTerminal E exponentWidth).execute Reference state) =
      ((exponentMeasurementAllocate p exponentWidth).execute
        (Register.prod (frame E exponentWidth).register Reference)
        (splitServiceState (Allocation.after p.size (2 * exponentWidth))
          (frame E exponentWidth) (after_disjoint E exponentWidth) state)).mapHistory
            (fun record => (record.1, (record.2.1.1, (record.2.1.2,
              MeasurementCells.allocateFramedPathEquiv
    (model := .quantum AlgorithmGate.model .empty)
                (Allocation.after p.size (2 * exponentWidth)) (frame E exponentWidth)
                2 (2 * exponentWidth) (terminal_disjoint E exponentWidth) record.2.2)))) :=
  MeasurementCells.allocateFramed_execute (model := .quantum AlgorithmGate.model .empty)
    (Allocation.after p.size (2 * exponentWidth))
    (frame E exponentWidth) 2 (2 * exponentWidth) (terminal_disjoint E exponentWidth) state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

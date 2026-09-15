/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run
import all QuantumAlg.Core.Execution.Local.MeasurementSequence
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual measured exponent execution with public inputs present from the start

The two original borrowed public points accompany every actual stage. The
original auxiliary preparation, retained arithmetic cells and selector
preparation use their original keys and wires. Allocation-free original
quantum fragments use the existing actual local framing construction.

The retained-cell stage only reassociates equal appended context entries to
reuse the original allocator with the larger resident frame. This is a type
equality, not an extra instruction or replacement interpreter. Both public
inputs remain listed in the complete output and charged as resident inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open MAU.Inversion.SharedEEA FiniteCyclicDLP GenericPointAddition.InPlace

private theorem union_separation {left right framed : RuntimeCtx .quantum}
    (original : RuntimeCtx.StorageDisjoint left right)
    (separate : RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed) :
    RuntimeCtx.StorageDisjoint left framed ∧ RuntimeCtx.StorageDisjoint right framed := by
  have keys := (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp separate.1
  have wires := (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp separate.2
  rw [RuntimeCtx.keys_disjointUnion] at keys
  rw [RuntimeCtx.physicalIdx_disjointUnion] at wires
  have keyParts := List.disjoint_append_left.mp keys
  have wireParts := List.disjoint_append_left.mp wires
  exact ⟨⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr keyParts.1,
    (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr wireParts.1⟩,
    ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr keyParts.2,
    (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr wireParts.2⟩⟩

private theorem union_separate {left right framed : RuntimeCtx .quantum}
    (original : RuntimeCtx.StorageDisjoint left right)
    (first : RuntimeCtx.StorageDisjoint left framed)
    (second : RuntimeCtx.StorageDisjoint right framed) :
    RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.keys_disjointUnion]
    exact List.disjoint_append_left.mpr
      ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp first.1,
        (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp second.1⟩
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.physicalIdx_disjointUnion]
    exact List.disjoint_append_left.mpr
      ⟨(RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp first.2,
        (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp second.2⟩

private theorem union_right_separate {left right framed : RuntimeCtx .quantum}
    (original : RuntimeCtx.StorageDisjoint left right)
    (first : RuntimeCtx.StorageDisjoint left framed)
    (second : RuntimeCtx.StorageDisjoint right framed) :
    RuntimeCtx.StorageDisjoint left (right.disjointUnion framed second) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.keys_disjointUnion]
    exact List.disjoint_append_right.mpr
      ⟨(RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp original.1,
        (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mp first.1⟩
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    rw [RuntimeCtx.physicalIdx_disjointUnion]
    exact List.disjoint_append_right.mpr
      ⟨(RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp original.2,
        (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mp first.2⟩

private theorem context_eq (first second : RuntimeCtx .quantum)
    (entries : first.entries = second.entries) : first = second := by
  cases first
  cases second
  cases entries
  rfl

private theorem union_assoc (left right framed : RuntimeCtx .quantum)
    (original : RuntimeCtx.StorageDisjoint left right)
    (outside : RuntimeCtx.StorageDisjoint (left.disjointUnion right original) framed)
    (rightOutside : RuntimeCtx.StorageDisjoint right framed)
    (combined : RuntimeCtx.StorageDisjoint left (right.disjointUnion framed rightOutside)) :
    (left.disjointUnion right original).disjointUnion framed outside =
      left.disjointUnion (right.disjointUnion framed rightOutside) combined :=
  context_eq _ _ (List.append_assoc _ _ _)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem after_disjoint :
    RuntimeCtx.StorageDisjoint (Allocation.after p.size (2 * exponentWidth))
      (frame E exponentWidth) :=
  MeasurementCells.original_disjoint _ _ 2 (2 * exponentWidth)
    (terminal_disjoint E exponentWidth)

private theorem cells_disjoint :
    RuntimeCtx.StorageDisjoint (Allocation.withCells p.size (2 * exponentWidth))
      (frame E exponentWidth) :=
  preparation_original_disjoint (indexedKey p.size (2 * exponentWidth))
    (indexedLayout p.size (2 * exponentWidth))
    (Allocation.selector_fresh p.size (2 * exponentWidth))
    (Allocation.selector_disjoint p.size (2 * exponentWidth)) (after_disjoint E exponentWidth)

private theorem numerator_disjoint :
    RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context p.size) (frame E exponentWidth) :=
  (union_separation (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth)).1

private theorem exponents_disjoint :
    RuntimeCtx.StorageDisjoint (Allocation.exponents p.size (2 * exponentWidth))
      (frame E exponentWidth) :=
  (union_separation (Allocation.complete_disjoint p.size (2 * exponentWidth))
    (cells_disjoint E exponentWidth)).2

private theorem inverse_disjoint :
    RuntimeCtx.StorageDisjoint (InversePreparation.after p.size) (frame E exponentWidth) :=
  MeasurementCells.original_disjoint _ _ 2 p.size (numerator_disjoint E exponentWidth)

private theorem coordinates_disjoint :
    RuntimeCtx.StorageDisjoint (InversePreparation.before p.size) (frame E exponentWidth) :=
  preparation_original_disjoint InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout p.size) (InversePreparation.auxiliary_fresh p.size)
    (InversePreparation.auxiliary_disjoint p.size) (inverse_disjoint E exponentWidth)

private theorem auxiliary_disjoint :
    RuntimeCtx.StorageDisjoint
      ((InversePreparation.after p.size).disjointUnion
        (Allocation.exponents p.size (2 * exponentWidth))
        (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))) (frame E exponentWidth) :=
  union_separate (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))
    (inverse_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)

private theorem before_disjoint :
    RuntimeCtx.StorageDisjoint (Allocation.before p.size (2 * exponentWidth))
      (frame E exponentWidth) :=
  union_separate (Allocation.input_disjoint p.size (2 * exponentWidth))
    (coordinates_disjoint E exponentWidth) (exponents_disjoint E exponentWidth)

/-- Public inputs and the original supplied quantum systems are all present initially. -/
def before : RuntimeCtx .quantum :=
  (Allocation.before p.size (2 * exponentWidth)).disjointUnion (frame E exponentWidth)
    (before_disjoint E exponentWidth)

private def withAuxiliary : RuntimeCtx .quantum :=
  ((InversePreparation.after p.size).disjointUnion
    (Allocation.exponents p.size (2 * exponentWidth))
    (Allocation.auxiliary_disjoint p.size (2 * exponentWidth))).disjointUnion
      (frame E exponentWidth) (auxiliary_disjoint E exponentWidth)

private def withCells : RuntimeCtx .quantum :=
  (Allocation.withCells p.size (2 * exponentWidth)).disjointUnion
    (frame E exponentWidth) (cells_disjoint E exponentWidth)

/-- Every original allocated scalar entry remains beside both original public inputs. -/
def after : RuntimeCtx .quantum :=
  (Allocation.after p.size (2 * exponentWidth)).disjointUnion (frame E exponentWidth)
    (after_disjoint E exponentWidth)

/-- Every terminal finite result cell remains beside the original quantum entries and inputs. -/
def terminal : RuntimeCtx .quantum :=
  (exponentMeasurementContext p exponentWidth).disjointUnion (frame E exponentWidth)
    (terminal_disjoint E exponentWidth)

/-- The original charged arithmetic preparation executes with both public inputs resident. -/
def prepareAuxiliary : Circuit (before E exponentWidth) (withAuxiliary E exponentWidth) :=
  prepareFramed InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout p.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh p.size) (InversePreparation.auxiliary_disjoint p.size)
      (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
    (preparation_wires_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh p.size) (InversePreparation.auxiliary_disjoint p.size)
      (Allocation.auxiliary_disjoint p.size (2 * exponentWidth)))
    (auxiliary_disjoint E exponentWidth) (InPlacePreparation.preparation p)

/-- The original arithmetic result cells are allocated with their unchanged original keys. -/
def allocateCells : Circuit (withAuxiliary E exponentWidth) (withCells E exponentWidth) := by
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
  unfold withAuxiliary withCells
  rw [first, last]
  exact MeasurementCells.allocateFramed (InversePreparation.after p.size)
    expandedFrame 2 p.size complete

/-- The original single zero selector is prepared without moving any original exponent wire. -/
def prepareSelector : Circuit (withCells E exponentWidth) (after E exponentWidth) :=
  prepareFramed (indexedKey p.size (2 * exponentWidth))
    (indexedLayout p.size (2 * exponentWidth))
    (Allocation.selector_fresh p.size (2 * exponentWidth))
    (Allocation.selector_disjoint p.size (2 * exponentWidth)) (after_disjoint E exponentWidth)
    (BasisPreparation.zero (indexedLayout p.size (2 * exponentWidth)))

/-- The same original three actual initialization stages retain both public point inputs. -/
def initializeWork : Circuit (before E exponentWidth) (after E exponentWidth) :=
  (prepareAuxiliary E exponentWidth).seq
    ((allocateCells E exponentWidth).seq (prepareSelector E exponentWidth))

/-- The original terminal allocator retains exactly one result cell per original exponent wire. -/
def allocateTerminal : Circuit (after E exponentWidth) (terminal E exponentWidth) :=
  MeasurementCells.allocateFramed (Allocation.after p.size (2 * exponentWidth))
    (frame E exponentWidth) 2 (2 * exponentWidth) (terminal_disjoint E exponentWidth)

variable [Fact p.Prime]

/-- Original exponent gates and the actual converted cascade execute beside the resident inputs. -/
def preMeasurement (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    Circuit (before E (orderWidth problem)) (after E (orderWidth problem)) :=
  ((frameLocal (beforeExponentPreparation p problem) trivial
      (frame E (orderWidth problem)) (before_disjoint E (orderWidth problem))).seq
    ((initializeWork E (orderWidth problem)).seq
      (frameLocal (Encoding.placedConvertedCascade E points
        (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd))
        (Encoding.placedConvertedCascade_isLocal E points _ _)
        (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem))))).seq
    (frameLocal (afterExponentReadout p problem) trivial
      (frame E (orderWidth problem)) (after_disjoint E (orderWidth problem)))

/-- Actual terminal measurements read the same original physical exponent wires. -/
def measurements : Circuit (terminal E exponentWidth) (terminal E exponentWidth) :=
  frameLocal (exponentMeasurements p exponentWidth) (Circuit.measurementSequence_isLocal _)
    (frame E exponentWidth) (terminal_disjoint E exponentWidth)

/-- The public inputs exist before exponent preparation and survive the complete measured run. -/
def exponentRun (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) :
    AlgorithmRun (before E (orderWidth problem)) (terminal E (orderWidth problem))
      (.fixedVector (2 * orderWidth problem) (.finite 2)) where
  code := ((preMeasurement E fieldTail odd problem points).seq
    (allocateTerminal E (orderWidth problem))).seq (measurements E (orderWidth problem))
  output := Output.all (terminal E (orderWidth problem)) (.read
    (inputLeft (terminal_disjoint E (orderWidth problem))
      (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))

/-- The final base reference still denotes the original initially borrowed input. -/
def terminalBaseRef : CInputRef (terminal E exponentWidth)
    (Canonical.Runtime.Context.PointShape E) :=
  inputRight (terminal_disjoint E exponentWidth) (baseRef E exponentWidth)

/-- The final target reference still denotes the original initially borrowed input. -/
def terminalTargetRef : CInputRef (terminal E exponentWidth)
    (Canonical.Runtime.Context.PointShape E) :=
  inputRight (terminal_disjoint E exponentWidth) (targetRef E exponentWidth)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

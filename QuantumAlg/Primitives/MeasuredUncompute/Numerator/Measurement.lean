/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Assembly
import all QuantumAlg.Core.Execution.Preparation.Borrowed.Positions
import all QuantumAlg.Core.Execution.QubitReadouts

/-!
# Actual numerator measurements in the original two-input runtime layout

The supplied numerator keeps its original physical identities after the
shared EEA auxiliaries are prepared. Exactly n finite result cells are
retained, and each existing numerator wire is Z measured into its own cell.
Their indexed order is little endian, as required by the later literal
phase-correction word. No new quantum system, packed classical word, or
input-dependent preparation is introduced
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorMeasurement

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- Keep the actual two inputs and complete shared EEA frame, retaining n finite results. -/
def context (width : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (InversePreparation.after width) 2 width

private def sourcePosition (width : Nat) (index : Fin width) : Fin (width + width) :=
  ⟨width + index.rev.val, by have bound := index.rev.isLt; omega⟩

private def suppliedWire (width : Nat) (index : Fin width) :
    Fin (InversePreparation.before width).systemCount :=
  positionsOfEqualWires (InversePreparation.inputLayout width)
    (InversePreparation.before width).quantumLayout (InversePreparation.input_wires width)
      (sourcePosition width index)

private theorem suppliedWire_record (width : Nat) (index : Fin width) :
    (InversePreparation.before width).quantumLayout.wire (suppliedWire width index) =
      ({ identity := (encoding width).width + index.rev.val, dimension := 2 } : QuantumWire) := by
  have actual := wireAtCorrespondingPosition (InversePreparation.inputLayout width)
    (InversePreparation.before width).quantumLayout (InversePreparation.input_wires width)
      (sourcePosition width index)
  apply actual.trans
  change QuantumWire.mk (InversePreparation.physicalIndex width (width + index.rev.val)) 2 = _
  have outside : ¬ width + index.rev.val < width := by omega
  simp only [InversePreparation.physicalIndex, if_neg outside, Nat.add_sub_cancel_left]

/-- The supplied numerator position survives the actual auxiliary preparation. -/
def preparedWire (width : Nat) (index : Fin width) :
    Fin (InversePreparation.after width).systemCount :=
  PreparationBorrowed.fullPositionEquiv (InversePreparation.before width)
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout width)
      (InversePreparation.auxiliary_fresh width) (InversePreparation.auxiliary_disjoint width)
        (.inr (suppliedWire width index))

theorem preparedWire_record (width : Nat) (index : Fin width) :
    (InversePreparation.after width).quantumLayout.wire (preparedWire width index) =
      ({ identity := (encoding width).width + index.rev.val, dimension := 2 } : QuantumWire) :=
  (PreparationBorrowed.fullPositionEquiv_old_wire (InversePreparation.before width)
    InversePreparation.auxiliaryKey (InputPreparation.auxiliaryLayout width)
      (InversePreparation.auxiliary_fresh width) (InversePreparation.auxiliary_disjoint width)
        (suppliedWire width index)).trans (suppliedWire_record width index)

/-- Classical result allocation leaves the same numerator position and physical wire live. -/
def wire (width : Nat) (index : Fin width) : Fin (context width).systemCount :=
  MeasurementCells.wireEquiv (InversePreparation.after width) 2 width (preparedWire width index)

/-- The measured position is the literal original numerator wire, never an EEA history bit. -/
theorem wire_record (width : Nat) (index : Fin width) :
    (context width).quantumLayout.wire (wire width index) =
      ({ identity := (encoding width).width + index.rev.val, dimension := 2 } : QuantumWire) :=
  (MeasurementCells.wireEquiv_preserved (InversePreparation.after width) 2 width
    (preparedWire width index)).trans (preparedWire_record width index)

theorem wire_dimension (width : Nat) (index : Fin width) :
    ((context width).quantumLayout.wire (wire width index)).dimension = 2 :=
  congrArg QuantumWire.dimension (wire_record width index)

/-- The ith finite storage location is an actual retained cell in the runtime context. -/
def cell (width : Nat) (index : Fin width) : CWriteRef (context width) (.finite 2) :=
  MeasurementCells.reference (InversePreparation.after width) 2 width index

/-- The actual ordered Z instructions each write one distinct result cell. -/
def readouts (width : Nat) : List (ZReadout (context width)) :=
  QubitReadouts.readouts (wire width) (wire_dimension width) (cell width)

/-- The result vector reads only the actual finite locations written by those Z instructions. -/
def input (width : Nat) : CInputRef (context width) (.fixedVector width (.finite 2)) :=
  QubitReadouts.input (cell width)

/-- Allocation is the existing sequence of retained finite cells on the same quantum frame. -/
def allocate (width : Nat) : Circuit (InversePreparation.after width) (context width) :=
  MeasurementCells.allocate (InversePreparation.after width) 2 width

/-- Z measurement itself has no terminal variant and releases no live resource. -/
def measure (width : Nat) : Circuit (context width) (context width) :=
  Circuit.measurementSequence (readouts width)

theorem cells_distinct (width : Nat) :
    Function.Injective fun index : Fin width => (cell width index).key :=
  MeasurementCells.reference_key_injective (InversePreparation.after width) 2 width

/-- Direct correction selection uses precisely the values that the actual measurements wrote. -/
theorem stored_mask (width : Nat) (store : Store (context width))
    (basis : (context width).register.Index) (index : Fin width) :
    QubitReadouts.mask ((Circuit.writeMeasurementPath (readouts width) store
      (Circuit.measurementBasisPath (readouts width) basis)).read (input width)) index =
        decide ((basis (wire width index)).val = 1) :=
  QubitReadouts.written_mask (wire width) (wire_dimension width) (cell width)
    (cells_distinct width) store basis index

/-- The classical cells add no quantum wire or physical identity. -/
theorem context_physical (width : Nat) :
    (context width).physicalIdx = (InversePreparation.after width).physicalIdx :=
  MeasurementCells.context_physicalIdx (InversePreparation.after width) 2 width

/-- Every requested numerator bit contributes one actual Z event. -/
theorem measurement_resources (width : Nat) (path : (measure width).Path) :
    (measure width).resourcePool path = width • ResourcePool.singleton (Circuit.zEvent 2) :=
  QubitReadouts.measurement_resources (wire width) (wire_dimension width) (cell width) path

/-- Real retained result storage is included beside all existing inputs and EEA auxiliaries. -/
theorem context_space (width : Nat) :
    (context width).residentSpace = width • SpacePool.ofShape (.finite 2) +
      (InversePreparation.after width).residentSpace :=
  MeasurementCells.context_residentSpace (InversePreparation.after width) 2 width

end

end QuantumAlg.MeasuredUncompute.NumeratorMeasurement

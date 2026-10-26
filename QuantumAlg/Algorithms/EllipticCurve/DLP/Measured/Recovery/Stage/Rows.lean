/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Values
import all QuantumAlg.Core.Execution.Context.Embedding.Union
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Layout
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Placement
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.SingleQubit.Support
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Core.Measure.Reset
import all Mathlib.Data.Matrix.PEquiv
import all Mathlib.Data.Matrix.Mul

/-!
# Actual common coordinates and preparation, feedback and reset rows

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

lemma streamingPointPlacement_frame (width : Nat) :
    (indexedPointPlacement width (0 : Fin 2)).frame.entries = [indexedEntry width 1] := by
  change (((List.range 2).erase 0).map (indexedEntry width)) = [indexedEntry width 1]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
namespace Placement

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

def selected (width m : Nat) (basis : (terminal width m).quantumLayout.Basis) : Fin 4 :=
  QuantumSignature.qubitsIndexEquiv 2
    (UnitaryCircuit.selectedInput Recovery.Point.Program.layout (terminal width m).quantumLayout
      (preparationWires width m) (preparation_dimensions width m) basis)

def complement (width m : Nat) (basis : (terminal width m).quantumLayout.Basis) :=
  (terminal width m).quantumLayout.restrictComplementBasis
    (Finset.univ.map (preparationWires width m)) basis

lemma selected_physical_value (width m : Nat)
    (basis : (terminal width m).quantumLayout.Basis) (index : Fin 2) :
    ((QuantumSignature.qubitsIndexEquiv 2).symm (selected width m basis) index).val =
      (basis (position width m index.castSucc)).val := by
  simp only [selected, Equiv.symm_apply_apply]
  rfl

lemma preparation_entry (width m r remaining : Nat)
    (row column : (terminal width m).quantumLayout.Basis) :
    ((preparation width m r remaining).matrix environment.quantum) row column =
      ((Recovery.Point.Program.step r remaining).binaryMatrix environment.quantum)
        (selected width m row) (selected width m column) *
          (if complement width m row = complement width m column then 1 else 0) := by
  rw [preparation, UnitaryCircuit.placeAt_matrix, UnitaryCircuit.operatorAt_entry]
  simp only [selected, complement, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  apply congrArg (fun weight : ℂ =>
    ((Recovery.Point.Program.step r remaining).matrix environment.quantum)
      (UnitaryCircuit.selectedInput Recovery.Point.Program.layout (terminal width m).quantumLayout
        (preparationWires width m) (preparation_dimensions width m) row)
      (UnitaryCircuit.selectedInput Recovery.Point.Program.layout (terminal width m).quantumLayout
        (preparationWires width m) (preparation_dimensions width m) column) * weight)
  by_cases same :
      (terminal width m).quantumLayout.restrictComplementBasis
          (Finset.univ.map (preparationWires width m)) row =
        (terminal width m).quantumLayout.restrictComplementBasis
          (Finset.univ.map (preparationWires width m)) column
  · simp only [if_pos same]
    exact (if_pos same).symm
  · simp only [if_neg same]
    exact (if_neg same).symm

lemma preparation_columns (width m r remaining : Nat) (input emitted memory : Bool)
    (row column : (terminal width m).quantumLayout.Basis)
    (rowSelected : selected width m row = Recovery.Point.Extension.index emitted memory)
    (columnSelected : selected width m column = Recovery.Point.Extension.index false input) :
    ((preparation width m r remaining).matrix environment.quantum) row column =
      (table (2 ^ remaining) (r % (2 * 2 ^ remaining)) input emitted memory : ℂ) *
        (if complement width m row = complement width m column then 1 else 0) := by
  rw [preparation_entry, rowSelected, columnSelected, Recovery.Point.Program.step_columns]

end

end Placement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

private abbrev Inner (width : Nat) := Recovery.Point.indexedPointPlacement width (0 : Fin 2)

private abbrev Outer (width m : Nat) :=
  Recovery.Point.cellsPlacement (readyContext width 2) 2 (2 * m)

abbrev Memory (width : Nat) := (Inner width).frame.register

abbrev ResidualReference (width m : Nat) (Reference : Register) :=
  (Outer width m).frame.register.prod Reference

abbrev Bank (width m : Nat) (Reference : Register) :=
  Recovery.Point.Instrument.FiberBank width (ResidualReference width m Reference)

private lemma memory_wires (width : Nat) :
    (indexedLayout width 1).wires = (Inner width).frame.quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (indexedLayout width 1).wires =
    ((Inner width).frame.entries.flatMap RuntimeEntry.quantumWires)
  rw [Recovery.Point.streamingPointPlacement_frame]
  change (indexedLayout width 1).wires = (indexedLayout width 1).wires ++ []
  exact (List.append_nil _).symm

def memoryBasis (width : Nat) : (Memory width).Index ≃ Fin 2 :=
  (basisOfEqualWires (indexedLayout width 1) (Inner width).frame.quantumLayout
    (memory_wires width)).symm.trans
      { toFun := fun value => value 0
        invFun := fun bit _ => bit
        left_inv := by
          intro value
          funext index
          fin_cases index
          rfl
        right_inv := fun _ => rfl }

private def memoryPosition (width : Nat) : Fin (Inner width).frame.systemCount :=
  positionsOfEqualWires (indexedLayout width 1) (Inner width).frame.quantumLayout
    (memory_wires width) 0

private lemma memoryPosition_wire (width : Nat) :
    (Inner width).frame.quantumLayout.wire (memoryPosition width) =
      QuantumWire.mk (InPlaceControlled.frameWidth width + 1) 2 := by
  exact wireAtCorrespondingPosition (indexedLayout width 1)
    (Inner width).frame.quantumLayout (memory_wires width) 0

private lemma memoryBasis_symm_value (width : Nat) (bit : Fin 2) :
    ((memoryBasis width).symm bit (memoryPosition width)).val = bit.val := by
  exact basisOfEqualWires_value (indexedLayout width 1) (Inner width).frame.quantumLayout
    (memory_wires width) (fun _ => bit) 0

private def moveMemory (width m : Nat) (Reference : Register) :
    (Fin 2 × Recovery.Point.Instrument.FiberBank width
      ((Memory width).prod (ResidualReference width m Reference))) ≃
        Fin 2 × ((Memory width).Index × Bank width m Reference) where
  toFun value :=
    (value.1, (value.2.2.2.1, (value.2.1, (value.2.2.1, value.2.2.2.2))))
  invFun value :=
    (value.1, (value.2.2.1, (value.2.2.2.1, (value.2.1, value.2.2.2.2))))
  left_inv := by rintro ⟨bit, original, selector, memory, residual⟩; rfl
  right_inv := by rintro ⟨bit, memory, original, selector, residual⟩; rfl

def coordinates (width m : Nat) (Reference : Register) :
    ((Interface width m).register.prod Reference).Index ≃
      Fin 2 × (Fin 2 × Bank width m Reference) :=
  ((Outer width m).referenceBasis Reference).trans
    (((Inner width).referenceBasis (ResidualReference width m Reference)).trans
      ((Recovery.Point.Instrument.fiberBasis width
        ((Memory width).prod (ResidualReference width m Reference))).trans
        ((moveMemory width m Reference).trans
          ((Equiv.refl (Fin 2)).prodCongr
            ((memoryBasis width).prodCongr (Equiv.refl (Bank width m Reference)))))))

lemma coordinates_symm (width m : Nat) (Reference : Register)
    (control memory : Fin 2) (bank : Bank width m Reference) :
    (coordinates width m Reference).symm (control, (memory, bank)) =
      ((Outer width m).referenceBasis Reference).symm
        (((Inner width).referenceBasis (ResidualReference width m Reference)).symm
          (MeasuredPointAddition.label width control bank.2.1 bank.1,
            ((memoryBasis width).symm memory, bank.2.2))) := by
  change ((Outer width m).referenceBasis Reference).symm
    (((Inner width).referenceBasis (ResidualReference width m Reference)).symm
      ((Recovery.Point.Instrument.fiberBasis width
        ((Memory width).prod (ResidualReference width m Reference))).symm
          (control, (bank.1, (bank.2.1, ((memoryBasis width).symm memory, bank.2.2)))))) = _
  rw [Recovery.Point.Instrument.fiberBasis_symm]

private def pointControlPosition (width : Nat) :
    Fin (MeasuredPointAddition.context width).systemCount :=
  ContextUnion.leftPosition (InPlaceControlled.context width)
    (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
    (InPlaceControlled.nativePosition width
      (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1)))

private lemma pointControlPosition_identity (width : Nat) :
    ((MeasuredPointAddition.context width).quantumLayout.wire
      (pointControlPosition width)).identity = InPlaceControlled.controlWire width := by
  exact (congrArg QuantumWire.identity
    (ContextUnion.contextUnion_left_wire (InPlaceControlled.context width)
      (MeasuredPointAddition.selectorContext width) (MeasuredPointAddition.selector_disjoint width)
      (InPlaceControlled.nativePosition width
        (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1))))).trans
    (InPlaceControlled.nativePosition_identity width
      (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1)))

private lemma pointLabel_control_value (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    (MeasuredPointAddition.label width control selector original
      (pointControlPosition width)).val = control.val := by
  have outer := ContextUnion.contextUnion_join_left_value
    (InPlaceControlled.context width) (MeasuredPointAddition.selectorContext width)
    (MeasuredPointAddition.selector_disjoint width)
    (InPlaceControlled.label width control original)
    ((MeasuredPointAddition.selectorBasis width).symm selector)
    (InPlaceControlled.nativePosition width
      (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1)))
  have inner := InPlaceControlled.nativeBasis_label_right width control original (0 : Fin 1)
  have nativeValue : (InPlaceControlled.label width control original
      (InPlaceControlled.nativePosition width
        (Fin.natAdd (ProductPlacement.frameEncoding width).width (0 : Fin 1)))).val =
      ((QubitLayout.canonical 1).basisEquiv.symm control (0 : Fin 1)).val := by
    simpa only [InPlaceControlled.nativeBasis, UnitaryCircuit.basisAt_val] using inner
  have controlValue :
      ((QubitLayout.canonical 1).basisEquiv.symm control (0 : Fin 1)).val = control.val := by
    fin_cases control <;> rfl
  exact outer.trans (nativeValue.trans controlValue)

private lemma control_position (width m : Nat) :
    (Outer width m).position ((Inner width).position (pointControlPosition width)) =
      Recovery.Layout.position width m 0 := by
  apply (Interface width m).quantumLayout.position_eq_of_identity_eq
  have outer := congrArg QuantumWire.identity
    ((Outer width m).contextEmbedding_position_wire
      ((Inner width).position (pointControlPosition width)))
  have inner := congrArg QuantumWire.identity
    ((Inner width).contextEmbedding_position_wire (pointControlPosition width))
  change ((Interface width m).quantumLayout.wire
      ((Outer width m).position ((Inner width).position (pointControlPosition width)))).identity =
    ((readyContext width 2).quantumLayout.wire
      ((Inner width).position (pointControlPosition width))).identity at outer
  change ((readyContext width 2).quantumLayout.wire
      ((Inner width).position (pointControlPosition width))).identity =
    physicalMap width (0 : Fin 2)
      (((MeasuredPointAddition.context width).quantumLayout.wire
        (pointControlPosition width)).identity) at inner
  rw [pointControlPosition_identity, physicalMap_control] at inner
  have target := congrArg QuantumWire.identity (Recovery.Layout.position_wire width m 0)
  exact outer.trans (inner.trans target.symm)

private lemma memory_position (width m : Nat) :
    (Outer width m).position ((Inner width).positions (.inr (memoryPosition width))) =
      Recovery.Layout.position width m 1 := by
  apply (Interface width m).quantumLayout.position_eq_of_identity_eq
  have outer := congrArg QuantumWire.identity
    ((Outer width m).contextEmbedding_position_wire
      ((Inner width).positions (.inr (memoryPosition width))))
  have inner := congrArg QuantumWire.identity
    ((Inner width).contextEmbedding_frame_position_wire (memoryPosition width))
  change ((Interface width m).quantumLayout.wire
      ((Outer width m).position ((Inner width).positions (.inr (memoryPosition width))))).identity
        =
    ((readyContext width 2).quantumLayout.wire
      ((Inner width).positions (.inr (memoryPosition width)))).identity at outer
  rw [memoryPosition_wire] at inner
  have target := congrArg QuantumWire.identity (Recovery.Layout.position_wire width m 1)
  exact outer.trans (inner.trans target.symm)

lemma coordinates_control_value (width m : Nat) (Reference : Register)
    (control memory : Fin 2) (bank : Bank width m Reference) :
    (((coordinates width m Reference).symm (control, (memory, bank))).1
      (Recovery.Layout.position width m 0)).val = control.val := by
  rw [coordinates_symm, ← control_position]
  change ((Outer width m).basis.symm
    ((Inner width).basis.symm
      (MeasuredPointAddition.label width control bank.2.1 bank.1,
        (memoryBasis width).symm memory), bank.2.2.1)
      ((Outer width m).position ((Inner width).position (pointControlPosition width)))).val = _
  rw [ContextEmbedding.contextEmbedding_join_local_value,
    ContextEmbedding.contextEmbedding_join_local_value]
  exact pointLabel_control_value width control bank.2.1 bank.1

lemma coordinates_memory_value (width m : Nat) (Reference : Register)
    (control memory : Fin 2) (bank : Bank width m Reference) :
    (((coordinates width m Reference).symm (control, (memory, bank))).1
      (Recovery.Layout.position width m 1)).val = memory.val := by
  rw [coordinates_symm, ← memory_position]
  change ((Outer width m).basis.symm
    ((Inner width).basis.symm
      (MeasuredPointAddition.label width control bank.2.1 bank.1,
        (memoryBasis width).symm memory), bank.2.2.1)
      ((Outer width m).position
        ((Inner width).positions (.inr (memoryPosition width))))).val = _
  rw [ContextEmbedding.contextEmbedding_join_local_value,
    ContextEmbedding.contextEmbedding_join_frame_value]
  exact memoryBasis_symm_value width memory

def bankBlock {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m)) (control : Fin 2) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q (ResidualReference
    p.size m Reference) divisionStore
    ((Inner p.size).store ((Outer p.size m).store stored).1).1 control

lemma pointMatrix_entry {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Interface p.size m)) (rowControl columnControl rowMemory columnMemory : Fin 2)
    (rowBank columnBank : Bank p.size m Reference) :
    pointMatrix (environment := environment) E Q m Reference divisionStore stored
        ((coordinates p.size m Reference).symm (rowControl, (rowMemory, rowBank)))
        ((coordinates p.size m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if rowControl = columnControl ∧ rowMemory = columnMemory then
        bankBlock (environment := environment) E Q m Reference divisionStore stored rowControl
          rowBank columnBank
      else 0 := by
  rw [coordinates_symm, coordinates_symm]
  simp only [pointMatrix, Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rw [Recovery.Point.Instrument.pointKraus_memory_entry]
  have source := Recovery.Point.Instrument.pointKraus_fiber_entry (environment := environment) E Q
    (ResidualReference p.size m Reference) divisionStore
    ((Inner p.size).store ((Outer p.size m).store stored).1).1
    rowControl columnControl rowBank columnBank
  simp only [Recovery.Point.Instrument.fiberBasis_symm] at source
  rw [source]
  have sameMemory : (memoryBasis p.size).symm rowMemory =
      (memoryBasis p.size).symm columnMemory ↔ rowMemory = columnMemory :=
    (memoryBasis p.size).symm.injective.eq_iff
  by_cases controlSame : rowControl = columnControl <;>
    by_cases memorySame : rowMemory = columnMemory
  · rw [if_pos controlSame, if_pos (sameMemory.mpr memorySame),
      if_pos ⟨controlSame, memorySame⟩, mul_one]
    rfl
  · rw [if_pos controlSame, if_neg (fun same => memorySame (sameMemory.mp same)),
      if_neg (fun same => memorySame same.2), mul_zero]
  · rw [if_neg controlSame, if_pos (sameMemory.mpr memorySame),
      if_neg (fun same => controlSame same.1), zero_mul]
  · rw [if_neg controlSame, if_neg (fun same => memorySame (sameMemory.mp same)),
      if_neg (fun same => controlSame same.1), zero_mul]

end

end PointCoordinates
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace FeedbackRows

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

def controlBit (width m : Nat) (basis : (Interface width m).register.Index) : Fin 2 :=
  Fin.cast (congrArg (fun size : ℕ+ => (size : Nat))
    (Recovery.Layout.position_qubit width m 0)) (basis (Recovery.Layout.position width m 0))

private def nativePhase (angle : ℝ) (bit : Fin 2) : ℂ :=
  if bit = 0 then 1 else Complex.exp ((angle : ℂ) * Complex.I)

private lemma placed_phase_entry {count : Nat} (ambient : QuantumLayout count)
    (oracles : OracleModel) {interpretation : oracles.Interpretation} (angle : ℝ) (target : Fin
      count)
    (qubit : (ambient.wire target).dimension = 2) (row column : ambient.Basis) :
    ((Gate.singleQubitAt ambient oracles (phaseGateOp angle) target qubit).matrix
      interpretation) row column =
      if row = column then
        nativePhase angle (Fin.cast
          (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (column target))
      else 0 := by
  let application := Gate.singleQubitApplication ambient (phaseGateOp angle) target qubit
  let bit : ambient.Basis → Fin 2 := fun basis =>
    Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target)
  have localEntry (first second : Fin 2) :
      (phaseGateOp angle : HilbertOperator (Qubits 1)) first second =
        if first = second then nativePhase angle second else 0 := by
    rw [phaseGateOp_diagonal]
    by_cases same : first = second
    · subst first
      simp only [Matrix.diagonal_apply, nativePhase]
    · simp only [Matrix.diagonal_apply, if_neg same]
  refine (Gate.singleQubitAt_matrix_entry ambient oracles (phaseGateOp angle)
    target qubit row column interpretation).trans ?_
  change (phaseGateOp angle : HilbertOperator (Qubits 1)) (bit row) (bit column) *
    (if (application.basisEquiv row).2 = (application.basisEquiv column).2 then 1 else 0) = _
  rw [localEntry]
  by_cases same : row = column
  · subst row
    simp only [ite_true, mul_one]
    rfl
  · by_cases selected : bit row = bit column
    · have different : (application.basisEquiv row).2 ≠
          (application.basisEquiv column).2 := by
        intro complement
        apply same
        apply application.basisEquiv.injective
        refine Prod.ext ?_ complement
        funext index
        change Fin 1 at index
        fin_cases index
        apply Fin.ext
        change (row target).val = (column target).val
        exact congrArg (fun value : Fin 2 => value.val) selected
      rw [if_pos selected, if_neg different, if_neg same, mul_zero]
    · rw [if_neg selected, if_neg same, zero_mul]

def feedbackOnePhase (width m : Nat) (previous current : Fin (2 * m))
    (stored : Store (Interface width m)) (bit : Fin 2) : ℂ :=
  if Recovery.Layout.feeds m previous current then
    match stored.read (.storage (Recovery.Layout.resultCell width m previous).toCStorageRef) with
    | .finite value => if value.val = 1 then
        nativePhase (-(QuantumFourierTransform.Source.phaseAngle
          (current.val - previous.val - 1))) bit
      else 1
  else 1

def feedbackPhase (width m : Nat) (current : Fin (2 * m))
    (stored : Store (Interface width m)) (bit : Fin 2) : List (Fin (2 * m)) → ℂ
  | [] => 1
  | previous :: tail => feedbackPhase width m current stored bit tail *
      feedbackOnePhase width m previous current stored bit

private lemma phaseProgram_entry (width m : Nat) (previous current : Fin (2 * m))
    (value : CShape.Value (.finite 2)) (row column : (Interface width m).register.Index) :
    ((phaseProgram width m previous current value).matrix environment.quantum) row column =
      if row = column then
        (match value with
        | .finite selected => if selected.val = 1 then
            nativePhase (-(QuantumFourierTransform.Source.phaseAngle
              (current.val - previous.val - 1))) (controlBit width m column)
          else 1)
      else 0 := by
  cases value with
  | finite selected =>
      by_cases enabled : selected.val = 1
      · simp only [phaseProgram, if_pos enabled]
        exact placed_phase_entry (Interface width m).quantumLayout .empty _
          (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0) row column
      · simp only [phaseProgram, if_neg enabled, UnitaryCircuit.identity_matrix]
        change (1 : HilbertOperator (Interface width m).register) row column = _
        exact Matrix.one_apply (i := row) (j := column)

lemma feedbackOneMatrix_diagonal (width m : Nat) (Reference : Register)
    (previous current : Fin (2 * m)) (stored : Store (Interface width m)) :
    feedbackOneMatrix (environment := environment) width m Reference previous current stored =
      Matrix.diagonal (fun label =>
        feedbackOnePhase width m previous current stored (controlBit width m label.1)) := by
  ext row column
  by_cases enabled : Recovery.Layout.feeds m previous current
  · simp only [feedbackOneMatrix, feedbackOnePhase, if_pos enabled]
    change ((phaseProgram width m previous current
        (stored.read (.storage (Recovery.Layout.resultCell width m
          previous).toCStorageRef))).matrix environment.quantum)
          row.1 column.1 * (1 : HilbertOperator Reference) row.2 column.2 = _
    rw [phaseProgram_entry, Matrix.one_apply]
    by_cases localSame : row.1 = column.1
    · by_cases referenceSame : row.2 = column.2
      · have same : row = column := Prod.ext localSame referenceSame
        subst row
        simp only [Matrix.diagonal_apply, ite_true, mul_one]
      · have different : row ≠ column := fun same => referenceSame (congrArg Prod.snd same)
        simp only [if_pos localSame, if_neg referenceSame, if_neg different,
          mul_zero, Matrix.diagonal_apply]
    · have different : row ≠ column := fun same => localSame (congrArg Prod.fst same)
      simp only [if_neg localSame, if_neg different, zero_mul, Matrix.diagonal_apply]
  · simp only [feedbackOneMatrix, feedbackOnePhase, if_neg enabled]
    exact Matrix.one_apply (i := row) (j := column)

lemma feedbackMatrix_diagonal (width m : Nat) (Reference : Register)
    (current : Fin (2 * m)) (stored : Store (Interface width m))
    (indices : List (Fin (2 * m))) :
    feedbackMatrix (environment := environment) width m Reference current stored indices =
      Matrix.diagonal (fun label =>
        feedbackPhase width m current stored (controlBit width m label.1) indices) := by
  induction indices with
  | nil =>
      ext row column
      simp only [feedbackMatrix, feedbackPhase, Matrix.one_apply, Matrix.diagonal_apply]
  | cons previous tail induction =>
      rw [feedbackMatrix, induction, feedbackOneMatrix_diagonal,
        Matrix.diagonal_mul_diagonal]
      rfl

lemma readout_feedback_entry (width m : Nat) (Reference : Register)
    (current : Fin (2 * m)) (stored : Store (Interface width m))
    (indices : List (Fin (2 * m)))
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension)
    (row column : ((Interface width m).register.prod Reference).Index) :
    (readoutMatrix (environment := environment) width m Reference outcome *
      feedbackMatrix (environment := environment) width m Reference current stored indices) row
        column =
        readoutMatrix (environment := environment) width m Reference outcome row column *
          feedbackPhase width m current stored (controlBit width m column.1) indices := by
  rw [feedbackMatrix_diagonal]
  exact Matrix.mul_diagonal _ _ _ _

end

end FeedbackRows
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.PreparationRows

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private def physicalLabel (width m : Nat) (Reference : Register) (control memory : Fin 2)
    (bank : Bank width m Reference) : (Recovery.Layout.terminal width m).register.Index :=
  ((coordinates width m Reference).symm (control, (memory, bank))).1

private lemma pointLabel_outside_control_value (width : Nat)
    (rowControl columnControl selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index)
    (wire : Fin (MeasuredPointAddition.context width).systemCount)
    (outside : wire ≠ pointControlPosition width) :
    (MeasuredPointAddition.label width rowControl selector original wire).val =
      (MeasuredPointAddition.label width columnControl selector original wire).val := by
  dsimp only [MeasuredPointAddition.label]
  obtain ⟨pointIndex, rfl⟩ :=
    (ContextUnion.unionPositionEquiv (InPlaceControlled.context width)
      (MeasuredPointAddition.selectorContext width)
      (MeasuredPointAddition.selector_disjoint width)).surjective wire
  cases pointIndex with
  | inr selectorWire =>
      change (((ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
          (MeasuredPointAddition.selectorContext width)
          (MeasuredPointAddition.selector_disjoint width)).symm
            (InPlaceControlled.label width rowControl original,
              (MeasuredPointAddition.selectorBasis width).symm selector))
          (ContextUnion.rightPosition _ _ _ selectorWire)).val =
        (((ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
            (MeasuredPointAddition.selectorContext width)
            (MeasuredPointAddition.selector_disjoint width)).symm
              (InPlaceControlled.label width columnControl original,
                (MeasuredPointAddition.selectorBasis width).symm selector))
            (ContextUnion.rightPosition _ _ _ selectorWire)).val
      rw [ContextUnion.contextUnion_join_right_value,
        ContextUnion.contextUnion_join_right_value]
  | inl controlled =>
      change (((ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
          (MeasuredPointAddition.selectorContext width)
          (MeasuredPointAddition.selector_disjoint width)).symm
            (InPlaceControlled.label width rowControl original,
              (MeasuredPointAddition.selectorBasis width).symm selector))
          (ContextUnion.leftPosition _ _ _ controlled)).val =
        (((ContextUnion.unionBasisEquiv (InPlaceControlled.context width)
            (MeasuredPointAddition.selectorContext width)
            (MeasuredPointAddition.selector_disjoint width)).symm
              (InPlaceControlled.label width columnControl original,
                (MeasuredPointAddition.selectorBasis width).symm selector))
            (ContextUnion.leftPosition _ _ _ controlled)).val
      rw [ContextUnion.contextUnion_join_left_value,
        ContextUnion.contextUnion_join_left_value]
      dsimp only [InPlaceControlled.label]
      obtain ⟨controlledIndex, rfl⟩ :=
        (ContextUnion.unionPositionEquiv (NumeratorMeasurement.context width)
          (InPlaceControlled.controlContext width)
          (InPlaceControlled.control_disjoint width)).surjective controlled
      cases controlledIndex with
      | inl originalWire =>
          change (((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
              (InPlaceControlled.controlContext width)
              (InPlaceControlled.control_disjoint width)).symm
                (original, (InPlaceControlled.controlBasis width).symm rowControl))
              (ContextUnion.leftPosition _ _ _ originalWire)).val =
            (((ContextUnion.unionBasisEquiv (NumeratorMeasurement.context width)
                (InPlaceControlled.controlContext width)
                (InPlaceControlled.control_disjoint width)).symm
                  (original, (InPlaceControlled.controlBasis width).symm columnControl))
                (ContextUnion.leftPosition _ _ _ originalWire)).val
          rw [ContextUnion.contextUnion_join_left_value,
            ContextUnion.contextUnion_join_left_value]
      | inr control =>
          obtain ⟨source, rfl⟩ := (positionsOfEqualWires
            (InPlaceControlled.controlLayout width)
            (InPlaceControlled.controlContext width).quantumLayout
            (InPlaceControlled.control_wires width)).surjective control
          have zero : source = (0 : Fin 1) := Subsingleton.elim _ _
          subst source
          apply False.elim
          apply outside
          change ContextUnion.leftPosition (InPlaceControlled.context width)
            (MeasuredPointAddition.selectorContext width)
            (MeasuredPointAddition.selector_disjoint width)
            (ContextUnion.rightPosition (NumeratorMeasurement.context width)
              (InPlaceControlled.controlContext width)
              (InPlaceControlled.control_disjoint width)
              (positionsOfEqualWires (InPlaceControlled.controlLayout width)
                (InPlaceControlled.controlContext width).quantumLayout
                (InPlaceControlled.control_wires width) 0)) = pointControlPosition width
          rw [← InPlaceControlled.nativePosition_right]
          rfl

private lemma outside_value (width m : Nat) (Reference : Register)
    (rowControl columnControl rowMemory columnMemory : Fin 2) (bank : Bank width m Reference)
    (wire : Fin (Recovery.Layout.terminal width m).systemCount)
    (notControl : wire ≠ Recovery.Layout.position width m 0)
    (notMemory : wire ≠ Recovery.Layout.position width m 1) :
    (physicalLabel width m Reference rowControl rowMemory bank wire).val =
      (physicalLabel width m Reference columnControl columnMemory bank wire).val := by
  have row := congrArg
    (fun labels : ((Recovery.Layout.terminal width m).register.prod Reference).Index =>
      (labels.1 wire).val)
    (coordinates_symm width m Reference rowControl rowMemory bank)
  have column := congrArg
    (fun labels : ((Recovery.Layout.terminal width m).register.prod Reference).Index =>
      (labels.1 wire).val)
    (coordinates_symm width m Reference columnControl columnMemory bank)
  refine row.trans ?_
  refine Eq.trans ?_ column.symm
  change ((Outer width m).basis.symm
      ((Inner width).basis.symm
        (MeasuredPointAddition.label width rowControl bank.2.1 bank.1,
          (memoryBasis width).symm rowMemory), bank.2.2.1) wire).val =
    ((Outer width m).basis.symm
      ((Inner width).basis.symm
        (MeasuredPointAddition.label width columnControl bank.2.1 bank.1,
          (memoryBasis width).symm columnMemory), bank.2.2.1) wire).val
  obtain ⟨outerIndex, rfl⟩ := (Outer width m).positions.surjective wire
  cases outerIndex with
  | inr frame =>
      rw [ContextEmbedding.contextEmbedding_join_frame_value,
        ContextEmbedding.contextEmbedding_join_frame_value]
  | inl ready =>
      change ((Outer width m).basis.symm
          ((Inner width).basis.symm
            (MeasuredPointAddition.label width rowControl bank.2.1 bank.1,
              (memoryBasis width).symm rowMemory), bank.2.2.1)
          ((Outer width m).position ready)).val =
        ((Outer width m).basis.symm
          ((Inner width).basis.symm
            (MeasuredPointAddition.label width columnControl bank.2.1 bank.1,
              (memoryBasis width).symm columnMemory), bank.2.2.1)
          ((Outer width m).position ready)).val
      rw [ContextEmbedding.contextEmbedding_join_local_value,
        ContextEmbedding.contextEmbedding_join_local_value]
      obtain ⟨innerIndex, rfl⟩ := (Inner width).positions.surjective ready
      cases innerIndex with
      | inr memory =>
          obtain ⟨source, rfl⟩ := (positionsOfEqualWires (indexedLayout width 1)
            (Inner width).frame.quantumLayout (memory_wires width)).surjective memory
          have zero : source = (0 : Fin 1) := Subsingleton.elim _ _
          subst source
          exact False.elim (notMemory (memory_position width m))
      | inl point =>
          change ((Inner width).basis.symm
              (MeasuredPointAddition.label width rowControl bank.2.1 bank.1,
                (memoryBasis width).symm rowMemory) ((Inner width).position point)).val =
            ((Inner width).basis.symm
              (MeasuredPointAddition.label width columnControl bank.2.1 bank.1,
                (memoryBasis width).symm columnMemory) ((Inner width).position point)).val
          rw [ContextEmbedding.contextEmbedding_join_local_value,
            ContextEmbedding.contextEmbedding_join_local_value]
          exact pointLabel_outside_control_value width rowControl columnControl
            bank.2.1 bank.1 point (fun same => notControl
              ((congrArg (fun localWire =>
                (Outer width m).position ((Inner width).position localWire)) same).trans
                  (control_position width m)))

private lemma selected_pair (width m : Nat) (Reference : Register)
    (control memory : Fin 2) (bank : Bank width m Reference) :
    Recovery.Layout.Placement.selected width m (physicalLabel width m Reference control memory
      bank) =
      QuantumSignature.qubitsIndexEquiv 2 ![control, memory] := by
  have selectedInputSame :
      UnitaryCircuit.selectedInput Recovery.Point.Program.layout (Recovery.Layout.terminal width
        m).quantumLayout
        (Recovery.Layout.preparationWires width m) (Recovery.Layout.preparation_dimensions width m)
        (physicalLabel width m Reference control memory bank) = ![control, memory] := by
    funext index
    apply Fin.ext
    have actual := Recovery.Layout.Placement.selected_physical_value width m
      (physicalLabel width m Reference control memory bank) index
    simp only [Recovery.Layout.Placement.selected, Equiv.symm_apply_apply] at actual
    fin_cases index
    · exact actual.trans (coordinates_control_value width m Reference control memory bank)
    · exact actual.trans (coordinates_memory_value width m Reference control memory bank)
  exact congrArg (QuantumSignature.qubitsIndexEquiv 2) selectedInputSame

private def remainder (width m : Nat) (Reference : Register) (control memory : Fin 2)
    (bank : Bank width m Reference) :=
  (Recovery.Layout.Placement.complement width m
      (physicalLabel width m Reference control memory bank),
    ((coordinates width m Reference).symm (control, (memory, bank))).2)

private lemma remainder_invariant (width m : Nat) (Reference : Register)
    (rowControl columnControl rowMemory columnMemory : Fin 2) (bank : Bank width m Reference) :
    remainder width m Reference rowControl rowMemory bank =
      remainder width m Reference columnControl columnMemory bank := by
  dsimp only [remainder]
  apply Prod.ext
  · funext index
    apply Fin.ext
    apply outside_value width m Reference rowControl columnControl rowMemory columnMemory bank
    · intro same
      apply Finset.mem_compl.mp index.property
      exact Finset.mem_map.mpr
        ⟨0, Finset.mem_univ _, same.symm⟩
    · intro same
      apply Finset.mem_compl.mp index.property
      exact Finset.mem_map.mpr
        ⟨1, Finset.mem_univ _, same.symm⟩
  · have referenceValue (control memory : Fin 2) :
        ((coordinates width m Reference).symm (control, (memory, bank))).2 = bank.2.2.2 :=
      (congrArg Prod.snd (coordinates_symm width m Reference control memory bank)).trans rfl
    exact (referenceValue rowControl rowMemory).trans
      (referenceValue columnControl columnMemory).symm

private lemma remainder_eq_iff (width m : Nat) (Reference : Register)
    (rowControl columnControl rowMemory columnMemory : Fin 2)
    (rowBank columnBank : Bank width m Reference) :
    remainder width m Reference rowControl rowMemory rowBank =
        remainder width m Reference columnControl columnMemory columnBank ↔
      rowBank = columnBank := by
  constructor
  · intro same
    have normalized : remainder width m Reference 0 0 rowBank =
        remainder width m Reference 0 0 columnBank :=
      (remainder_invariant width m Reference rowControl 0 rowMemory 0 rowBank).symm.trans
        (same.trans (remainder_invariant width m Reference columnControl 0 columnMemory 0
          columnBank))
    have physicalSame : physicalLabel width m Reference 0 0 rowBank =
        physicalLabel width m Reference 0 0 columnBank := by
      apply (UnitaryCircuit.basis_eq_iff_selectedInput_eq_and_complement_eq
        Recovery.Point.Program.layout (Recovery.Layout.terminal width m).quantumLayout
        (Recovery.Layout.preparationWires width m) (Recovery.Layout.preparation_dimensions width m)
        _ _).mpr
      constructor
      · apply (QuantumSignature.qubitsIndexEquiv 2).injective
        change Recovery.Layout.Placement.selected width m
            (physicalLabel width m Reference 0 0 rowBank) =
          Recovery.Layout.Placement.selected width m
            (physicalLabel width m Reference 0 0 columnBank)
        rw [selected_pair, selected_pair]
      · exact congrArg Prod.fst normalized
    have referenceSame := congrArg Prod.snd normalized
    dsimp only [remainder] at referenceSame
    have jointSame : (coordinates width m Reference).symm (0, (0, rowBank)) =
        (coordinates width m Reference).symm (0, (0, columnBank)) :=
      Prod.ext physicalSame referenceSame
    exact congrArg (fun value : Fin 2 × (Fin 2 × Bank width m Reference) => value.2.2)
      ((coordinates width m Reference).symm.injective jointSame)
  · intro same
    subst columnBank
    exact remainder_invariant width m Reference rowControl columnControl rowMemory columnMemory
      rowBank

private def bit (value : Bool) : Fin 2 := if value then 1 else 0

private lemma selected_bool_pair (width m : Nat) (Reference : Register)
    (control memory : Bool) (bank : Bank width m Reference) :
    Recovery.Layout.Placement.selected width m
        (physicalLabel width m Reference (bit control) (bit memory) bank) =
      Recovery.Point.Extension.index control memory := by
  rw [selected_pair]
  cases control <;> cases memory <;> rfl

private lemma spectator_indicators_mul (coefficient : ℂ) {first second result : Prop}
    {firstDecision : Decidable first} {secondDecision : Decidable second}
    {resultDecision : Decidable result} (same : first ∧ second ↔ result) :
    (coefficient * @ite ℂ first firstDecision 1 0) * @ite ℂ second secondDecision 1 0 =
      coefficient * @ite ℂ result resultDecision 1 0 := by
  by_cases left : first
  · by_cases right : second
    · simp only [if_pos left, if_pos right, if_pos (same.mp ⟨left, right⟩), mul_one]
    · have absent : ¬ result := fun value => right (same.mpr value).2
      simp only [if_pos left, if_neg right, if_neg absent, mul_one, mul_zero]
  · have absent : ¬ result := fun value => left (same.mpr value).1
    simp only [if_neg left, if_neg absent, mul_zero, zero_mul]

lemma preparationMatrix_columns (width m r : Nat) (index : Fin (2 * m))
    (Reference : Register) (input emitted next : Bool)
    (rowBank columnBank : Bank width m Reference) :
    preparationMatrix (environment := environment) width m r index Reference
        ((coordinates width m Reference).symm (bit emitted, (bit next, rowBank)))
        ((coordinates width m Reference).symm (0, (bit input, columnBank))) =
      (table (2 ^ Recovery.Layout.remaining m index)
        (r % (2 * 2 ^ Recovery.Layout.remaining m index)) input emitted next : ℂ) *
          (if rowBank = columnBank then 1 else 0) := by
  rw [preparationMatrix, UnitaryOperator.unitaryOperator_prodTensor_apply]
  change ((Recovery.Layout.preparation width m r (Recovery.Layout.remaining m index)).matrix
      environment.quantum (physicalLabel width m Reference (bit emitted) (bit next) rowBank)
      (physicalLabel width m Reference (bit false) (bit input) columnBank) *
    (1 : Matrix Reference.Index Reference.Index ℂ)
      (((coordinates width m Reference).symm (bit emitted, (bit next, rowBank))).2)
      (((coordinates width m Reference).symm (bit false, (bit input, columnBank))).2)) = _
  rw [Recovery.Layout.Placement.preparation_columns width m r (Recovery.Layout.remaining m index)
    input emitted next _ _ (selected_bool_pair width m Reference emitted next rowBank)
      (selected_bool_pair width m Reference false input columnBank), Matrix.one_apply]
  have equivalent := Prod.ext_iff.symm.trans (remainder_eq_iff width m Reference
    (bit emitted) (bit false) (bit next) (bit input) rowBank columnBank)
  dsimp only [remainder] at equivalent
  exact spectator_indicators_mul _ equivalent

end

end PointCoordinates.PreparationRows
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.ReadoutRows

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private lemma memory_ne_control (width m : Nat) :
    Recovery.Layout.position width m 1 ≠ Recovery.Layout.position width m 0 := by
  intro same
  have wire := congrArg
    (fun position => ((Interface width m).quantumLayout.wire position).identity) same
  rw [Recovery.Layout.position_wire, Recovery.Layout.position_wire] at wire
  exact Nat.one_ne_zero (Nat.add_left_cancel wire)

private lemma outside_head_iff (width m : Nat) (Reference : Register)
    (rowControl columnControl rowMemory columnMemory : Fin 2)
    (rowBank columnBank : Bank width m Reference) :
    ((∀ wire : Fin (Interface width m).systemCount,
        wire ≠ Recovery.Layout.position width m 0 →
          ((coordinates width m Reference).symm (rowControl, (rowMemory, rowBank))).1 wire =
            ((coordinates width m Reference).symm
              (columnControl, (columnMemory, columnBank))).1 wire) ∧
      ((coordinates width m Reference).symm (rowControl, (rowMemory, rowBank))).2 =
        ((coordinates width m Reference).symm
          (columnControl, (columnMemory, columnBank))).2) ↔
      rowMemory = columnMemory ∧ rowBank = columnBank := by
  constructor
  · rintro ⟨outside, referenceSame⟩
    have memorySame : rowMemory = columnMemory := by
      apply Fin.ext
      have physical := congrArg Fin.val
        (outside (Recovery.Layout.position width m 1) (memory_ne_control width m))
      rw [coordinates_memory_value, coordinates_memory_value] at physical
      exact physical
    have remainderSame :
        PreparationRows.remainder width m Reference rowControl rowMemory rowBank =
          PreparationRows.remainder width m Reference columnControl columnMemory columnBank :=
      by
      dsimp only [PreparationRows.remainder]
      apply Prod.ext
      · funext wire
        exact outside wire.val (fun same =>
          (Finset.mem_compl.mp wire.property) (Finset.mem_map.mpr
            ⟨0, Finset.mem_univ _, same.symm⟩))
      · exact referenceSame
    exact ⟨memorySame, (PreparationRows.remainder_eq_iff width m Reference
      rowControl columnControl rowMemory columnMemory rowBank columnBank).mp remainderSame⟩
  · rintro ⟨memorySame, bankSame⟩
    subst columnMemory
    subst columnBank
    constructor
    · intro wire notControl
      apply Fin.ext
      by_cases isMemory : wire = Recovery.Layout.position width m 1
      · subst wire
        rw [coordinates_memory_value, coordinates_memory_value]
      · exact PreparationRows.outside_value width m Reference rowControl columnControl
          rowMemory rowMemory rowBank wire notControl isMemory
    · have referenceValue (control memory : Fin 2) :
          ((coordinates width m Reference).symm (control, (memory, rowBank))).2 =
            rowBank.2.2.2 :=
        (congrArg Prod.snd (coordinates_symm width m Reference control memory rowBank)).trans rfl
      exact (referenceValue rowControl rowMemory).trans
        (referenceValue columnControl rowMemory).symm

private lemma reset_operator_row {count : Nat} (layout : QuantumLayout count)
    (wire : Fin count) (Reference : Register)
    (outcome : Fin (layout.wire wire).dimension)
    (following : HilbertOperator (layout.register.prod Reference))
    (row : layout.Basis) (rowReference : Reference.Index)
    (column : (layout.register.prod Reference).Index) :
    ((UnitaryOperator.prodTensor (QuditShift.operator layout wire (-outcome))
        (1 : UnitaryOperator Reference)).val *
      ZMeasurement.projector (R := layout.register.prod Reference)
        (fun basis => basis.1 wire) outcome * following) (row, rowReference) column =
      if row wire = 0 then
        following (Function.update row wire outcome, rowReference) column
      else 0 := by
  rw [QuditShift.operator_reference_permutation]
  let shifted : (layout.register.prod Reference).Index ≃
      (layout.register.prod Reference).Index :=
    (QuditShift.labelShift layout wire (-outcome)).symm.prodCongr
      (Equiv.refl Reference.Index)
  change ((shifted.toPEquiv.toMatrix : HilbertOperator (layout.register.prod Reference)) *
    ZMeasurement.projector (R := layout.register.prod Reference)
      (fun basis => basis.1 wire) outcome * following) (row, rowReference) column = _
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
  change (ZMeasurement.projector (R := layout.register.prod Reference)
      (fun basis => basis.1 wire) outcome * following)
    (Function.update row wire (row wire - -outcome), rowReference) column = _
  rw [ZMeasurement.projector, Matrix.diagonal_mul]
  simp only [Function.update_self, sub_neg_eq_add, ZReset.shiftedLabelEqOutcome]
  by_cases zero : row wire = 0
  · simp only [zero, if_true, zero_add, one_mul]
  · simp only [if_neg zero, zero_mul]

private lemma hadamard_reference_entry (width m : Nat) (Reference : Register)
    (row column : ((Interface width m).register.prod Reference).Index) :
    (UnitaryOperator.prodTensor
      ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
          environment.quantum)
      (1 : UnitaryOperator Reference)).val row column =
      Gate.HOp (FeedbackRows.controlBit width m row.1)
        (FeedbackRows.controlBit width m column.1) *
          (if (∀ wire : Fin (Interface width m).systemCount,
              wire ≠ Recovery.Layout.position width m 0 → row.1 wire = column.1 wire) ∧
            row.2 = column.2 then 1 else 0) := by
  have localEntry :
      ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
          environment.quantum)
          row.1 column.1 =
        Gate.HOp (FeedbackRows.controlBit width m row.1)
          (FeedbackRows.controlBit width m column.1) *
            (if ∀ wire : Fin (Interface width m).systemCount,
              wire ≠ Recovery.Layout.position width m 0 → row.1 wire = column.1 wire then 1 else
                0) := by
    refine (Gate.singleQubitAt_matrix_entry_outside (Interface width m).quantumLayout .empty
      Gate.HOp (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)
      row.1 column.1 environment.quantum).trans ?_
    apply congrArg (fun indicator : ℂ =>
      Gate.HOp (FeedbackRows.controlBit width m row.1)
        (FeedbackRows.controlBit width m column.1) * indicator)
    by_cases outside : ∀ wire : Fin (Interface width m).systemCount,
        wire ≠ Recovery.Layout.position width m 0 → row.1 wire = column.1 wire
    · simp only [if_pos outside]
    · simp only [if_neg outside]
  have referenceEntry : (1 : UnitaryOperator Reference) row.2 column.2 =
      if row.2 = column.2 then (1 : ℂ) else 0 := by
    change (1 : HilbertOperator Reference) row.2 column.2 = _
    by_cases same : row.2 = column.2 <;>
      simp only [Matrix.one_apply, same, ite_true, ite_false]
  refine (UnitaryOperator.unitaryOperator_prodTensor_apply
    ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
      (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
        environment.quantum)
    (1 : UnitaryOperator Reference) row column).trans ?_
  rw [localEntry, referenceEntry]
  split_ifs <;> simp_all

private lemma readoutMatrix_reset_row (width m : Nat) (Reference : Register)
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension)
    (row column : ((Interface width m).register.prod Reference).Index) :
    readoutMatrix (environment := environment) width m Reference outcome row column =
      if row.1 (Recovery.Layout.position width m 0) = 0 then
        (UnitaryOperator.prodTensor
          ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
            (Recovery.Layout.position width m 0)
            (Recovery.Layout.position_qubit width m 0)).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).val
            (Function.update row.1 (Recovery.Layout.position width m 0) outcome, row.2) column
      else 0 := by
  let hadamard : HilbertOperator ((Interface width m).register.prod Reference) :=
    (UnitaryOperator.prodTensor
      ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
          environment.quantum)
      (1 : UnitaryOperator Reference)).val
  have correctionSame :=
    QuditShift.qubitShiftCircuit_matrix (Interface width m).quantumLayout
      (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0) .empty
        (-outcome) environment.quantum
  have correctionTensor :=
    congrArg (fun operator : UnitaryOperator (Interface width m).register =>
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)).val) correctionSame
  change ((UnitaryOperator.prodTensor
    ((correction width m (.finite outcome)).matrix environment.quantum)
      (1 : UnitaryOperator Reference)).val *
    ZMeasurement.projector (R := (Interface width m).register.prod Reference)
      (fun basis => basis.1 (Recovery.Layout.position width m 0)) outcome * hadamard) row
        column = _
  refine (congrArg (fun matrix : HilbertOperator ((Interface width m).register.prod Reference) =>
    (matrix * ZMeasurement.projector (R := (Interface width m).register.prod Reference)
      (fun basis => basis.1 (Recovery.Layout.position width m 0)) outcome * hadamard) row column)
    correctionTensor).trans ?_
  exact reset_operator_row (Interface width m).quantumLayout (Recovery.Layout.position width m 0)
    Reference outcome hadamard row.1 row.2 column

lemma readoutMatrix_entry (width m : Nat) (Reference : Register)
    (outcome : Fin ((Interface width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension)
    (rowControl columnControl rowMemory columnMemory : Fin 2)
    (rowBank columnBank : Bank width m Reference) :
    readoutMatrix (environment := environment) width m Reference outcome
      ((coordinates width m Reference).symm (rowControl, (rowMemory, rowBank)))
      ((coordinates width m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if rowControl = 0 ∧ rowMemory = columnMemory ∧ rowBank = columnBank then
        Gate.HOp (outcomeBit width m outcome) columnControl
      else 0 := by
  let row := (coordinates width m Reference).symm (rowControl, (rowMemory, rowBank))
  let column := (coordinates width m Reference).symm (columnControl, (columnMemory, columnBank))
  have zeroIff : row.1 (Recovery.Layout.position width m 0) = 0 ↔ rowControl = 0 := by
    simp only [Fin.ext_iff, Fin.val_zero, row, coordinates_control_value]
  have columnBit : FeedbackRows.controlBit width m column.1 = columnControl := by
    apply Fin.ext
    exact coordinates_control_value width m Reference columnControl columnMemory columnBank
  have rowBit : FeedbackRows.controlBit width m
      (Function.update row.1 (Recovery.Layout.position width m 0) outcome) =
        outcomeBit width m outcome := by
    apply Fin.ext
    simp only [FeedbackRows.controlBit, outcomeBit, Function.update_self]
  have outsideIff :
      ((∀ wire : Fin (Interface width m).systemCount,
          wire ≠ Recovery.Layout.position width m 0 →
            Function.update row.1 (Recovery.Layout.position width m 0) outcome wire =
              column.1 wire) ∧ row.2 = column.2) ↔
        rowMemory = columnMemory ∧ rowBank = columnBank := by
    have unchanged :
        (∀ wire : Fin (Interface width m).systemCount,
          wire ≠ Recovery.Layout.position width m 0 →
            Function.update row.1 (Recovery.Layout.position width m 0) outcome wire =
              column.1 wire) ↔
          (∀ wire : Fin (Interface width m).systemCount,
            wire ≠ Recovery.Layout.position width m 0 → row.1 wire = column.1 wire) := by
      constructor <;> intro same wire outside
      · simpa only [Function.update_of_ne outside] using same wire outside
      · simpa only [Function.update_of_ne outside] using same wire outside
    rw [unchanged]
    exact outside_head_iff width m Reference rowControl columnControl rowMemory columnMemory
      rowBank columnBank
  change readoutMatrix (environment := environment) width m Reference outcome row column = _
  refine (readoutMatrix_reset_row width m Reference outcome row column).trans ?_
  by_cases zero : rowControl = 0
  · rw [if_pos (zeroIff.mpr zero)]
    change (UnitaryOperator.prodTensor
      ((Gate.singleQubitAt (Interface width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
          environment.quantum)
      (1 : UnitaryOperator Reference)).val
        (Function.update row.1 (Recovery.Layout.position width m 0) outcome, row.2) column = _
    rw [hadamard_reference_entry, rowBit, columnBit]
    by_cases spectators : rowMemory = columnMemory ∧ rowBank = columnBank
    · simp only [if_pos (outsideIff.mpr spectators), mul_one, zero, spectators,
        and_self, if_true]
    · simp only [if_neg (fun same => spectators (outsideIff.mp same)), mul_zero]
      simp only [zero, true_and, if_neg spectators]
  · rw [if_neg (fun same => zero (zeroIff.mp same))]
    have blocked : ¬(rowControl = 0 ∧ rowMemory = columnMemory ∧
      rowBank = columnBank) := fun accepted => zero accepted.1
    rw [if_neg blocked]

end

end PointCoordinates.ReadoutRows
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

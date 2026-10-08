/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Framing
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# Original inverse QFT on the complete allocated scalar register

Identity on the actual selector and arithmetic complement surrounds the
original exponent program. The complete preparation-assembly equivalence
places this tensor on the existing allocated context; no new preparation or
physical swap occurs. Every complement label is retained, without a promise
that it is zero or independent of the exponent state.

The terminal exponent wires are the identical physical systems used by the
original paired big-endian selection. Their exact dimension-two and value
identities provide the inputs for actual retained Z readout instructions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA

private def readoutIdentity {count : Nat} (layout : QuantumLayout count) :
    UnitaryCircuit AlgorithmGate.model .empty layout :=
  UnitaryCircuit.identity AlgorithmGate.model .empty layout

private theorem readoutAuxiliaryDisjoint (width count : Nat) :
    List.Disjoint (InputPreparation.auxiliaryLayout width).identities
      (before width count).quantumLayout.identities := by
  simpa only [RuntimeCtx.runtimeCtx_quantumLayout_identities] using
    ContextUnion.preparation_wires_union InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
      (InversePreparation.auxiliary_disjoint width) (auxiliary_disjoint width count)

private theorem readoutCellsWires (width count : Nat) :
    (QuantumLayout.append (InputPreparation.auxiliaryLayout width)
      (before width count).quantumLayout (readoutAuxiliaryDisjoint width count)).wires =
        (withCells width count).quantumLayout.wires := by
  simp only [QuantumLayout.wires_append, RuntimeCtx.quantumLayout_wires,
    withCells, RuntimeCtx.quantumWires_disjointUnion, before]
  change (InputPreparation.auxiliaryLayout width).wires ++
      ((InversePreparation.before width).quantumWires ++
        (exponents width count).quantumWires) =
    (MeasurementCells.context (InversePreparation.after width) 2 width).quantumWires ++
      (exponents width count).quantumWires
  rw [MeasurementCells.context_quantumWires, InversePreparation.after,
    RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout]
  exact (List.append_assoc _ _ _).symm

private def readoutAuxiliaryProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    UnitaryCircuit AlgorithmGate.model .empty
      (withCells modulus.size (2 * exponentWidth)).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumLayout.append (InputPreparation.auxiliaryLayout modulus.size)
      (before modulus.size (2 * exponentWidth)).quantumLayout
      (readoutAuxiliaryDisjoint modulus.size (2 * exponentWidth)))
    (withCells modulus.size (2 * exponentWidth)).quantumLayout
    (readoutCellsWires modulus.size (2 * exponentWidth))
    (UnitaryCircuit.tensor (readoutIdentity (InputPreparation.auxiliaryLayout modulus.size))
      (beforeExponentProgram modulus exponentWidth program)
      (readoutAuxiliaryDisjoint modulus.size (2 * exponentWidth)))

private theorem readoutSelectorDisjoint (width count : Nat) :
    List.Disjoint (indexedLayout width count).identities
      (withCells width count).quantumLayout.identities := by
  simpa only [RuntimeCtx.runtimeCtx_quantumLayout_identities] using
    selector_disjoint width count

private theorem readoutSelectorWires (width count : Nat) :
    (QuantumLayout.append (indexedLayout width count)
      (withCells width count).quantumLayout (readoutSelectorDisjoint width count)).wires =
        (after width count).quantumLayout.wires :=
  RuntimeCtx.addOwnedLayout_wires_eq_append
    (withCells width count) (indexedKey width count) (indexedLayout width count)
      (selector_fresh width count) (selector_disjoint width count)

/-- The original exponent gates act beside identity on every actual allocated work coordinate. -/
def afterExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    UnitaryCircuit AlgorithmGate.model .empty
      (after modulus.size (2 * exponentWidth)).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QuantumLayout.append (indexedLayout modulus.size (2 * exponentWidth))
      (withCells modulus.size (2 * exponentWidth)).quantumLayout
      (readoutSelectorDisjoint modulus.size (2 * exponentWidth)))
    (after modulus.size (2 * exponentWidth)).quantumLayout
    (readoutSelectorWires modulus.size (2 * exponentWidth))
    (UnitaryCircuit.tensor (readoutIdentity (indexedLayout modulus.size (2 * exponentWidth)))
      (readoutAuxiliaryProgram modulus exponentWidth program)
      (readoutSelectorDisjoint modulus.size (2 * exponentWidth)))

private theorem readoutPrepWires (width count : Nat) :
    (QuantumLayout.append (InputPreparation.auxiliaryLayout width)
      (before width count).quantumLayout (readoutAuxiliaryDisjoint width count)).wires =
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).quantumLayout.wires := by
  rw [QuantumLayout.wires_append]
  simp only [RuntimeCtx.quantumLayout_wires]
  simp only [before, RuntimeCtx.quantumWires_disjointUnion]
  rw [InversePreparation.after, RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout]
  exact (List.append_assoc _ _ _).symm

private theorem readoutPrepAssembly_eq (modulus count : Nat) :
    (QuantumLayout.appendBasisEquiv (InputPreparation.auxiliaryLayout modulus.size)
      (before modulus.size count).quantumLayout
      (readoutAuxiliaryDisjoint modulus.size count)).symm.trans
        (Execution.basisOfEqualWires
          (QuantumLayout.append (InputPreparation.auxiliaryLayout modulus.size)
            (before modulus.size count).quantumLayout
            (readoutAuxiliaryDisjoint modulus.size count))
          ((InversePreparation.after modulus.size).disjointUnion
            (exponents modulus.size count) (auxiliary_disjoint modulus.size count)).quantumLayout
          (readoutPrepWires modulus.size count)) =
      auxiliaryAssembly modulus count := by
  rfl

private theorem framedCellsWires (ctx frame : RuntimeCtx .quantum)
    (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint
      (MeasurementCells.context ctx dimension count) frame) :
    ((ctx.disjointUnion frame (MeasurementCells.original_disjoint ctx frame
      dimension count separate)).quantumLayout).wires =
    ((MeasurementCells.context ctx dimension count).disjointUnion
      frame separate).quantumLayout.wires := by
  simp only [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumWires_disjointUnion,
    MeasurementCells.context_quantumWires]

private theorem framedCellsBasis_eq (ctx frame : RuntimeCtx .quantum)
    (dimension : ℕ+) : (count : Nat) →
    (separate : RuntimeCtx.StorageDisjoint
      (MeasurementCells.context ctx dimension count) frame) →
    Execution.basisOfEqualWires
      (ctx.disjointUnion frame
        (MeasurementCells.original_disjoint ctx frame dimension count separate)).quantumLayout
      ((MeasurementCells.context ctx dimension count).disjointUnion frame separate).quantumLayout
      (framedCellsWires ctx frame dimension count separate) =
    MeasurementCells.framedBasisEquiv ctx frame dimension count separate
  | 0, _ => rfl
  | count + 1, separate => by
      apply Equiv.ext
      intro basis
      funext index
      apply Fin.ext
      let prefixSeparate := MeasurementCells.original_disjoint
        (MeasurementCells.context ctx dimension count) frame dimension 1 separate
      let source := (ctx.disjointUnion frame
        (MeasurementCells.original_disjoint ctx frame dimension count prefixSeparate)).quantumLayout
      let priorLayout := ((MeasurementCells.context ctx dimension count).disjointUnion
        frame prefixSeparate).quantumLayout
      let current := ((MeasurementCells.context ctx dimension (count + 1)).disjointUnion
        frame separate).quantumLayout
      let sourceIndex :=
        (Execution.positionsOfEqualWires source priorLayout
          (framedCellsWires ctx frame dimension count prefixSeparate)).symm index
      have currentPosition :
          Execution.positionsOfEqualWires source current
            (framedCellsWires ctx frame dimension (count + 1) separate) sourceIndex =
            index := Fin.ext rfl
      have currentValue := Execution.basisOfEqualWires_value source current
        (framedCellsWires ctx frame dimension (count + 1) separate) basis sourceIndex
      rw [currentPosition] at currentValue
      have prefixValue := Execution.basisOfEqualWires_value source priorLayout
        (framedCellsWires ctx frame dimension count prefixSeparate) basis sourceIndex
      have priorPosition :
          Execution.positionsOfEqualWires source priorLayout
            (framedCellsWires ctx frame dimension count prefixSeparate) sourceIndex =
            index :=
        (Execution.positionsOfEqualWires source priorLayout
          (framedCellsWires ctx frame dimension count prefixSeparate)).apply_symm_apply index
      rw [priorPosition] at prefixValue
      have inherited := congrArg (fun equivalence => (equivalence basis index).val)
        (framedCellsBasis_eq ctx frame dimension count prefixSeparate)
      exact currentValue.trans (prefixValue.symm.trans inherited)

private theorem equalWiresBasis_trans {firstCount middleCount lastCount : Nat}
    (first : QuantumLayout firstCount) (middle : QuantumLayout middleCount)
    (last : QuantumLayout lastCount) (firstMiddle : first.wires = middle.wires)
    (middleLast : middle.wires = last.wires) (firstLast : first.wires = last.wires) :
    (Execution.basisOfEqualWires first middle firstMiddle).trans
      (Execution.basisOfEqualWires middle last middleLast) =
        Execution.basisOfEqualWires first last firstLast := by
  apply Equiv.ext
  intro basis
  funext index
  apply Fin.ext
  rfl

private theorem readoutCellsAssembly_eq (width count : Nat) :
    Execution.basisOfEqualWires
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).quantumLayout
      (withCells width count).quantumLayout
      (framedCellsWires (InversePreparation.after width) (exponents width count)
        2 width (complete_disjoint width count)) =
      cellsAssembly width count := by
  exact framedCellsBasis_eq (InversePreparation.after width) (exponents width count)
    2 width (complete_disjoint width count)

private theorem readoutAuxiliaryAssembly_eq (modulus count : Nat) :
    (QuantumLayout.appendBasisEquiv (InputPreparation.auxiliaryLayout modulus.size)
      (before modulus.size count).quantumLayout
      (readoutAuxiliaryDisjoint modulus.size count)).symm.trans
        (Execution.basisOfEqualWires
          (QuantumLayout.append (InputPreparation.auxiliaryLayout modulus.size)
            (before modulus.size count).quantumLayout
            (readoutAuxiliaryDisjoint modulus.size count))
          (withCells modulus.size count).quantumLayout
          (readoutCellsWires modulus.size count)) =
      (auxiliaryAssembly modulus count).trans (cellsAssembly modulus.size count) := by
  apply Equiv.ext
  intro basis
  have composed := congrArg (fun equivalence =>
      equivalence ((QuantumLayout.appendBasisEquiv
        (InputPreparation.auxiliaryLayout modulus.size)
        (before modulus.size count).quantumLayout
        (readoutAuxiliaryDisjoint modulus.size count)).symm basis))
    (equalWiresBasis_trans
      (QuantumLayout.append (InputPreparation.auxiliaryLayout modulus.size)
        (before modulus.size count).quantumLayout
        (readoutAuxiliaryDisjoint modulus.size count))
      ((InversePreparation.after modulus.size).disjointUnion
        (exponents modulus.size count) (auxiliary_disjoint modulus.size count)).quantumLayout
      (withCells modulus.size count).quantumLayout
      (readoutPrepWires modulus.size count)
      (framedCellsWires (InversePreparation.after modulus.size)
        (exponents modulus.size count) 2 modulus.size
        (complete_disjoint modulus.size count))
      (readoutCellsWires modulus.size count))
  simp only [Equiv.trans_apply] at composed ⊢
  rw [← composed, ← readoutPrepAssembly_eq, ← readoutCellsAssembly_eq]
  rfl

private theorem readoutSelectorAssembly_eq (width count : Nat) :
    (QuantumLayout.appendBasisEquiv (indexedLayout width count)
      (withCells width count).quantumLayout (readoutSelectorDisjoint width count)).symm.trans
        (Execution.basisOfEqualWires
          (QuantumLayout.append (indexedLayout width count)
            (withCells width count).quantumLayout (readoutSelectorDisjoint width count))
          (after width count).quantumLayout (readoutSelectorWires width count)) =
      selectorAssembly width count := by
  rfl

private theorem readoutAuxiliaryProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (readoutAuxiliaryProgram modulus exponentWidth program).matrix =
      UnitaryOperator.reindex
        ((auxiliaryAssembly modulus (2 * exponentWidth)).trans
          (cellsAssembly modulus.size (2 * exponentWidth)))
        (UnitaryOperator.prodTensor
          (1 : UnitaryOperator (InputPreparation.auxiliaryLayout modulus.size).register)
          (beforeExponentProgram modulus exponentWidth program).matrix) := by
  unfold readoutAuxiliaryProgram
  rw [Execution.unitaryOfEqualWires_matrix, UnitaryCircuit.tensor_native_matrix]
  rw [readoutIdentity, UnitaryCircuit.identity_matrix,
    UnitaryOperator.unitaryOperator_reindex_trans,
    readoutAuxiliaryAssembly_eq]

private theorem afterExponentProgram_matrix (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (afterExponentProgram modulus exponentWidth program).matrix =
      UnitaryOperator.reindex (selectorAssembly modulus.size (2 * exponentWidth))
        (UnitaryOperator.prodTensor
          (1 : UnitaryOperator (indexedLayout modulus.size (2 * exponentWidth)).register)
          (readoutAuxiliaryProgram modulus exponentWidth program).matrix) := by
  unfold afterExponentProgram
  rw [Execution.unitaryOfEqualWires_matrix, UnitaryCircuit.tensor_native_matrix]
  rw [readoutIdentity, UnitaryCircuit.identity_matrix,
    UnitaryOperator.unitaryOperator_reindex_trans,
    readoutSelectorAssembly_eq]

/-- Every selector and auxiliary label is retained in the actual complete matrix. -/
theorem afterExponentProgram_assembly_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (row column : (indexedLayout modulus.size (2 * exponentWidth)).register.Index ×
      (InputPreparation.auxiliaryLayout modulus.size).register.Index ×
        (before modulus.size (2 * exponentWidth)).register.Index) :
    (afterExponentProgram modulus exponentWidth program).matrix
      (initializedAssembly modulus (2 * exponentWidth) row)
      (initializedAssembly modulus (2 * exponentWidth) column) =
      (if row.1 = column.1 then 1 else 0) *
        ((if row.2.1 = column.2.1 then 1 else 0) *
          (beforeExponentProgram modulus exponentWidth program).matrix
            row.2.2 column.2.2) := by
  rw [afterExponentProgram_matrix, readoutAuxiliaryProgram_matrix]
  change (UnitaryOperator.prodTensor
    (1 : UnitaryOperator (indexedLayout modulus.size (2 * exponentWidth)).register)
    (UnitaryOperator.prodTensor
      (1 : UnitaryOperator (InputPreparation.auxiliaryLayout modulus.size).register)
      (beforeExponentProgram modulus exponentWidth program).matrix))
      ((initializedAssembly modulus (2 * exponentWidth)).symm
        (initializedAssembly modulus (2 * exponentWidth) row))
      ((initializedAssembly modulus (2 * exponentWidth)).symm
        (initializedAssembly modulus (2 * exponentWidth) column)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    UnitaryOperator.prodTensor_apply, UnitaryOperator.prodTensor_apply]
  rfl

/-- The complete allocated frame adds no native event to the original exponent code. -/
theorem afterExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    (afterExponentProgram modulus exponentWidth program).eventTrace =
      program.eventTrace := by
  change [] ++ ([] ++ (beforeExponentProgram modulus exponentWidth program).eventTrace) = _
  rw [List.nil_append, List.nil_append, beforeExponentProgram_trace]

/-- The actual original exponent program executes on the complete allocated scalar context. -/
def afterExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout) :
    Circuit (.quantum AlgorithmGate.model .empty) (after modulus.size (2 * exponentWidth))
      (after modulus.size (2 * exponentWidth)) :=
  .unitary (afterExponentProgram modulus exponentWidth program)

/-- Actual allocated-context execution retains the full quantum-reference density. -/
theorem afterExponentCircuit_density (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (after modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((afterExponentCircuit modulus exponentWidth program).execute
      Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program).matrix
          (1 : UnitaryOperator Reference)) state.quantumMarginal :=
  Circuit.unitary_jointDensity (afterExponentProgram modulus exponentWidth program) state

/-- Actual readout framing retains the exact original native event cost. -/
theorem afterExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (path : (afterExponentCircuit modulus exponentWidth program).Path) :
    (afterExponentCircuit modulus exponentWidth program).resourcePool path =
      program.eventCost := by
  change ResourcePool.ofList
    (afterExponentProgram modulus exponentWidth program).eventTrace = _
  rw [afterExponentProgram_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- Every native duration assignment gives the original program depth on the allocated context. -/
theorem afterExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (afterExponentCircuit modulus exponentWidth program).Path) :
    (afterExponentCircuit modulus exponentWidth program).depth duration path =
      program.evaluatedEventDepth duration := by
  change max 0 (max 0
    ((beforeExponentProgram modulus exponentWidth program).evaluatedEventDepth
      duration)) = _
  rw [Nat.zero_max, Nat.zero_max]
  exact beforeExponentCircuit_depth modulus exponentWidth program duration ()

/-- The original exponent order names its identical systems in the final allocated context. -/
def afterExponentWires (modulus exponentWidth : Nat) (index : Fin (2 * exponentWidth)) :
    Fin (after modulus.size (2 * exponentWidth)).systemCount :=
  ContextPermutation.positions (body_entries modulus.size (2 * exponentWidth))
    (indexedPosition modulus.size (2 * exponentWidth) index.castSucc)

/-- Terminal exponent index i is exactly its original physical dimension-two wire. -/
theorem afterExponentWires_wire (modulus exponentWidth : Nat) (index : Fin (2 * exponentWidth)) :
    (after modulus.size (2 * exponentWidth)).quantumLayout.wire
      (afterExponentWires modulus exponentWidth index) =
      QuantumWire.mk (InPlaceControlled.frameWidth modulus.size + index.val) 2 := by
  rw [afterExponentWires, ContextPermutation.positions_wire]
  change (readyContext modulus.size (2 * exponentWidth)).quantumLayout.wire
    (ContextUnion.rightPosition (NumeratorMeasurement.context modulus.size)
      (indexedContext modulus.size (List.range (2 * exponentWidth + 1)) List.nodup_range)
      (indexedContext_disjoint modulus.size (List.range (2 * exponentWidth + 1))
        List.nodup_range)
      (rangePosition modulus.size (2 * exponentWidth + 1) index.castSucc)) = _
  rw [ContextUnion.contextUnion_right_wire, rangePosition_wire]
  rfl

/-- Every actual terminal exponent read has the required qubit dimension. -/
theorem afterExponentWires_qubits (modulus exponentWidth : Nat)
    (index : Fin (2 * exponentWidth)) :
    ((after modulus.size (2 * exponentWidth)).quantumLayout.wire
      (afterExponentWires modulus exponentWidth index)).dimension = 2 :=
  congrArg QuantumWire.dimension (afterExponentWires_wire modulus exponentWidth index)

/-- Distinct original exponent positions remain distinct actual readout systems. -/
theorem afterExponentWires_injective (modulus exponentWidth : Nat) :
    Function.Injective (afterExponentWires modulus exponentWidth) := by
  intro left right same
  have identities := congrArg (fun position =>
    ((after modulus.size (2 * exponentWidth)).quantumLayout.wire position).identity) same
  rw [afterExponentWires_wire, afterExponentWires_wire] at identities
  apply Fin.ext
  exact Nat.add_left_cancel identities

/-- Actual terminal values are the same original indexed selections on every complete basis. -/
theorem afterExponentWires_value (modulus exponentWidth : Nat)
    (value : (after modulus.size (2 * exponentWidth)).register.Index)
    (index : Fin (2 * exponentWidth)) :
    (value (afterExponentWires modulus exponentWidth index)).val =
      (indexedValue modulus.size (2 * exponentWidth)
        ((ContextPermutation.basis (body_entries modulus.size (2 * exponentWidth))).symm value)
        index.castSucc).val := by
  have actual := ContextPermutation.basis_value (body_entries modulus.size (2 * exponentWidth))
    ((ContextPermutation.basis (body_entries modulus.size (2 * exponentWidth))).symm value)
    (indexedPosition modulus.size (2 * exponentWidth) index.castSucc)
  rw [Equiv.apply_symm_apply] at actual
  exact actual.trans (indexedValue_value modulus.size (2 * exponentWidth) _ index.castSucc).symm

universe u

/-- The unchanged original inverse-QFT readout acts on the complete allocated scalar register. -/
def afterExponentReadout {G : Type u} [Group G] (modulus : Nat)
    (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (after modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (after modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  afterExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit problem)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Framing

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
    UnitaryCircuit layout.register :=
  .identity layout.register layout.identities layout.identities_nodup

private theorem readoutAuxiliaryDisjoint (width count : Nat) :
    List.Disjoint (InputPreparation.auxiliaryLayout width).identities
      (before width count).physicalIdx :=
  ContextUnion.preparation_wires_union InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (InversePreparation.auxiliary_fresh width)
    (InversePreparation.auxiliary_disjoint width) (auxiliary_disjoint width count)

private theorem readoutCellsPhysical (width count : Nat) :
    (withCells width count).physicalIdx =
      (InputPreparation.auxiliaryLayout width).identities ++ (before width count).physicalIdx := by
  rw [withCells, before, RuntimeCtx.physicalIdx_disjointUnion,
    RuntimeCtx.physicalIdx_disjointUnion]
  rw [NumeratorMeasurement.context_physical]
  change ((InputPreparation.auxiliaryLayout width).wires ++
    (InversePreparation.before width).quantumWires).map QuantumWire.identity ++
      (exponents width count).physicalIdx = _
  rw [List.map_append, ← layout_identities_eq_map_wires, List.append_assoc]
  rfl

private theorem readoutAuxiliaryMerge (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    PhysicalLayout.DisjointMerge
      (readoutIdentity (InputPreparation.auxiliaryLayout modulus.size)).physical_idx
      (beforeExponentProgram modulus exponentWidth program physical).physical_idx := by
  refine ⟨(InputPreparation.auxiliaryLayout modulus.size).identities_nodup,
    (beforeExponentProgram modulus exponentWidth program physical).physical_idx_nodup, ?_⟩
  rw [beforeExponentProgram_physical]
  exact readoutAuxiliaryDisjoint modulus.size (2 * exponentWidth)

private def readoutAuxiliaryProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    UnitaryCircuit (Register.prod (InputPreparation.auxiliaryLayout modulus.size).register
      (before modulus.size (2 * exponentWidth)).register) :=
  UnitaryCircuit.tensor (readoutIdentity (InputPreparation.auxiliaryLayout modulus.size))
    (beforeExponentProgram modulus exponentWidth program physical)
    (readoutAuxiliaryMerge modulus exponentWidth program physical)

private theorem readoutAuxiliaryProgram_physical (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (readoutAuxiliaryProgram modulus exponentWidth program physical).physical_idx =
      (withCells modulus.size (2 * exponentWidth)).physicalIdx := by
  change (InputPreparation.auxiliaryLayout modulus.size).identities ++
    (beforeExponentProgram modulus exponentWidth program physical).physical_idx = _
  rw [beforeExponentProgram_physical, readoutCellsPhysical]

private theorem readoutSelectorMerge (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    PhysicalLayout.DisjointMerge
      (readoutIdentity (indexedLayout modulus.size (2 * exponentWidth))).physical_idx
      (readoutAuxiliaryProgram modulus exponentWidth program physical).physical_idx := by
  refine ⟨(indexedLayout modulus.size (2 * exponentWidth)).identities_nodup,
    (readoutAuxiliaryProgram modulus exponentWidth program physical).physical_idx_nodup, ?_⟩
  rw [readoutAuxiliaryProgram_physical]
  exact selector_disjoint modulus.size (2 * exponentWidth)

/-- The original exponent gates act beside identity on every actual allocated work coordinate. -/
def afterExponentProgram (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    UnitaryCircuit (after modulus.size (2 * exponentWidth)).register :=
  UnitaryCircuit.reindex (initializedAssembly modulus (2 * exponentWidth))
    (UnitaryCircuit.tensor (readoutIdentity (indexedLayout modulus.size (2 * exponentWidth)))
      (readoutAuxiliaryProgram modulus exponentWidth program physical)
      (readoutSelectorMerge modulus exponentWidth program physical))

/-- The actual readout program occupies exactly the already allocated complete physical context. -/
theorem afterExponentProgram_physical (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (afterExponentProgram modulus exponentWidth program physical).physical_idx =
      (after modulus.size (2 * exponentWidth)).physicalIdx := by
  change (indexedLayout modulus.size (2 * exponentWidth)).identities ++
    (readoutAuxiliaryProgram modulus exponentWidth program physical).physical_idx = _
  rw [readoutAuxiliaryProgram_physical]
  change (indexedLayout modulus.size (2 * exponentWidth)).identities ++
    (withCells modulus.size (2 * exponentWidth)).physicalIdx =
      ((indexedLayout modulus.size (2 * exponentWidth)).wires ++
        (withCells modulus.size (2 * exponentWidth)).quantumWires).map QuantumWire.identity
  rw [List.map_append, ← layout_identities_eq_map_wires]
  rfl

/-- Every selector and auxiliary label is retained in the actual complete matrix. -/
theorem afterExponentProgram_assembly_entry (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (row column : (indexedLayout modulus.size (2 * exponentWidth)).register.Index ×
      (InputPreparation.auxiliaryLayout modulus.size).register.Index ×
        (before modulus.size (2 * exponentWidth)).register.Index) :
    (afterExponentProgram modulus exponentWidth program physical).matrix
      (initializedAssembly modulus (2 * exponentWidth) row)
      (initializedAssembly modulus (2 * exponentWidth) column) =
      (if row.1 = column.1 then 1 else 0) *
        ((if row.2.1 = column.2.1 then 1 else 0) *
          (beforeExponentProgram modulus exponentWidth program physical).matrix
            row.2.2 column.2.2) := by
  change (UnitaryOperator.prodTensor
    (1 : UnitaryOperator (indexedLayout modulus.size (2 * exponentWidth)).register)
    (UnitaryOperator.prodTensor
      (1 : UnitaryOperator (InputPreparation.auxiliaryLayout modulus.size).register)
      (beforeExponentProgram modulus exponentWidth program physical).matrix))
      ((initializedAssembly modulus (2 * exponentWidth)).symm
        (initializedAssembly modulus (2 * exponentWidth) row))
      ((initializedAssembly modulus (2 * exponentWidth)).symm
        (initializedAssembly modulus (2 * exponentWidth) column)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    UnitaryOperator.prodTensor_apply, UnitaryOperator.prodTensor_apply]
  rfl

/-- The complete allocated frame adds no native event to the original exponent code. -/
theorem afterExponentProgram_trace (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    (afterExponentProgram modulus exponentWidth program physical).eventTrace =
      program.eventTrace := by
  change [] ++ ([] ++ (beforeExponentProgram modulus exponentWidth program physical).eventTrace) = _
  rw [List.nil_append, List.nil_append, beforeExponentProgram_trace]

/-- The actual original exponent program executes on the complete allocated scalar context. -/
def afterExponentCircuit (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth)) :
    Circuit (after modulus.size (2 * exponentWidth))
      (after modulus.size (2 * exponentWidth)) :=
  .unitary (afterExponentProgram modulus exponentWidth program physical)
    (afterExponentProgram_physical modulus exponentWidth program physical)

/-- Actual allocated-context execution retains the full quantum-reference density. -/
theorem afterExponentCircuit_density (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (after modulus.size (2 * exponentWidth)) Reference H) :
    ((afterExponentCircuit modulus exponentWidth program physical).execute
      Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program physical).matrix
          (1 : UnitaryOperator Reference)) state.quantumMarginal :=
  Circuit.unitary_jointDensity (afterExponentProgram modulus exponentWidth program physical)
    (afterExponentProgram_physical modulus exponentWidth program physical) state

/-- Actual readout framing retains the exact original native event cost. -/
theorem afterExponentCircuit_cost (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (path : (afterExponentCircuit modulus exponentWidth program physical).Path) :
    (afterExponentCircuit modulus exponentWidth program physical).resourcePool path =
      program.eventCost := by
  change ResourcePool.ofList
    (afterExponentProgram modulus exponentWidth program physical).eventTrace = _
  rw [afterExponentProgram_trace]
  exact UnitaryCircuit.ofList_eventTrace_eq_eventCost program

/-- Every native duration assignment gives the original program depth on the allocated context. -/
theorem afterExponentCircuit_depth (modulus exponentWidth : Nat)
    (program : UnitaryCircuit (Qubits (exponentWidth + exponentWidth)))
    (physical : program.physical_idx = List.range (exponentWidth + exponentWidth))
    (duration : Resource.Event .quantum → Nat)
    (path : (afterExponentCircuit modulus exponentWidth program physical).Path) :
    (afterExponentCircuit modulus exponentWidth program physical).depth duration path =
      program.evaluatedEventDepth duration := by
  change max 0 (max 0
    ((beforeExponentProgram modulus exponentWidth program physical).evaluatedEventDepth
      duration)) = _
  rw [Nat.zero_max, Nat.zero_max]
  exact beforeExponentCircuit_depth modulus exponentWidth program physical duration ()

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
    Circuit (after modulus.size (2 * FiniteCyclicDLP.orderWidth problem))
      (after modulus.size (2 * FiniteCyclicDLP.orderWidth problem)) :=
  afterExponentCircuit modulus (FiniteCyclicDLP.orderWidth problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit problem)
    (FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit_physical_idx problem)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

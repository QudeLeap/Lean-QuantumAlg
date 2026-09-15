/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Readout
import all QuantumAlg.Core.Execution.Measurement.Readout.Effect
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual terminal exponent cells and measurements

Exactly one fresh finite-two cell is allocated for each original exponent
wire. The existing retained-cell allocator preserves the complete quantum
state and every physical wire. Actual sequential Z instructions then write
those cells in the original paired big-endian order. The event law reads only
their stored results and retains arbitrary older storage and reference states.

The terminal allocation charges the real finite classical space. Each
requested bit contributes one native Z measurement, including zero bits.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation

/-- Fresh terminal finite-two cells extend the actual complete allocated scalar context. -/
def exponentMeasurementContext (modulus exponentWidth : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)

/-- The unchanged original exponent positions pass through the actual classical allocation. -/
def exponentMeasurementWires (modulus exponentWidth : Nat) (index : Fin (2 * exponentWidth)) :
    Fin (exponentMeasurementContext modulus exponentWidth).systemCount :=
  MeasurementCells.wireEquiv (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)
    (afterExponentWires modulus exponentWidth index)

/-- Each terminal system retains its original identity and dimension after allocating cells. -/
theorem exponentMeasurementWires_wire (modulus exponentWidth : Nat)
    (index : Fin (2 * exponentWidth)) :
    (exponentMeasurementContext modulus exponentWidth).quantumLayout.wire
      (exponentMeasurementWires modulus exponentWidth index) =
      QuantumWire.mk (MeasuredUncompute.InPlaceControlled.frameWidth modulus.size +
        index.val) 2 :=
  (MeasurementCells.wireEquiv_preserved _ 2 (2 * exponentWidth)
    (afterExponentWires modulus exponentWidth index)).trans
      (afterExponentWires_wire modulus exponentWidth index)

/-- The actual terminal wires satisfy the qubit requirement of retained Z readout. -/
theorem exponentMeasurementWires_qubits (modulus exponentWidth : Nat)
    (index : Fin (2 * exponentWidth)) :
    ((exponentMeasurementContext modulus exponentWidth).quantumLayout.wire
      (exponentMeasurementWires modulus exponentWidth index)).dimension = 2 :=
  congrArg QuantumWire.dimension (exponentMeasurementWires_wire modulus exponentWidth index)

/-- Every original exponent bit names a different actual measured physical system. -/
theorem exponentMeasurementWires_injective (modulus exponentWidth : Nat) :
    Function.Injective (exponentMeasurementWires modulus exponentWidth) :=
  (MeasurementCells.wireEquiv _ 2 (2 * exponentWidth)).injective.comp
    (afterExponentWires_injective modulus exponentWidth)

/-- Original exponent values pass through classical allocation without encoding changes. -/
theorem exponentMeasurementWires_value (modulus exponentWidth : Nat)
    (value : (after modulus.size (2 * exponentWidth)).register.Index)
    (index : Fin (2 * exponentWidth)) :
    (MeasurementCells.basisEquiv (after modulus.size (2 * exponentWidth)) 2
      (2 * exponentWidth) value (exponentMeasurementWires modulus exponentWidth index)).val =
      (value (afterExponentWires modulus exponentWidth index)).val :=
  MeasurementCells.basisEquiv_value _ 2 (2 * exponentWidth) value
    (afterExponentWires modulus exponentWidth index)

/-- Each original exponent index has its own actual writable finite result cell. -/
def exponentMeasurementCells (modulus exponentWidth : Nat) :
    Fin (2 * exponentWidth) →
      CWriteRef (exponentMeasurementContext modulus exponentWidth) (.finite 2) :=
  MeasurementCells.reference (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)

/-- The complete terminal result cannot overwrite another indexed result cell. -/
theorem exponentMeasurementCells_distinct (modulus exponentWidth : Nat) :
    Function.Injective fun index => (exponentMeasurementCells modulus exponentWidth index).key :=
  MeasurementCells.reference_key_injective _ 2 (2 * exponentWidth)

/-- Every result cell is created by the existing actual retained-storage instruction. -/
def exponentMeasurementAllocate (modulus exponentWidth : Nat) :
    Circuit (after modulus.size (2 * exponentWidth))
      (exponentMeasurementContext modulus exponentWidth) :=
  MeasurementCells.allocate (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)

/-- Actual terminal classical allocation preserves the full quantum-reference density. -/
theorem exponentMeasurementAllocate_density (modulus exponentWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after modulus.size (2 * exponentWidth)) Reference History) :
    ((exponentMeasurementAllocate modulus exponentWidth).execute
      Reference state).quantumMarginal =
      state.quantumMarginal.reindex
        (MeasurementCells.jointBasisEquiv _ 2 (2 * exponentWidth) Reference) :=
  MeasurementCells.allocate_quantumMarginal _ 2 (2 * exponentWidth) state

/-- Terminal cell allocation preserves every physical quantum identity in its existing order. -/
theorem exponentMeasurementContext_physical (modulus exponentWidth : Nat) :
    (exponentMeasurementContext modulus exponentWidth).physicalIdx =
      (after modulus.size (2 * exponentWidth)).physicalIdx :=
  MeasurementCells.context_physicalIdx _ 2 (2 * exponentWidth)

/-- The terminal classical result contributes its actual finite storage to resident space. -/
theorem exponentMeasurementContext_resident (modulus exponentWidth : Nat) :
    (exponentMeasurementContext modulus exponentWidth).residentSpace =
      (2 * exponentWidth) • SpacePool.ofShape (.finite 2) +
        (after modulus.size (2 * exponentWidth)).residentSpace :=
  MeasurementCells.context_residentSpace _ 2 (2 * exponentWidth)

/-- The same actual terminal result cells are charged as retained auxiliary space. -/
theorem exponentMeasurementContext_auxiliary (modulus exponentWidth : Nat) :
    (exponentMeasurementContext modulus exponentWidth).auxiliarySpace =
      (2 * exponentWidth) • SpacePool.ofShape (.finite 2) +
        (after modulus.size (2 * exponentWidth)).auxiliarySpace :=
  MeasurementCells.context_auxiliarySpace _ 2 (2 * exponentWidth)

/-- Every exponent wire is measured by the existing sequential Z interpreter. -/
def exponentMeasurements (modulus exponentWidth : Nat) :
    Circuit (exponentMeasurementContext modulus exponentWidth)
      (exponentMeasurementContext modulus exponentWidth) :=
  .measurementSequence (QubitReadouts.readouts
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth))

/-- Actual terminal execution allocates its own result cells before writing every measurement. -/
def exponentMeasurementCircuit (modulus exponentWidth : Nat) :
    Circuit (after modulus.size (2 * exponentWidth))
      (exponentMeasurementContext modulus exponentWidth) :=
  .seq (exponentMeasurementAllocate modulus exponentWidth)
    (exponentMeasurements modulus exponentWidth)

/-- The actual terminal program charges exactly one native measurement per original bit. -/
theorem exponentMeasurementCircuit_cost (modulus exponentWidth : Nat)
    (path : (exponentMeasurementCircuit modulus exponentWidth).Path) :
    (exponentMeasurementCircuit modulus exponentWidth).resourcePool path =
      (2 * exponentWidth) • ResourcePool.singleton (Circuit.zEvent 2) := by
  change (MeasurementCells.allocate (after modulus.size (2 * exponentWidth)) 2
    (2 * exponentWidth)).Path × (exponentMeasurements modulus exponentWidth).Path at path
  change ResourcePool.ofList
    ((MeasurementCells.allocate _ 2 (2 * exponentWidth)).eventTrace path.1 ++
      (exponentMeasurements modulus exponentWidth).eventTrace path.2) = _
  rw [MeasurementCells.allocate_eventTrace, List.nil_append]
  exact QubitReadouts.measurement_resources _ _ _ path.2

/-- Unit-duration depth counts precisely the actual sequential terminal Z instructions. -/
theorem exponentMeasurementCircuit_unitDepth (modulus exponentWidth : Nat)
    (path : (exponentMeasurementCircuit modulus exponentWidth).Path) :
    (exponentMeasurementCircuit modulus exponentWidth).depth (fun _ => 1) path =
      2 * exponentWidth := by
  change (MeasurementCells.allocate (after modulus.size (2 * exponentWidth)) 2
    (2 * exponentWidth)).Path × (exponentMeasurements modulus exponentWidth).Path at path
  change (MeasurementCells.allocate _ 2 (2 * exponentWidth)).depth (fun _ => 1) path.1 +
    (exponentMeasurements modulus exponentWidth).depth (fun _ => 1) path.2 = _
  rw [MeasurementCells.allocate_depth, zero_add]
  exact (Circuit.measurementSequence_unitDepth _ path.2).trans List.length_ofFn

/-- Actual terminal events read only freshly written cells and retain the whole input marginal. -/
theorem exponentMeasurementCircuit_eventWeight (modulus exponentWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after modulus.size (2 * exponentWidth)) Reference History)
    (event : (Fin (2 * exponentWidth) → Bool) → Bool) :
    ((exponentMeasurementCircuit modulus exponentWidth).execute Reference state).effectWeight
        (fun record => if event (QubitReadouts.mask (record.1.read
          (QubitReadouts.input (exponentMeasurementCells modulus exponentWidth)))) = true then
            Effect.one (Register.prod
              (exponentMeasurementContext modulus exponentWidth).register Reference)
          else Effect.zero (Register.prod
            (exponentMeasurementContext modulus exponentWidth).register Reference)) =
      (QubitReadouts.eventEffect (exponentMeasurementWires modulus exponentWidth)
        event Reference).weight
          (state.quantumMarginal.reindex
            (MeasurementCells.jointBasisEquiv _ 2 (2 * exponentWidth) Reference)) := by
  rw [exponentMeasurementCircuit, Circuit.execute_seq, State.effectWeight_mapHistory]
  have observed := QubitReadouts.measurement_eventEffectWeight
    (exponentMeasurementWires modulus exponentWidth)
    (exponentMeasurementWires_qubits modulus exponentWidth)
    (exponentMeasurementCells modulus exponentWidth)
    (exponentMeasurementCells_distinct modulus exponentWidth)
    ((exponentMeasurementAllocate modulus exponentWidth).execute Reference state) event
  exact observed.trans (congrArg
    (QubitReadouts.eventEffect (exponentMeasurementWires modulus exponentWidth)
      event Reference).weight (exponentMeasurementAllocate_density modulus exponentWidth state))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

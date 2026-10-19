/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Model
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# One Simon bank and fixed stored sample slots

The sample slots, single original two-register bank and finite measurement
cells are actual live entries. The slots retain the chronological sample
order. Structural lifting keeps every previous operand and wire identity;
it neither copies a value nor allocates another quantum register.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

/-- Exactly the original two-register physical layout. -/
@[implicit_reducible]
def bankLayout (n : Nat) : QuantumLayout (2 * n) :=
  (SimonsProblem.layout n).toQuantum

/-- The original binary zero label, on those same physical wires. -/
def preparation (n : Nat) : BasisPreparation (bankLayout n) :=
  ⟨(SimonsProblem.layout n).basisEquiv.symm 0⟩

/-- Allocate one retained bit-string slot for every fixed sample index. -/
@[implicit_reducible]
def slots (base : RuntimeCtx .quantum) (n : Nat) : Nat → RuntimeCtx .quantum
  | 0 => base
  | count + 1 =>
      (slots base n count).addRetained (slots base n count).canonicalFreshKey
        (.bits n) (slots base n count).canonicalFreshKey_fresh

/-- Index zero is the newest allocated slot; execution writes indices in ascending order. -/
@[implicit_reducible]
def slotRef (base : RuntimeCtx .quantum) (n : Nat) :
    (count : Nat) → Fin count → CWriteRef (slots base n count) (.bits n)
  | 0, index => Fin.elim0 index
  | count + 1, index =>
      Fin.cases
        (CWriteRef.retainedHead (slots base n count)
          (slots base n count).canonicalFreshKey (.bits n)
          (slots base n count).canonicalFreshKey_fresh)
        (fun previous => (slotRef base n count previous).underRetained
          (slots base n count).canonicalFreshKey (.bits n)
          (slots base n count).canonicalFreshKey_fresh) index

/-- Earlier structural reads refer to the same cells beneath the actual sample slots. -/
def slotsInput {base : RuntimeCtx .quantum} {shape : CShape} (n : Nat)
    (input : CInputRef base shape) : (count : Nat) → CInputRef (slots base n count) shape
  | 0 => input
  | count + 1 =>
      (slotsInput n input count).underRetained (slots base n count).canonicalFreshKey
        (.bits n) (slots base n count).canonicalFreshKey_fresh

/-- The retained sample slots contribute no quantum wire. -/
lemma nativeSimon_slots_wires (base : RuntimeCtx .quantum) (n count : Nat) :
    (slots base n count).quantumWires = base.quantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [slots, RuntimeCtx.quantumWires_addRetained] using ih

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

include noQuantum in
private lemma allocationDisjoint :
    List.Disjoint (bankLayout n).identities (slots base n count).physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, nativeSimon_slots_wires, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- One owned quantum bank is added after the fixed sample storage. -/
def bankContext : RuntimeCtx .quantum :=
  (slots base n count).addOwnedLayout (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)

/-- The same finite measurement cells are overwritten in every round. -/
def context : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum n count) 2 n

/-- Each actual measured qubit writes to its own finite two-valued cell. -/
def cells (index : Fin n) : CWriteRef (context base noQuantum n count) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum n count) 2 n index

/-- The allocated sample slot keeps its writable role beneath the owned bank. -/
def bankSlot (index : Fin count) : CWriteRef (bankContext base noQuantum n count) (.bits n) where
  toCStorageRef := (slotRef base n count index).toCStorageRef.underOwnedLayout
    (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
  writable := (slotRef base n count index).writable

/-- Writable access to the actual sample slot after all measurement cells are retained. -/
def sampleRef (index : Fin count) : CWriteRef (context base noQuantum n count) (.bits n) :=
  MeasurementCells.liftWrite 2 (bankSlot base noQuantum n count index) n

/-- The reducer receives exactly the stored rows, in their sample-index order. -/
def samplesInput : CInputRef (context base noQuantum n count) (.fixedVector count (.bits n)) :=
  .fixedVector fun index => .storage (sampleRef base noQuantum n count index).toCStorageRef

/-- Every original caller operand remains structurally readable under all real allocations. -/
def liftInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum n count) shape :=
  MeasurementCells.liftInput 2
    ((slotsInput n input count).underOwnedLayout (slots base n count).canonicalFreshKey
      (bankLayout n) (slots base n count).canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum n count)) n

/-- The prepared context contains exactly the original two-register bank. -/
lemma nativeSimon_bankContext_wires :
    (bankContext base noQuantum n count).quantumWires = (bankLayout n).wires := by
  change (bankLayout n).wires ++ (slots base n count).quantumWires = _
  rw [nativeSimon_slots_wires, noQuantum, List.append_nil]

/-- Classical readout cells add no physical system or wire permutation. -/
lemma nativeSimon_context_wires :
    (context base noQuantum n count).quantumWires = (bankLayout n).wires := by
  rw [context, MeasurementCells.context_quantumWires]
  exact nativeSimon_bankContext_wires base noQuantum n count

end

noncomputable section

variable {ctx : RuntimeCtx .quantum} (n : Nat)
  (sameWires : ctx.quantumWires = (bankLayout n).wires)

include sameWires in
private lemma layoutWires : (bankLayout n).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The source position denotes the same physical wire in the live runtime context. -/
def wireEquiv : Fin (2 * n) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (bankLayout n) ctx.quantumLayout (layoutWires n sameWires)

/-- Both identity and dimension are preserved at each source wire position. -/
lemma nativeSimon_wire_preserved (wire : Fin (2 * n)) :
    ctx.quantumLayout.wire (wireEquiv n sameWires wire) = (bankLayout n).wire wire :=
  Execution.wireAtCorrespondingPosition
    (bankLayout n) ctx.quantumLayout (layoutWires n sameWires) wire

include sameWires in
/-- Every live quantum system belongs to the original qubit bank. -/
lemma nativeSimon_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv n sameWires).surjective wire
  simpa only [bankLayout, QubitLayout.toQuantum_wire] using
    congrArg QuantumWire.dimension (nativeSimon_wire_preserved n sameWires original)

/-- The original big-endian binary label and the actual wirewise label describe the same basis. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (2 * n)).Index :=
  (Execution.basisOfEqualWires (bankLayout n) ctx.quantumLayout
    (layoutWires n sameWires)).symm.trans (SimonsProblem.layout n).basisEquiv

include sameWires in
/-- Reindexing the source basis leaves every original physical identity unchanged. -/
lemma nativeSimon_physicalIdx :
    ctx.physicalIdx = (SimonsProblem.layout n).systemIdx := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  simp only [bankLayout, QuantumLayout.wires, List.map_ofFn, Function.comp_def,
    QubitLayout.toQuantum_wire, QubitLayout.systemIdx]

/-- Place the supplied original circuit on this same physical bank. -/
def member (sampling : SamplingCircuit n) :
    UnitaryCircuit AlgorithmGate.model (sourceModel n) ctx.quantumLayout :=
  Execution.unitaryOfEqualWires (bankLayout n) ctx.quantumLayout
    (layoutWires n sameWires) sampling.circuit

end

end QuantumAlg.SimonsProblem.FixedSample.Native

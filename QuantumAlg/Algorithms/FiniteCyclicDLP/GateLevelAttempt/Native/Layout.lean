/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# Original three-register bank and retained Fourier readouts

One owned bank contains both original exponent registers and the complete
encoded group workspace. Its preparation sets the exponents to zero
and the workspace to the encoded group identity. The finite readout cells are allocated
once and reused; earlier public classical inputs keep their original keys.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Both original exponent registers are read in their original consecutive order. -/
def sampleWidth (P : KnownOrderProblem G) : Nat :=
  orderWidth P + orderWidth P

/-- The physical bank is exactly the original three-register layout. -/
def bankLayout (P : KnownOrderProblem G) : QuantumLayout (totalQubits P) :=
  (layout P).toQuantumLayout

/-- The original zero-exponent, encoded-identity input in wirewise basis coordinates. -/
def preparation (P : KnownOrderProblem G) (ux : UxAccess P) :
    BasisPreparation (bankLayout P) :=
  ⟨(layout P).binaryIndexEquiv.symm (tripleIndex 0 0 (ux.encode 1))⟩

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G)

include noQuantum in
private theorem allocationDisjoint : List.Disjoint (bankLayout P).identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- One owned bank is added to the original quantum-free caller context. -/
def bankContext : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (bankLayout P) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum P)

/-- The same actual finite cells hold both Fourier outcomes in every round. -/
def context : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum P) 2 (sampleWidth P)

/-- Each measured position writes its own actual two-valued retained cell. -/
def cells (index : Fin (sampleWidth P)) :
    CWriteRef (context base noQuantum P) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum P) 2 (sampleWidth P) index

/-- Recovery reads the original ordered finite outcomes directly from their retained cells. -/
def sampleInput :
    CInputRef (context base noQuantum P) (.fixedVector (sampleWidth P) (.finite 2)) :=
  MeasurementCells.input (bankContext base noQuantum P) 2 (sampleWidth P)

/-- Every incoming classical operand retains its original structural storage reference. -/
def liftInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum P) shape :=
  MeasurementCells.liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey (bankLayout P) base.canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum P)) (sampleWidth P)

/-- Allocation adds exactly the original three-register bank, without a second quantum workspace. -/
theorem nativeFiniteCyclic_bankContext_wires :
    (bankContext base noQuantum P).quantumWires = (bankLayout P).wires := by
  change (bankLayout P).wires ++ base.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- Retaining the classical outcomes preserves every original quantum wire. -/
theorem nativeFiniteCyclic_context_wires :
    (context base noQuantum P).quantumWires = (bankLayout P).wires := by
  rw [context, MeasurementCells.context_quantumWires]
  exact nativeFiniteCyclic_bankContext_wires base noQuantum P

end

noncomputable section

universe u

variable {G : Type u} [Group G]
  {ctx : RuntimeCtx .quantum} (P : KnownOrderProblem G)
  (sameWires : ctx.quantumWires = (bankLayout P).wires)

include sameWires in
private theorem layoutWires : (bankLayout P).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- Original circuit positions identify exactly the same live physical systems. -/
def wireEquiv : Fin (totalQubits P) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (bankLayout P) ctx.quantumLayout (layoutWires P sameWires)

/-- Both physical identity and dimension survive the layout correspondence. -/
theorem nativeFiniteCyclic_wire_preserved (wire : Fin (totalQubits P)) :
    ctx.quantumLayout.wire (wireEquiv P sameWires wire) = (bankLayout P).wire wire :=
  Execution.wireAtCorrespondingPosition
    (bankLayout P) ctx.quantumLayout (layoutWires P sameWires) wire

include sameWires in
/-- Every live system of the original three-register bank is a qubit. -/
theorem nativeFiniteCyclic_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv P sameWires).surjective wire
  exact congrArg QuantumWire.dimension (nativeFiniteCyclic_wire_preserved P sameWires original)

/-- Wirewise runtime labels and the original circuit's binary labels describe the same basis. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (totalQubits P)).Index :=
  (Execution.basisOfEqualWires (bankLayout P) ctx.quantumLayout
    (layoutWires P sameWires)).symm.trans (layout P).binaryIndexEquiv

include sameWires in
/-- This index correspondence performs no physical permutation of the original circuit wires. -/
theorem nativeFiniteCyclic_physicalIdx : ctx.physicalIdx = (layout P).systemIdx := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (bankLayout P)).symm.trans
    (layout P).toQuantumLayout_identities

end

end GateLevelAttempt.Native
end QuantumAlg.FiniteCyclicDLP.Canonical

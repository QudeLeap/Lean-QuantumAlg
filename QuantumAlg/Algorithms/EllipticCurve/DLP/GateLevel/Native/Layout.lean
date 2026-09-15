/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Unitary
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Context.Layout

/-!
# The original intrinsic ECDLP bank and its retained Fourier readouts

One owned bank contains both original exponent registers and the complete
identity-inclusive point encoding. Its preparation sets the exponents to zero
and the point to the group identity. The finite readout cells are allocated
once and reused; earlier public classical inputs keep their original keys.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Both original exponent registers are read in their original consecutive order. -/
def sampleWidth (I : ECDLPInstance E) : Nat :=
  FiniteCyclicDLP.orderWidth (problem I) + FiniteCyclicDLP.orderWidth (problem I)

/-- The physical bank is exactly the original identity-inclusive ECDLP layout. -/
def bankLayout (I : ECDLPInstance E) : QuantumLayout (Layout.totalQubits I) :=
  (qubitLayout I).toQuantumLayout

/-- The original zero-exponent, identity-point input in wirewise basis coordinates. -/
def preparation (I : ECDLPInstance E) : BasisPreparation (bankLayout I) :=
  ⟨(qubitLayout I).binaryIndexEquiv.symm (basisIndex I 0 0 1)⟩

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (I : ECDLPInstance E)

include noQuantum in
private theorem allocationDisjoint : List.Disjoint (bankLayout I).identities base.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- One owned bank is added to the original quantum-free caller context. -/
def bankContext : RuntimeCtx .quantum :=
  base.addOwnedLayout base.canonicalFreshKey (bankLayout I) base.canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum I)

/-- The same actual finite cells hold both Fourier outcomes in every round. -/
def context : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum I) 2 (sampleWidth I)

/-- Each measured position writes its own actual two-valued retained cell. -/
def cells (index : Fin (sampleWidth I)) :
    CWriteRef (context base noQuantum I) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum I) 2 (sampleWidth I) index

/-- Recovery reads the original ordered finite outcomes directly from their retained cells. -/
def sampleInput :
    CInputRef (context base noQuantum I) (.fixedVector (sampleWidth I) (.finite 2)) :=
  MeasurementCells.input (bankContext base noQuantum I) 2 (sampleWidth I)

/-- Every incoming classical operand retains its original structural storage reference. -/
def liftInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base noQuantum I) shape :=
  MeasurementCells.liftInput 2
    (input.underOwnedLayout base.canonicalFreshKey (bankLayout I) base.canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum I)) (sampleWidth I)

/-- Allocation adds exactly the original intrinsic bank, without a second quantum workspace. -/
theorem nativeECDLP_bankContext_wires :
    (bankContext base noQuantum I).quantumWires = (bankLayout I).wires := by
  change (bankLayout I).wires ++ base.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- Retaining the classical outcomes preserves every original quantum wire. -/
theorem nativeECDLP_context_wires :
    (context base noQuantum I).quantumWires = (bankLayout I).wires := by
  rw [context, MeasurementCells.context_quantumWires]
  exact nativeECDLP_bankContext_wires base noQuantum I

end

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  {ctx : RuntimeCtx .quantum} (I : ECDLPInstance E)
  (sameWires : ctx.quantumWires = (bankLayout I).wires)

include sameWires in
private theorem layoutWires : (bankLayout I).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- Original circuit positions identify exactly the same live physical systems. -/
def wireEquiv : Fin (Layout.totalQubits I) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (bankLayout I) ctx.quantumLayout (layoutWires I sameWires)

/-- Both physical identity and dimension survive the layout correspondence. -/
theorem nativeECDLP_wire_preserved (wire : Fin (Layout.totalQubits I)) :
    ctx.quantumLayout.wire (wireEquiv I sameWires wire) = (bankLayout I).wire wire :=
  Execution.wireAtCorrespondingPosition
    (bankLayout I) ctx.quantumLayout (layoutWires I sameWires) wire

include sameWires in
/-- Every live system of the original intrinsic bank is a qubit. -/
theorem nativeECDLP_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv I sameWires).surjective wire
  exact congrArg QuantumWire.dimension (nativeECDLP_wire_preserved I sameWires original)

/-- Wirewise runtime labels and the original circuit's binary labels describe the same basis. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (Layout.totalQubits I)).Index :=
  (Execution.basisOfEqualWires (bankLayout I) ctx.quantumLayout
    (layoutWires I sameWires)).symm.trans (qubitLayout I).binaryIndexEquiv

include sameWires in
/-- This index correspondence performs no physical permutation of the original circuit wires. -/
theorem nativeECDLP_physicalIdx : ctx.physicalIdx = (qubitLayout I).systemIdx := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (bankLayout I)).symm.trans
    (qubitLayout I).toQuantumLayout_identities

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

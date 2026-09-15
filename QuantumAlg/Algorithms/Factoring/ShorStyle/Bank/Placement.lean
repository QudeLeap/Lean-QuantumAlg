/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Native Shor members and seed loading on the existing bank

Equality of the complete ordered wire records identifies the actual bank
after any classical retention or scratch scopes. The selected compiled
member and shared constant-X loader use precisely those coordinates. No
quantum system is allocated by either operation, and physical placement
does not add or relabel any native event.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement

noncomputable section

open NativeQuantum

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout N).wires)

include sameWires in
private theorem layoutWires : (runtimeLayout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The whole-bank wire correspondence preserves actual physical order. -/
def wireEquiv : Fin (totalQubits N) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (runtimeLayout N) ctx.quantumLayout (layoutWires N sameWires)

/-- Each corresponding position retains its complete physical identity and dimension. -/
theorem wire_preserved (index : Fin (totalQubits N)) :
    ctx.quantumLayout.wire (wireEquiv N sameWires index) = (runtimeLayout N).wire index :=
  Execution.wireAtCorrespondingPosition (runtimeLayout N) ctx.quantumLayout
    (layoutWires N sameWires) index

include sameWires in
/-- All dimensions needed for full-bank reset follow from the actual ordered wire equality. -/
theorem qubits (wire : Fin ctx.systemCount) : (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨source, rfl⟩ := (wireEquiv N sameWires).surjective wire
  exact (congrArg QuantumWire.dimension (wire_preserved N sameWires source)).trans
    (runtimeLayout_dimension N source)

/-- The binary label describes precisely the same complete actual register. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (totalQubits N)).Index :=
  (Execution.basisOfEqualWires (runtimeLayout N) ctx.quantumLayout
    (layoutWires N sameWires)).symm.trans
      (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv

include sameWires in
/-- Every live physical identity belongs to the one unchanged bank. -/
theorem physicalIdx : ctx.physicalIdx = List.range (totalQubits N) := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (runtimeLayout N)).symm.trans
    (runtimeLayout_identities N)

/-- The selected compiled modular-power member acts on the actual bank's basis coordinates. -/
def memberProgram (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    UnitaryCircuit ctx.register :=
  UnitaryCircuit.reindex (basisEquiv N sameWires).symm (NativeQuantum.program parameter)

/-- The shared actual X sequence reloads the source seed after a proved bank reset. -/
def reloadProgram : UnitaryCircuit ctx.register :=
  UnitaryCircuit.reindex (basisEquiv N sameWires).symm
    (EncodedBit.Word.BasisLoad.program (seedLabel N))

/-- The actual selected member covers exactly the existing bank. -/
theorem member_physicalIdx (parameter : CShape.Value (ParameterShape (modulusBits N))) :
    (memberProgram N sameWires parameter).physical_idx = ctx.physicalIdx :=
  (program_physicalIdx parameter).trans (physicalIdx N sameWires).symm

/-- Reload uses the same complete register and adds no system. -/
theorem reload_physicalIdx : (reloadProgram N sameWires).physical_idx = ctx.physicalIdx :=
  (EncodedBit.Word.BasisLoad.basisLoad_physicalIdx (seedLabel N)).trans
    (physicalIdx N sameWires).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement

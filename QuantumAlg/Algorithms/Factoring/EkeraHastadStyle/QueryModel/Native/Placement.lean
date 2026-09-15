/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# The original XOR member on its actual physical bank

Equal ordered wire records transport the source circuit to the runtime
register. The original component owns the sealed query and its XOR operator;
this placement adds no unitary, classical computation, or event label.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

noncomputable section

/-- The known modulus determines its original injective residue encoding. -/
def encoding {N : Nat} (input : Input N) : ShortDLP.UnitEncoding N (parameters N).workspaceBits :=
  ShortDLP.UnitEncoding.ofResidueEncoding
    { modulus_pos := input.modulus_pos
      register_fits := input.samplerInput.register_fits }

variable {ctx : RuntimeCtx .quantum} (N : Nat) (sameWires : ctx.quantumWires = (layout N).wires)

include sameWires in
private theorem layoutWires : (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- Corresponding positions preserve complete wire identities and dimensions. -/
def wireEquiv : Fin (ShortDLP.totalQubits (parameters N)) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)

/-- The actual wire at each source position retains its physical identity and dimension. -/
theorem nativeOracle_wire_preserved (wire : Fin (ShortDLP.totalQubits (parameters N))) :
    ctx.quantumLayout.wire (wireEquiv N sameWires wire) = (layout N).wire wire :=
  Execution.wireAtCorrespondingPosition (layout N) ctx.quantumLayout (layoutWires N sameWires) wire

include sameWires in
/-- Every actual bank wire has dimension two. -/
theorem nativeOracle_context_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨original, rfl⟩ := (wireEquiv N sameWires).surjective wire
  exact congrArg QuantumWire.dimension (nativeOracle_wire_preserved N sameWires original)

/-- Binary source labels identify the same actual ordered physical wires. -/
def basisEquiv : ctx.register.Index ≃ (Qubits (ShortDLP.totalQubits (parameters N))).Index :=
  (Execution.basisOfEqualWires (layout N) ctx.quantumLayout (layoutWires N sameWires)).symm.trans
    (ShortDLP.layout (parameters N)).binaryIndexEquiv

include sameWires in
/-- The runtime bank has exactly the consecutive source identities. -/
theorem nativeOracle_physicalIdx :
    ctx.physicalIdx = List.range (ShortDLP.totalQubits (parameters N)) := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (layout N)).symm.trans
    (ShortDLP.layout_systemIdx (parameters N))

/-- One complete original prepare-query-readout member, at the actual stored parameter. -/
def member (input : Input N) (parameter : (ParameterShape N).Value) : UnitaryCircuit ctx.register :=
  UnitaryCircuit.reindex (basisEquiv N sameWires).symm
    (ShortDLP.circuit (encoding input) (parameterUnit parameter) (parameterTarget parameter))

/-- The placed original member covers the actual complete bank. -/
theorem nativeOracle_member_physicalIdx (input : Input N)
    (parameter : (ParameterShape N).Value) :
    (member N sameWires input parameter).physical_idx = ctx.physicalIdx :=
  (ShortDLP.circuit_physical_idx (encoding input)
    (parameterUnit parameter) (parameterTarget parameter)).trans
      (nativeOracle_physicalIdx N sameWires).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

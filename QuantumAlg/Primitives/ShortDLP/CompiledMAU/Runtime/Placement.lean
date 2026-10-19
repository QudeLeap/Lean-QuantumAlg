/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Actual short-DLP operations on the unchanged runtime bank

The complete ordered wire records identify the existing owned bank after any
classical storage additions. The original compiled member and literal reload
are reindexed through that wire correspondence. Neither operation allocates
systems or changes native event coordinates. The equality of wire lists is
an internal placement fact, not a quantum input-state assumption.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

noncomputable section

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

include sameWires in
private lemma layoutWires :
    (runtimeLayout m ell width).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The actual runtime positions are matched to the complete ordered source bank. -/
def wireEquiv : Fin (totalQubits (registerParameters m ell width)) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires)

/-- The correspondence preserves actual physical identity and dimension together. -/
lemma shortDLP_runtimeWire_preserved
    (index : Fin (totalQubits (registerParameters m ell width))) :
    ctx.quantumLayout.wire (wireEquiv m ell width sameWires index) =
      (runtimeLayout m ell width).wire index :=
  Execution.wireAtCorrespondingPosition (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires) index

include sameWires in
/-- All reset dimensions follow the proved layout correspondence. -/
lemma shortDLP_runtimePlacement_qubits (wire : Fin ctx.systemCount) :
    (ctx.quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨source, rfl⟩ := (wireEquiv m ell width sameWires).surjective wire
  exact (congrArg QuantumWire.dimension
    (shortDLP_runtimeWire_preserved m ell width sameWires source)).trans
    (shortDLP_runtimeLayout_dimension m ell width source)

/-- The source's binary labels represent exactly the same ordered runtime systems. -/
def basisEquiv : ctx.register.Index ≃
    (Qubits (totalQubits (registerParameters m ell width))).Index :=
  (Execution.basisOfEqualWires (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires)).symm.trans
      (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv

include sameWires in
/-- Every incoming physical identity is exactly one of the actual source bank identities. -/
lemma shortDLP_runtimePlacement_physicalIdx :
    ctx.physicalIdx = List.range (totalQubits (registerParameters m ell width)) := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (runtimeLayout m ell width)).symm.trans
    (shortDLP_runtimeLayout_identities m ell width)

/-- The actual compiled two-exponentiation member acts on the same runtime bank. -/
def memberProgram (N : Nat) (generator target : (ZMod N)ˣ) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires)
    (compiledCircuit m ell width N generator target)

/-- The actual X reload acts on the same systems after their proved reset. -/
def reloadProgram (N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires)
    (CompiledMAU.reloadProgram m ell width N)

/-- Full-bank placement preserves every actual native and oracle event. -/
lemma shortDLP_runtimeMember_eventTrace (N : Nat) (generator target : (ZMod N)ˣ)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (memberProgram m ell width sameWires N generator target).eventTrace operations services =
      (compiledCircuit m ell width N generator target).eventTrace operations services :=
  Execution.unitaryOfEqualWires_trace _ _ _ _ operations services

/-- The same-bank reload retains its literal X event word, including the empty word. -/
lemma shortDLP_runtimeReload_eventTrace (N : Nat)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (reloadProgram m ell width sameWires N).eventTrace operations services =
      (CompiledMAU.reloadProgram m ell width N).eventTrace operations services :=
  Execution.unitaryOfEqualWires_trace _ _ _ _ operations services

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

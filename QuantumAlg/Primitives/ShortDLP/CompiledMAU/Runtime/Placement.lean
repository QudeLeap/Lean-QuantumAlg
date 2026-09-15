/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Core.Execution.Context.Layout
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
private theorem layoutWires :
    (runtimeLayout m ell width).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The actual runtime positions are matched to the complete ordered source bank. -/
def wireEquiv : Fin (totalQubits (registerParameters m ell width)) ≃ Fin ctx.systemCount :=
  Execution.positionsOfEqualWires (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires)

/-- The correspondence preserves actual physical identity and dimension together. -/
theorem shortDLP_runtimeWire_preserved
    (index : Fin (totalQubits (registerParameters m ell width))) :
    ctx.quantumLayout.wire (wireEquiv m ell width sameWires index) =
      (runtimeLayout m ell width).wire index :=
  Execution.wireAtCorrespondingPosition (runtimeLayout m ell width) ctx.quantumLayout
    (layoutWires m ell width sameWires) index

include sameWires in
/-- All reset dimensions follow the proved layout correspondence. -/
theorem shortDLP_runtimePlacement_qubits (wire : Fin ctx.systemCount) :
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
theorem shortDLP_runtimePlacement_physicalIdx :
    ctx.physicalIdx = List.range (totalQubits (registerParameters m ell width)) := by
  change ctx.quantumWires.map QuantumWire.identity = _
  rw [sameWires]
  exact (layout_identities_eq_map_wires (runtimeLayout m ell width)).symm.trans
    (shortDLP_runtimeLayout_identities m ell width)

/-- The actual compiled two-exponentiation member acts on the same runtime bank. -/
def memberProgram (N : Nat) (generator target : (ZMod N)ˣ) : UnitaryCircuit ctx.register :=
  UnitaryCircuit.reindex (basisEquiv m ell width sameWires).symm
    (compiledCircuit m ell width N generator target)

/-- The actual X reload acts on the same systems after their proved reset. -/
def reloadProgram (N : Nat) : UnitaryCircuit ctx.register :=
  UnitaryCircuit.reindex (basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadProgram m ell width N)

/-- The member's actual unitary constructor covers the complete existing bank. -/
theorem shortDLP_runtimeMember_physicalIdx (N : Nat) (generator target : (ZMod N)ˣ) :
    (memberProgram m ell width sameWires N generator target).physical_idx = ctx.physicalIdx :=
  (compiledCircuit_physical_idx m ell width N generator target).trans
    (shortDLP_runtimePlacement_physicalIdx m ell width sameWires).symm

/-- Reload preserves the same complete bank even when no X gate is needed. -/
theorem shortDLP_runtimeReload_physicalIdx (N : Nat) :
    (reloadProgram m ell width sameWires N).physical_idx = ctx.physicalIdx :=
  (shortDLP_reload_physical_idx m ell width N).trans
    (shortDLP_runtimePlacement_physicalIdx m ell width sameWires).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

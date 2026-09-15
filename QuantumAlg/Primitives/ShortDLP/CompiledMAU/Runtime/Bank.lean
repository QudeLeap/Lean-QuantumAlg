/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Prepare the short-DLP owned bank once around a classical frame

One actual Circuit.prepare adds one owned layout with the source seed. The
old context may contain arbitrary classical values and their reference
correlations, but supplies no quantum system. This is an internal allocation
boundary for the surrounding factoring program, not a condition on later
rounds. Its resulting physical bank remains present during those rounds.

The bank's ordered wire equality and actual owned-layout entry establish its
reset boundary. Later reset and reload instructions do not use this allocation
constructor and do not introduce another bank.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank

noncomputable section

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

include noQuantum in
private theorem input_systemCount : ctx.systemCount = 0 := by
  change ctx.quantumWires.length = 0
  rw [noQuantum]
  rfl

include noQuantum in
private theorem allocationDisjoint (m ell width : Nat) :
    List.Disjoint (runtimeLayout m ell width).identities ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The actual single owned bank, with every original classical entry still live. -/
def context (m ell width : Nat) : RuntimeCtx .quantum :=
  ctx.addOwnedLayout ctx.canonicalFreshKey (runtimeLayout m ell width)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)

/-- The only quantum allocation in this component prepares the actual source seed. -/
def prepare (m ell width N : Nat) : Circuit ctx (context ctx noQuantum m ell width) :=
  .prepare ctx ctx.canonicalFreshKey (runtimeLayout m ell width) ctx.canonicalFreshKey_fresh
    (allocationDisjoint ctx noQuantum m ell width) (seedPreparation m ell width N)

/-- The new live bank has the owned role assigned by the actual preparation constructor. -/
theorem shortDLP_runtimeBank_ownedEntry (m ell width : Nat) :
    RuntimeEntry.ownedLayout ctx.canonicalFreshKey (runtimeLayout m ell width) ∈
      (context ctx noQuantum m ell width).entries :=
  List.Mem.head _

/-- Every physical wire comes from the one actual source bank, with no earlier quantum tail. -/
theorem shortDLP_runtimeBank_quantumWires (m ell width : Nat) :
    (context ctx noQuantum m ell width).quantumWires = (runtimeLayout m ell width).wires := by
  change (runtimeLayout m ell width).wires ++ ctx.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- The source and actual context have identical ordered physical wire records. -/
theorem shortDLP_runtimeBank_layoutWires (m ell width : Nat) :
    (runtimeLayout m ell width).wires =
      (context ctx noQuantum m ell width).quantumLayout.wires :=
  ((context ctx noQuantum m ell width).quantumLayout_wires.trans
    (shortDLP_runtimeBank_quantumWires ctx noQuantum m ell width)).symm

/-- The single actual bank occupies precisely the original short-DLP physical identities. -/
theorem shortDLP_runtimeBank_physicalIdx (m ell width : Nat) :
    (context ctx noQuantum m ell width).physicalIdx =
      List.range (totalQubits (registerParameters m ell width)) := by
  change (context ctx noQuantum m ell width).quantumWires.map QuantumWire.identity = _
  rw [shortDLP_runtimeBank_quantumWires]
  exact (layout_identities_eq_map_wires (runtimeLayout m ell width)).symm.trans
    (shortDLP_runtimeLayout_identities m ell width)

/-- Reset dimensions are internal consequences of the actual owned bank's ordered wires. -/
theorem shortDLP_runtimeBank_qubits (m ell width : Nat)
    (wire : Fin (context ctx noQuantum m ell width).systemCount) :
    ((context ctx noQuantum m ell width).quantumLayout.wire wire).dimension = 2 := by
  let positions := Execution.positionsOfEqualWires (runtimeLayout m ell width)
    (context ctx noQuantum m ell width).quantumLayout
    (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width)
  obtain ⟨source, rfl⟩ := positions.surjective wire
  exact (congrArg QuantumWire.dimension
    (Execution.wireAtCorrespondingPosition (runtimeLayout m ell width)
      (context ctx noQuantum m ell width).quantumLayout
      (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width) source)).trans
    (shortDLP_runtimeLayout_dimension m ell width source)

/-- Exact binary coordinates adjoin only the unique empty incoming quantum basis. -/
def basisEquiv (m ell width : Nat) :
    (context ctx noQuantum m ell width).register.Index ≃
      (Qubits (totalQubits (registerParameters m ell width))).Index :=
  (Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)
    (input_systemCount ctx noQuantum)).symm.trans
      (ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv

/-- The actual allocation emits exactly one instance of its declared source preparation. -/
theorem shortDLP_runtimeBank_prepare_eventTrace (m ell width N : Nat)
    (path : (prepare ctx noQuantum m ell width N).Path) :
    (prepare ctx noQuantum m ell width N).eventTrace path =
      [(seedPreparation m ell width N).event] := rfl

/-- Actual resident accounting contains the original frame and exactly one source bank. -/
theorem shortDLP_runtimeBank_resident (m ell width : Nat) :
    (context ctx noQuantum m ell width).residentSpace =
      SpacePool.ofQuantumLayout (runtimeLayout m ell width) + ctx.residentSpace :=
  RuntimeCtx.residentSpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)

/-- The actual new bank has the owned auxiliary role; no second quantum capacity is added. -/
theorem shortDLP_runtimeBank_auxiliary (m ell width : Nat) :
    (context ctx noQuantum m ell width).auxiliarySpace =
      SpacePool.ofQuantumLayout (runtimeLayout m ell width) + ctx.auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeBank

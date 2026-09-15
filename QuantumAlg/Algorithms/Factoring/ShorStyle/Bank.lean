/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Layout
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# One actual owned bank for all native Shor rounds

One preparation adds the entire phase, power and shared arithmetic auxiliary
beside an arbitrary classical frame. The empty quantum condition describes
this internal first-allocation boundary. Later rounds retain the same owned
entry and use actual reset and reload, rather than prepare a replacement.
Every new physical system is counted in both resident and auxiliary space.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBank

noncomputable section

open NativeQuantum

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

include noQuantum in
private theorem input_systemCount : ctx.systemCount = 0 := by
  change ctx.quantumWires.length = 0
  rw [noQuantum]
  rfl

include noQuantum in
theorem allocationDisjoint (N : Nat) :
    List.Disjoint (runtimeLayout N).identities ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The actual single owned entry is adjoined to all original classical storage. -/
@[implicit_reducible]
def context (N : Nat) : RuntimeCtx .quantum :=
  ctx.addOwnedLayout ctx.canonicalFreshKey (runtimeLayout N) ctx.canonicalFreshKey_fresh
    (allocationDisjoint ctx noQuantum N)

/-- Exactly one native preparation allocates the complete reusable bank. -/
def prepare (N : Nat) : Circuit ctx (context ctx noQuantum N) :=
  .prepare ctx ctx.canonicalFreshKey (runtimeLayout N) ctx.canonicalFreshKey_fresh
    (allocationDisjoint ctx noQuantum N) (seedPreparation N)

/-- The newly prepared entry has its actual owned storage role. -/
theorem ownedEntry (N : Nat) :
    RuntimeEntry.ownedLayout ctx.canonicalFreshKey (runtimeLayout N) ∈
      (context ctx noQuantum N).entries := List.Mem.head _

/-- All live quantum wires come from the one actual bank; none are silently omitted. -/
theorem quantumWires (N : Nat) :
    (context ctx noQuantum N).quantumWires = (runtimeLayout N).wires := by
  change (runtimeLayout N).wires ++ ctx.quantumWires = _
  rw [noQuantum, List.append_nil]

/-- Actual context order agrees with the bank's physical positions and dimensions. -/
theorem layoutWires (N : Nat) :
    (runtimeLayout N).wires = (context ctx noQuantum N).quantumLayout.wires :=
  ((context ctx noQuantum N).quantumLayout_wires.trans
    (quantumWires ctx noQuantum N)).symm

/-- The complete live bank occupies exactly the source phase, power and auxiliary positions. -/
theorem physicalIdx (N : Nat) :
    (context ctx noQuantum N).physicalIdx = List.range (totalQubits N) := by
  change (context ctx noQuantum N).quantumWires.map QuantumWire.identity = _
  rw [quantumWires]
  exact (layout_identities_eq_map_wires (runtimeLayout N)).symm.trans
    (runtimeLayout_identities N)

/-- The dimensions needed for actual full-bank reset follow from the live layout. -/
theorem qubits (N : Nat) (wire : Fin (context ctx noQuantum N).systemCount) :
    ((context ctx noQuantum N).quantumLayout.wire wire).dimension = 2 := by
  let positions := Execution.positionsOfEqualWires (runtimeLayout N)
    (context ctx noQuantum N).quantumLayout (layoutWires ctx noQuantum N)
  obtain ⟨source, rfl⟩ := positions.surjective wire
  exact (congrArg QuantumWire.dimension
    (Execution.wireAtCorrespondingPosition (runtimeLayout N)
      (context ctx noQuantum N).quantumLayout (layoutWires ctx noQuantum N) source)).trans
    (runtimeLayout_dimension N source)

/-- Binary coordinates preserve every bank position and adjoin only the unique empty old basis. -/
def basisEquiv (N : Nat) :
    (context ctx noQuantum N).register.Index ≃ (Qubits (totalQubits N)).Index :=
  (Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout N)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N)
    (input_systemCount ctx noQuantum)).symm.trans
      (OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv

/-- The allocation emits its actual basis-preparation event exactly once. -/
theorem prepare_eventTrace (N : Nat) (path : (prepare ctx noQuantum N).Path) :
    (prepare ctx noQuantum N).eventTrace path = [(seedPreparation N).event] := rfl

/-- Resident capacity counts the entire one bank beside every original classical entry. -/
theorem resident (N : Nat) :
    (context ctx noQuantum N).residentSpace =
      SpacePool.ofQuantumLayout (runtimeLayout N) + ctx.residentSpace :=
  RuntimeCtx.residentSpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout N)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N)

/-- The same owned bank contributes to auxiliary capacity without an uncounted second payload. -/
theorem auxiliary (N : Nat) :
    (context ctx noQuantum N).auxiliarySpace =
      SpacePool.ofQuantumLayout (runtimeLayout N) + ctx.auxiliarySpace :=
  RuntimeCtx.auxiliarySpace_addOwnedLayout ctx ctx.canonicalFreshKey (runtimeLayout N)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum N)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBank

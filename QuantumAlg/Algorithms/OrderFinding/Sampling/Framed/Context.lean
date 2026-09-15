/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Source
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Circuit

/-!
# Original order sampling with an existing classical input frame

The original source circuit acts on newly prepared phase and target wires.
Existing classical cells remain in the context, and canonical fresh storage
identities prevent collisions with them. Physical quantum identities and the
source query are unchanged [dW19, qcnotes.tex:2203-2225]. These definitions use
the same preparation instruction and source unitary as empty-input sampling.
-/

namespace QuantumAlg.OrderFinding.Sampling.Framed

noncomputable section

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

include noQuantum in
theorem input_systemCount : ctx.systemCount = 0 := by
  change ctx.quantumWires.length = 0
  rw [noQuantum]
  rfl

include noQuantum in
theorem preparationDisjoint (t n : Nat) :
    List.Disjoint (runtimeLayout t n).identities ctx.physicalIdx := by
  simp only [RuntimeCtx.physicalIdx, noQuantum, List.map_nil]
  exact List.disjoint_nil_right _

/-- The actual fresh owned quantum block retains every existing classical input cell. -/
@[implicit_reducible]
def preparedContext (t n : Nat) : RuntimeCtx .quantum :=
  ctx.addOwnedLayout ctx.canonicalFreshKey (runtimeLayout t n) ctx.canonicalFreshKey_fresh
    (preparationDisjoint ctx noQuantum t n)

theorem preparedContext_quantumWires (t n : Nat) :
    (preparedContext ctx noQuantum t n).quantumWires = (runtimeLayout t n).wires := by
  change (runtimeLayout t n).wires ++ ctx.quantumWires = _
  rw [noQuantum, List.append_nil]

theorem preparedContext_physicalIdx (t n : Nat) :
    (preparedContext ctx noQuantum t n).physicalIdx = List.range (t + n) := by
  rw [RuntimeCtx.physicalIdx, preparedContext_quantumWires]
  change (List.ofFn fun index : Fin (t + n) =>
    (runtimeLayout t n).wire index).map QuantumWire.identity = _
  rw [List.map_ofFn]
  exact sourceLayout_systemIdx t n

/-- Exact physical coordinates, adjoining only the unique empty old quantum basis. -/
def preparedLayoutEquiv (t n : Nat) :
    (runtimeLayout t n).register.Index ≃ (preparedContext ctx noQuantum t n).register.Index :=
  Execution.preparedEmptyBasisEquiv ctx ctx.canonicalFreshKey (runtimeLayout t n)
    ctx.canonicalFreshKey_fresh (preparationDisjoint ctx noQuantum t n)
    (input_systemCount ctx noQuantum)

/-- The same binary source labels on the actual newly allocated quantum block. -/
def preparedBasisEquiv (t n : Nat) :
    (preparedContext ctx noQuantum t n).register.Index ≃ (Qubits (t + n)).Index :=
  (preparedLayoutEquiv ctx noQuantum t n).symm.trans (sourceLayout t n).binaryIndexEquiv

/-- The original source unitary uses the actual frame's prepared register coordinates. -/
def nativeProgram {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    UnitaryCircuit (preparedContext ctx noQuantum t n).register :=
  UnitaryCircuit.reindex (preparedBasisEquiv ctx noQuantum t n).symm (orderFindingCircuit A)

theorem nativeProgram_placement {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    (nativeProgram ctx noQuantum A).physical_idx =
      (preparedContext ctx noQuantum t n).physicalIdx := by
  change (orderFindingCircuit A).physical_idx = _
  rw [orderFindingCircuit_physical_idx, preparedContext_physicalIdx]

/-- Actual preparation preserves the existing input frame and charges the source zero state. -/
def preparationCode (t n : Nat) : Circuit ctx (preparedContext ctx noQuantum t n) :=
  .prepare ctx ctx.canonicalFreshKey (runtimeLayout t n) ctx.canonicalFreshKey_fresh
    (preparationDisjoint ctx noQuantum t n) (inputPreparation t n)

end

end QuantumAlg.OrderFinding.Sampling.Framed

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Prepare the short-DLP owned bank once around a classical frame

Actual zero preparation adds one owned layout, then the literal X reload
constructs its source seed. The old context may contain arbitrary classical
values and their reference correlations, but supplies no quantum system.
This is an internal allocation boundary for the surrounding factoring
program, not a condition on later rounds. Its resulting physical bank remains
present during those rounds.

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

/-- The same literal X loading word acts on every actual bank wire. -/
def loadProgram (m ell width N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (context ctx noQuantum m ell width).quantumLayout :=
  Execution.unitaryOfEqualWires (runtimeLayout m ell width)
    (context ctx noQuantum m ell width).quantumLayout
    (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width)
    (reloadProgram m ell width N)

/-- Exact loading semantics uses the correspondence of complete ordered physical wires. -/
theorem shortDLP_runtimeBank_load_matrix (m ell width N : Nat) :
    (loadProgram ctx noQuantum m ell width N).matrix =
      UnitaryOperator.reindex
        (Execution.basisOfEqualWires (runtimeLayout m ell width)
          (context ctx noQuantum m ell width).quantumLayout
          (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width))
        (reloadProgram m ell width N).matrix :=
  Execution.unitaryOfEqualWires_matrix _ _ _ _

/-- The placed loading word takes the corresponding zero vector to the exact source seed. -/
theorem shortDLP_runtimeBank_load_seed (m ell width N : Nat) :
    let corresponding := Execution.basisOfEqualWires (runtimeLayout m ell width)
      (context ctx noQuantum m ell width).quantumLayout
      (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width)
    (loadProgram ctx noQuantum m ell width N).applyVec
        (HilbertVector.reindex corresponding
          (ZeroPreparation.normalized (runtimeLayout m ell width)).vec) =
      HilbertVector.reindex corresponding (seedState m ell width N).vec := by
  dsimp only
  change (loadProgram ctx noQuantum m ell width N).matrix.applyVec _ = _
  rw [shortDLP_runtimeBank_load_matrix]
  refine (UnitaryOperator.reindex_applyVec
    (R := (runtimeLayout m ell width).register)
    (S := (context ctx noQuantum m ell width).register)
    (Execution.basisOfEqualWires (runtimeLayout m ell width)
      (context ctx noQuantum m ell width).quantumLayout
      (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width))
    (reloadProgram m ell width N).matrix
    (ZeroPreparation.normalized (runtimeLayout m ell width)).vec).trans ?_
  exact congrArg (HilbertVector.reindex
    (R := (runtimeLayout m ell width).register)
    (S := (context ctx noQuantum m ell width).register)
    (Execution.basisOfEqualWires (runtimeLayout m ell width)
      (context ctx noQuantum m ell width).quantumLayout
      (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width)))
    (congrArg (NormalizedVector.vec (R := (runtimeLayout m ell width).register))
      (shortDLP_reload_seedState m ell width N))

variable {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Allocate the sole quantum bank and prepare every actual wire in zero. -/
def allocateZero (m ell width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx (context ctx noQuantum m ell width) :=
  .prepareZero ctx ctx.canonicalFreshKey (runtimeLayout m ell width)
    ctx.canonicalFreshKey_fresh (allocationDisjoint ctx noQuantum m ell width)

/-- Initialize the source by actual zero allocation followed by its literal X loading word. -/
def prepare (m ell width N : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty operations services)
      ctx (context ctx noQuantum m ell width) :=
  .seq (allocateZero ctx noQuantum m ell width)
    (.unitary (loadProgram ctx noQuantum m ell width N))

/-- Every allocated qubit emits one preparation event; the subsequent native X word is retained. -/
theorem shortDLP_runtimeBank_prepare_eventTrace (m ell width N : Nat)
    (path : (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).Path) :
    (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).eventTrace path =
      List.replicate (totalQubits (registerParameters m ell width))
        (.preparation (model := .quantum AlgorithmGate.model .empty operations services)
          (2 : ℕ+)) ++
        (reloadProgram m ell width N).eventTrace operations services := by
  change ZeroPreparation.eventTrace AlgorithmGate.model .empty
      (runtimeLayout m ell width) operations services ++
      (loadProgram ctx noQuantum m ell width N).eventTrace operations services = _
  refine congrArg₂ List.append ?_
    (Execution.unitaryOfEqualWires_trace (runtimeLayout m ell width)
      (context ctx noQuantum m ell width).quantumLayout
      (shortDLP_runtimeBank_layoutWires ctx noQuantum m ell width)
      (reloadProgram m ell width N) operations services)
  change List.ofFn (fun _ : Fin (totalQubits (registerParameters m ell width)) =>
    (Resource.Event.preparation (model :=
      .quantum AlgorithmGate.model .empty operations services) (2 : ℕ+))) = _
  exact List.ofFn_const _ _

/-- The exact initialization pool includes all zero preparations and every actual seed-loading X. -/
theorem shortDLP_runtimeBank_prepare_resourcePool (m ell width N : Nat)
    (path : (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).Path) :
    (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).resourcePool path =
      totalQubits (registerParameters m ell width) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.preparation (2 : ℕ+)) +
        reloadXCount m ell width N • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate AlgorithmGate.Coordinate.singleQubit) := by
  simp only [Circuit.resourcePool, shortDLP_runtimeBank_prepare_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_replicate,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    shortDLP_reload_eventCost_classical_context, ResourcePool.scale]

/-- Loading depends on completion of the zero preparation on the same physical bank. -/
theorem shortDLP_runtimeBank_prepare_eventDepth (m ell width N : Nat)
    (path : (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).Path) :
    (prepare (operations := operations) (services := services)
      ctx noQuantum m ell width N).eventDepth path =
      .seq (ZeroPreparation.eventDepth AlgorithmGate.model .empty
        (runtimeLayout m ell width) operations services)
        ((reloadProgram m ell width N).eventDepth operations services) := rfl

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

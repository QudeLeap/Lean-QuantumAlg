/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.BankReset
import all QuantumAlg.Core.Execution.Basis.Seeded.Unitary
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Weighted
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Literal same-bank reload after complete measured reset

The actual native X word reloads the
same owned bank after the separately charged parallel reset. No new bank or
new output cell is allocated. Every original store-weighted reference entry
is retained, without an incoming seed premise for reset plus reload.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Reload

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Loading is a literal native unitary word and performs no allocation. -/
def code (N : Nat) : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  .unitary (load base noQuantum m ell width N)

/-- Complete reset precedes literal reload on the same bank and the same retained result cells. -/
def resetReload (N : Nat) : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  (BankReset.code base noQuantum m ell width).seq (code base noQuantum m ell width N)

/-- The actual loader transports every complete store/reference seed block. -/
lemma measuredReload_seeded (N : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (zero : BasisSeeded.Holds (Context base noQuantum m ell width).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (preparedSeed base noQuantum m ell width N)
      ((code base noQuantum m ell width N).execute environment Reference state) :=
  BasisSeeded.unitary (load base noQuantum m ell width N) environment _ _
    (measuredLoad_apply_zero base noQuantum m ell width environment N) state zero

/-- Reset plus reload establishes the seed internally for arbitrary incoming mixed states. -/
lemma measuredResetReload_seeded (N : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (preparedSeed base noQuantum m ell width N)
      ((resetReload base noQuantum m ell width N).execute environment Reference state) :=
  BasisSeeded.seq (BankReset.code base noQuantum m ell width)
    (code base noQuantum m ell width N) environment (preparedSeed base noQuantum m ell width N)
    state
    (measuredReload_seeded base noQuantum m ell width N _
      (BankReset.measuredBankReset_seeded base noQuantum m ell width state))

/-- Every old classical observation keeps its complete reference correlation through both steps. -/
lemma measuredResetReload_referenceFiberSum (N : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (weight : Store (Context base noQuantum m ell width) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((resetReload base noQuantum m ell width N).execute environment Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight entry.1) leftRef rightRef := by
  rw [resetReload, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  exact (Circuit.unitary_weighted_reference (environment := environment) (load base noQuantum
    m ell width N)
    ((BankReset.code base noQuantum m ell width).execute environment Reference state)
    weight leftRef rightRef).trans
      (BankReset.measuredBankReset_referenceFiberSum
        base noQuantum m ell width state weight leftRef rightRef)

/-- Exact literal X cost remains charged in the actual classical execution model. -/
lemma measuredReload_events (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).resourcePool path =
      EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
        ResourcePool.singleton (model := model) (.gate .singleQubit) := by
  change ResourcePool.ofList
    ((load base noQuantum m ell width N).eventTrace BitWord.model .empty) = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost
    (load base noQuantum m ell width N) BitWord.model .empty]
  rw [load, unitaryOfEqualWires_cost]
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event ((sourceLoad width N).eventCost BitWord.model .empty) =
    ResourcePool.count event (EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
      ResourcePool.singleton (model := model) (.gate .singleQubit))
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
    have nativeCost : (sourceLoad width N).eventCost =
        EncodedBit.Word.BasisLoad.xCount (seedLabel width N) •
          ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
            (.gate .singleQubit) :=
      EncodedBit.Word.BasisLoad.basisLoad_eventCost (Physical.qubits width) .empty
        (seedLabel width N)
    rw [nativeCost]
    cases coordinate <;> simp
  | oracle query => exact nomatch query
  | classicalOperation _ => simp
  | classicalQuery _ => simp
  | preparation _ => simp
  | measurement _ => simp

/-- The same actual loader obeys its independent selected-bit quantum-time bound. -/
lemma measuredReload_quantumTime (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).quantumTime path ≤
      EncodedBit.Word.BasisLoad.xCount (seedLabel width N) := by
  refine ((code base noQuantum m ell width N).quantumTime_le_unitDepth path).trans ?_
  change DepthExpr.depthEval (fun _ => 1)
    ((load base noQuantum m ell width N).eventDepth BitWord.model .empty) ≤ _
  rw [load, unitaryOfEqualWires_depth]
  exact (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
    (sourceLoad width N) BitWord.model .empty).le.trans
      (EncodedBit.Word.BasisLoad.basisLoad_unitDepth
        (Physical.qubits width) .empty (seedLabel width N)).le

/-- The paid reset adds at most one quantum layer before the actual native reload. -/
lemma measuredResetReload_quantumTime (N : Nat)
    (path : (resetReload base noQuantum m ell width N).Path) :
    (resetReload base noQuantum m ell width N).quantumTime path ≤
      1 + EncodedBit.Word.BasisLoad.xCount (seedLabel width N) :=
  Nat.add_le_add (BankReset.measuredBankReset_quantumTime base noQuantum m ell width path.1)
    (measuredReload_quantumTime base noQuantum m ell width N path.2)

/-- The loader keeps the exact existing resident frame and retained cells live. -/
lemma measuredReload_resident (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).peakResidentSpace path =
      (Context base noQuantum m ell width).residentSpace :=
  Circuit.peakResidentSpace_unitary (load base noQuantum m ell width N) path

/-- The actual loader allocates no extra quantum or classical auxiliary storage. -/
lemma measuredReload_auxiliary (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).peakAuxiliarySpace path =
      (Context base noQuantum m ell width).auxiliarySpace :=
  Circuit.peakAuxiliarySpace_unitary (load base noQuantum m ell width N) path

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Reload

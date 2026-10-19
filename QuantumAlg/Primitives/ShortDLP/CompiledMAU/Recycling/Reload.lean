/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.BankReset
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

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Reload

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The complete bank basis follows the proved equality of actual ordered physical wires. -/
def corresponding : (Arithmetic.layout width).toQuantum.register.Index ≃
    (Context base noQuantum m ell width).register.Index :=
  basisOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout (context_wires base noQuantum m ell width)

/-- The original internally computed seed is placed on the existing physical bank. -/
def seed (N : Nat) : (Context base noQuantum m ell width).register.Index :=
  corresponding base noQuantum m ell width
    ((Arithmetic.layout width).basisEquiv.symm (seedLabel width N))

/-- Loading is a literal native unitary word and performs no allocation. -/
def code (N : Nat) : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  .unitary (load base noQuantum m ell width N)

/-- Complete reset precedes literal reload on the same bank and the same retained result cells. -/
def resetReload (N : Nat) : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  (BankReset.code base noQuantum m ell width).seq (code base noQuantum m ell width N)

/-- The binary zero supplied to the source X word is exactly the reset's physical zero. -/
lemma recyclingReload_zero :
    corresponding base noQuantum m ell width ((Arithmetic.layout width).basisEquiv.symm 0) =
      (Context base noQuantum m ell width).quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (positionsOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)).surjective target
  apply Fin.ext
  have same := basisOfEqualWires_value (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout (context_wires base noQuantum m ell width)
    ((Arithmetic.layout width).basisEquiv.symm 0) source
  refine same.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ (Arithmetic.encoding width).width)).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- Actual native X loading has the exact seed action, including its phase and physical labels. -/
lemma recyclingReload_apply_zero (N : Nat) :
    (load base noQuantum m ell width N).applyNormalized environment.quantum
        (NormalizedVector.ket (Context base noQuantum m ell width).quantumLayout.zeroLabel) =
      NormalizedVector.ket (seed base noQuantum m ell width N) := by
  have action :
      (load base noQuantum m ell width N).applyVec environment.quantum
          (HilbertVector.reindex (R := (Arithmetic.layout width).toQuantum.register)
            (S := (Context base noQuantum m ell width).register)
            (corresponding base noQuantum m ell width)
            (NormalizedVector.ket ((Arithmetic.layout width).basisEquiv.symm 0)).vec) =
        HilbertVector.reindex (R := (Arithmetic.layout width).toQuantum.register)
          (S := (Context base noQuantum m ell width).register)
          (corresponding base noQuantum m ell width)
          (NormalizedVector.ket
            ((Arithmetic.layout width).basisEquiv.symm (seedLabel width N))).vec := by
    change ((load base noQuantum m ell width N).matrix environment.quantum).applyVec _ = _
    rw [load, unitaryOfEqualWires_matrix]
    change (UnitaryOperator.reindex (corresponding base noQuantum m ell width)
      ((sourceLoad width N).matrix environment.quantum)).applyVec _ = _
    rw [UnitaryOperator.reindex_applyVec]
    exact congrArg (HilbertVector.reindex (R := (Arithmetic.layout width).toQuantum.register)
      (S := (Context base noQuantum m ell width).register)
      (corresponding base noQuantum m ell width))
      (congrArg (NormalizedVector.vec (R := (Arithmetic.layout width).toQuantum.register))
        (sourceLoad_zero (environment := environment.quantum) width N))
  rw [HilbertVector.reindex_ket, HilbertVector.reindex_ket, recyclingReload_zero] at action
  apply NormalizedVector.ext
  intro row
  exact congrArg (fun vector : HilbertVector (Context base noQuantum m ell width).register =>
    vector row) action

/-- The actual loader transports every complete store/reference seed block. -/
lemma recyclingReload_seeded (N : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (zero : BasisSeeded.Holds (Context base noQuantum m ell width).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (seed base noQuantum m ell width N)
      ((code base noQuantum m ell width N).execute environment Reference state) :=
  BasisSeeded.unitary (load base noQuantum m ell width N) environment _ _
    (recyclingReload_apply_zero base noQuantum m ell width N) state zero

/-- Reset plus reload establishes the seed internally for arbitrary incoming mixed states. -/
lemma recyclingResetReload_seeded (N : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (seed base noQuantum m ell width N)
      ((resetReload base noQuantum m ell width N).execute environment Reference state) :=
  BasisSeeded.seq (BankReset.code base noQuantum m ell width)
    (code base noQuantum m ell width N) environment (seed base noQuantum m ell width N) state
    (recyclingReload_seeded base noQuantum m ell width N _
      (BankReset.recyclingBankReset_seeded base noQuantum m ell width state))

/-- Every old classical observation keeps its complete reference correlation through both steps. -/
lemma recyclingResetReload_referenceFiberSum (N : Nat) {Reference : Register}
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
      (BankReset.recyclingBankReset_referenceFiberSum
        base noQuantum m ell width state weight leftRef rightRef)

/-- Exact literal X cost remains charged in the actual classical execution model. -/
lemma recyclingReload_events (N : Nat) (path : (code base noQuantum m ell width N).Path) :
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
    cases coordinate <;> simp [sourceLoad, EncodedBit.Word.BasisLoad.basisLoad_eventCost]
  | oracle query => exact nomatch query
  | classicalOperation _ => simp
  | classicalQuery _ => simp
  | preparation _ => simp
  | measurement _ => simp

/-- The same actual loader obeys its independent selected-bit quantum-time bound. -/
lemma recyclingReload_quantumTime (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).quantumTime path ≤
      EncodedBit.Word.BasisLoad.xCount (seedLabel width N) := by
  refine ((code base noQuantum m ell width N).quantumTime_le_unitDepth path).trans ?_
  change DepthExpr.depthEval (fun _ => 1)
    ((load base noQuantum m ell width N).eventDepth BitWord.model .empty) ≤ _
  rw [load, unitaryOfEqualWires_depth]
  exact (UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
    (sourceLoad width N) BitWord.model .empty).le.trans
      (EncodedBit.Word.BasisLoad.basisLoad_unitDepth
        (Arithmetic.layout width) .empty (seedLabel width N)).le

/-- The paid reset adds at most one quantum layer before the actual native reload. -/
lemma recyclingResetReload_quantumTime (N : Nat)
    (path : (resetReload base noQuantum m ell width N).Path) :
    (resetReload base noQuantum m ell width N).quantumTime path ≤
      1 + EncodedBit.Word.BasisLoad.xCount (seedLabel width N) :=
  Nat.add_le_add (BankReset.recyclingBankReset_quantumTime base noQuantum m ell width path.1)
    (recyclingReload_quantumTime base noQuantum m ell width N path.2)

/-- The loader keeps precisely the existing resident bank and retained outputs live. -/
lemma recyclingReload_resident (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).peakResidentSpace path =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.residentSpace) :=
  (Circuit.peakResidentSpace_unitary (load base noQuantum m ell width N) path).trans
    (context_resident base noQuantum m ell width)

/-- The loader introduces no new auxiliary storage beyond the existing owned bank and outputs. -/
lemma recyclingReload_auxiliary (N : Nat) (path : (code base noQuantum m ell width N).Path) :
    (code base noQuantum m ell width N).peakAuxiliarySpace path =
      resultBits m ell • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.auxiliarySpace) :=
  (Circuit.peakAuxiliarySpace_unitary (load base noQuantum m ell width N) path).trans
    (context_auxiliary base noQuantum m ell width)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Reload

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.MAU.Addition.HRS.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Borrowed.Unitary
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Owned.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Owned.Borrowed.CoordinateAgreement
import all QuantumAlg.Core.Execution.Borrowed.Unitary
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Primitives.MAU.Addition.HRS.Semantics
import all QuantumAlg.Primitives.MAU.Addition.HRS.NativeResources

/-!
# Complete one-dirty constant addition

The actual recursive HRS program uses one supplied owned word and one supplied
borrowed bit. Its complete output retains both. The borrowed bit and every
external-reference correlation are restored by the full operator identity,
independently of input purity [HRS16, paper.tex:175-177,232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution.OwnedBorrowedQubits

private def nativeOperator (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryOperator (context width 1).register :=
  wordOperator width 1 (wordTranslation width constant.val)

private theorem supplied_wires (width : Nat) :
    (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum.wires =
      (context width 1).quantumLayout.wires := by
  rw [show (oneDirtyEncoding width).width = width + 1 by rfl]
  change (wordLayout (width + 1)).toQuantumLayout.wires =
    (context width 1).quantumLayout.wires
  exact context_wires width 1

private def nativeProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty (context width 1).quantumLayout :=
  Execution.unitaryOfEqualWires
    (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum
    (context width 1).quantumLayout (supplied_wires width)
      (oneDirtyProgram width constant)

private def sourceContextEquiv (width : Nat) :
    (Qubits (width + 1)).Index ≃ (context width 1).register.Index :=
  let transport :
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum.register.Index ≃
        (context width 1).register.Index :=
    Execution.basisOfEqualWires
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum
      (context width 1).quantumLayout (supplied_wires width)
  (QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm.trans transport

set_option maxHeartbeats 500000 in
-- Reducing the transported basis equivalence requires unfolding both canonical layouts.
private theorem sourceContextEquiv_eq (width : Nat) :
    sourceContextEquiv width = (basisEquiv width 1).symm := by
  rfl

set_option maxHeartbeats 1000000 in
-- Reindex cancellation expands the source circuit's full matrix equality.
private theorem sourceProgram_matrix (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).matrix =
      UnitaryOperator.reindex
        (QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
        (oneDirtyOperator width constant) := by
  have actual := hrsOneDirty_matrix width constant
  change UnitaryOperator.reindex
      (QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv
      (oneDirtyProgram width constant).matrix = oneDirtyOperator width constant at actual
  rw [← actual]
  exact (UnitaryOperator.unitaryOperator_reindex_cancel
    (QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv
    (oneDirtyProgram width constant).matrix).symm

set_option maxHeartbeats 1500000 in
-- Composing the two layout transports normalizes a proof-dependent basis equivalence.
private theorem nativeProgram_matrix (width : Nat) (constant : Fin (2 ^ width)) :
    (nativeProgram width constant).matrix = nativeOperator width constant := by
  change (nativeProgram width constant).matrix =
    UnitaryOperator.reindex (wordBinaryEquiv width 1).symm
      (oneDirtyOperator width constant)
  rw [← basisEquiv_eq_wordBinaryEquiv width 1]
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, sourceProgram_matrix]
  calc
    UnitaryOperator.reindex
        (Execution.basisOfEqualWires
          (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum
          (context width 1).quantumLayout (supplied_wires width))
        (UnitaryOperator.reindex
          (QubitLayout.canonical (oneDirtyEncoding width).width).basisEquiv.symm
          (oneDirtyOperator width constant)) =
      UnitaryOperator.reindex (sourceContextEquiv width)
        (oneDirtyOperator width constant) :=
      UnitaryOperator.unitaryOperator_reindex_trans _ _ _
    _ = UnitaryOperator.reindex (basisEquiv width 1).symm
        (oneDirtyOperator width constant) := by
      apply congrArg (fun equivalence =>
        UnitaryOperator.reindex equivalence (oneDirtyOperator width constant))
      exact sourceContextEquiv_eq width

private def code (width : Nat) (constant : Fin (2 ^ width)) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width 1) (context width 1) :=
  .unitary (nativeProgram width constant)

/-- Independent complete constant-addition contract with one borrowed bit.

**Input.**

- One supplied owned width-qubit word and one supplied borrowed qubit,
in any joint normalized state, including mixed inputs and correlations with an
arbitrary external reference. The fitted classical constant is a compilation
parameter and occupies no runtime register. No initialization is assumed.
**Output.**

- Both words remain live. The owned word undergoes addition of the
constant modulo 2^width, and the borrowed bit undergoes identity. This is an
exact full-state operator specification, including its phase and reference.
**Resource budget.**

- Each of the literal X, CNOT and Toffoli coordinates has
cap width*(39*clog(2,width)+1). Unit-duration depth has that same bound. Resident
space is width+1 dimension-two systems; owned auxiliary space is width systems.
There are no classical bits or systems of other dimensions. The borrowed bit
is one of those resident systems and is not counted as another owned word.
**Success.**

- The unit result has probability one. The joint-state target and
complete borrowed classical-quantum-reference restoration hold for every input.
Width zero is the zero-event identity retaining the one supplied borrowed bit.
**Source.**

- Arbitrarily correlated dirty borrowing and recursive constant
addition in [HRS16, paper.tex:175-177,232-260]. The explicit native and depth
formulas are bounds proved for this actual recursive construction.
-/
public def problem (width : Nat) (constant : Fin (2 ^ width)) :
    Problem (.quantum AlgorithmGate.model .empty)
      (context width 1) (context width 1) .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (nativeOperator width constant)]
  resources :=
    { events := nativeBudget width
      resident := space (width + 1)
      auxiliary := space width }
  depth :=
    { duration := fun _ => 1
      limit := width * (39 * Nat.clog 2 width + 1)
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Execute the actual adder and retain both the owned word and borrowed bit in complete Output. -/
public def algorithm (width : Nat) (constant : Fin (2 ^ width)) :
    Algorithm (.quantum AlgorithmGate.model .empty)
      (context width 1) (context width 1) .unit where
  run := { code := code width constant, output := Output.all (context width 1) .unit }

/-- The public execution explicitly retains every owned and borrowed live entry. -/
public theorem hrsOneDirty_output_listing (width : Nat) (constant : Fin (2 ^ width)) :
    (algorithm width constant).run.output.listing = (context width 1).keys := (rfl)

/-- The independent resident budget counts the supplied word and the one borrowed qubit. -/
public theorem hrsOneDirty_resident_budget (width : Nat) (constant : Fin (2 ^ width)) :
    (problem width constant).resources.resident = space (width + 1) := (rfl)

/-- Only the supplied owned word contributes to the owned auxiliary budget. -/
public theorem hrsOneDirty_auxiliary_budget (width : Nat) (constant : Fin (2 ^ width)) :
    (problem width constant).resources.auxiliary = space width := (rfl)

private theorem actual_events (width : Nat) (constant : Fin (2 ^ width))
    (path : (code width constant).Path) :
    (code width constant).resourcePool path ≤ nativeBudget width := by
  change ResourcePool.ofList (nativeProgram width constant).eventTrace ≤ _
  have cost : (nativeProgram width constant).eventCost =
      (oneDirtyProgram width constant).eventCost :=
    Execution.unitaryOfEqualWires_cost
      (QubitLayout.canonical (oneDirtyEncoding width).width).toQuantum
      (context width 1).quantumLayout (supplied_wires width)
      (oneDirtyProgram width constant) .empty .empty
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, cost]
  exact hrsOneDirty_native_bound width constant

private theorem actual_restoration (width : Nat) (constant : Fin (2 ^ width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : Execution.State (context width 1) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    (code width constant).BorrowedRestored Reference state
      ((code width constant).execute Reference state) := by
  apply Circuit.borrowedRestored_unitary_complement
    (nativeProgram width constant)
    (complementaryOperator width 1 (wordTranslation width constant.val))
  rw [nativeProgram_matrix]
  exact wordOperator_complement width 1 (wordTranslation width constant.val)

private theorem actual_run_restoration (width : Nat) (constant : Fin (2 ^ width))
    {Reference : Register}
    (input : Execution.OracleInput .empty (context width 1) Reference) :
    (algorithm width constant).run.RestoresBorrowed input := by
  change Execution.observeBorrowedAfter (code width constant) Reference
      ((code width constant).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
    Execution.observeBorrowed Reference input.state
  refine (actual_restoration width constant
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
  refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
  apply congrArg (Execution.observeBorrowed Reference)
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _
    (fun _ => rfl) _ _

/-- The actual one-dirty adder meets its independent state, restoration and resource contract. -/
public theorem main (width : Nat) (constant : Fin (2 ^ width)) :
    ∃ candidate, Algorithm.Solves candidate (problem width constant) := by
  refine ⟨algorithm width constant, ?_⟩
  constructor
  · intro Reference input _valid _initialized
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid _initialized requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width constant) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (nativeOperator width constant)
      (nativeProgram width constant) (nativeProgram_matrix width constant)
      (Output.all (context width 1) .unit) input
  · intro Reference input _valid _initialized
    exact actual_run_restoration width constant input
  · intro _Reference _input _valid _initialized path _supported
    exact actual_events width constant path
  · intro _Reference _input _valid _initialized path _supported axis
    change Nat.max ((context width 1).residentSpace axis) 0 ≤ space (width + 1) axis
    rw [context_resident]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid _initialized path _supported axis
    change Nat.max ((context width 1).auxiliarySpace axis) 0 ≤ space width axis
    rw [context_auxiliary]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid _initialized path _supported
    change DepthExpr.depthEval (fun _ => 1)
      ((nativeProgram width constant).eventDepth .empty .empty) ≤ _
    rw [nativeProgram, Execution.unitaryOfEqualWires_depth,
      UnitaryCircuit.unitaryCircuit_unit_depth_classical_context]
    exact hrsOneDirty_depth_bound width constant

end

end QuantumAlg.MAU.Addition.HRS

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
public import QuantumAlg.Primitives.MAU.Addition.HRS.Semantics
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Borrowed.Unitary
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Owned.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Borrowed.Unitary
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
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

private def nativeProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit (context width 1).register :=
  UnitaryCircuit.reindex (wordBinaryEquiv width 1).symm (oneDirtyProgram width constant)

private theorem nativeProgram_matrix (width : Nat) (constant : Fin (2 ^ width)) :
    (nativeProgram width constant).matrix = nativeOperator width constant :=
  (UnitaryCircuit.reindex_matrix (wordBinaryEquiv width 1).symm
    (oneDirtyProgram width constant)).trans
      (congrArg (UnitaryOperator.reindex (wordBinaryEquiv width 1).symm)
        (hrsOneDirty_matrix width constant))

private theorem placement (width : Nat) (constant : Fin (2 ^ width)) :
    (nativeProgram width constant).physical_idx = (context width 1).physicalIdx := by
  change (oneDirtyProgram width constant).physical_idx = (context width 1).physicalIdx
  rw [hrsOneDirty_physical, context_physicalIdx]

private def code (width : Nat) (constant : Fin (2 ^ width)) :
    Circuit (context width 1) (context width 1) :=
  .unitary (nativeProgram width constant) (placement width constant)

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
    Problem .quantum (context width 1) (context width 1) .unit where
  valid := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [StateRequirement.unitary (nativeOperator width constant)]
  resources :=
    { events := nativeBudget width
      resident := space (width + 1)
      auxiliary := space width }
  depth := .quantum (fun _ => 1) (width * (39 * Nat.clog 2 width + 1))

/-- Execute the actual adder and retain both the owned word and borrowed bit in complete Output. -/
public def algorithm (width : Nat) (constant : Fin (2 ^ width)) :
    Algorithm .quantum (context width 1) (context width 1) .unit where
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
  exact (le_of_eq
    ((UnitaryCircuit.ofList_eventTrace_eq_eventCost (nativeProgram width constant)).trans
      (UnitaryCircuit.reindex_eventCost (wordBinaryEquiv width 1).symm
        (oneDirtyProgram width constant)))).trans (hrsOneDirty_native_bound width constant)

private theorem actual_restoration (width : Nat) (constant : Fin (2 ^ width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : Execution.State (context width 1) Reference H) :
    (code width constant).BorrowedRestored Reference state
      ((code width constant).execute Reference state) := by
  apply Circuit.borrowedRestored_unitary_complement
    (nativeProgram width constant) (placement width constant)
    (complementaryOperator width 1 (wordTranslation width constant.val))
  rw [nativeProgram_matrix]
  exact wordOperator_complement width 1 (wordTranslation width constant.val)

/-- The actual one-dirty adder meets its independent state, restoration and resource contract. -/
public theorem main (width : Nat) (constant : Fin (2 ^ width)) :
    ∃ candidate, Algorithm.Solves candidate (problem width constant) := by
  refine ⟨algorithm width constant, ?_⟩
  constructor
  · intro Reference input _valid
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro Reference input _valid requirement present
    have same : requirement = StateRequirement.unitary (nativeOperator width constant) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds (nativeOperator width constant)
      (nativeProgram width constant) (placement width constant)
      (nativeProgram_matrix width constant)
      (Output.all (context width 1) .unit) input
  · intro Reference input _valid
    exact actual_restoration width constant (input.state.mapClassical fun store => (store, store))
  · intro _Reference _input _valid path _supported
    exact actual_events width constant path
  · intro _Reference _input _valid path _supported axis
    change Nat.max ((context width 1).residentSpace axis) 0 ≤ space (width + 1) axis
    rw [context_resident]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid path _supported axis
    change Nat.max ((context width 1).auxiliarySpace axis) 0 ≤ space width axis
    rw [context_auxiliary]
    exact le_of_eq (Nat.max_zero _)
  · intro _Reference _input _valid path _supported
    exact hrsOneDirty_depth_bound width constant

end

end QuantumAlg.MAU.Addition.HRS

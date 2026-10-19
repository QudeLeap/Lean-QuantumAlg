/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Borrowed

/-!
# One owned qubit word and one borrowed qubit word

The owned word precedes the borrowed word in the actual ordered physical
frame. Both words remain resident. Only the owned word contributes to auxiliary
space; the borrowed role requires separate joint restoration by the execution.
No initialization or independence promise is attached to either word.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

def wordLayout (width : Nat) : QubitLayout width :=
  { physical_idx := Fin.val, physical_idx_injective := Fin.val_injective }

def borrowedLayout (owned borrowed : Nat) : QubitLayout borrowed :=
  { physical_idx := fun index => owned + index.val
    physical_idx_injective := fun _left _right same =>
      Fin.ext (Nat.add_left_cancel same) }

def borrowedContext (owned borrowed : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedLayout ⟨1⟩ (borrowedLayout owned borrowed).toQuantumLayout
    (by decide) (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private lemma disjointWords (owned borrowed : Nat) :
    List.Disjoint (wordLayout owned).toQuantumLayout.identities
      (borrowedContext owned borrowed).physicalIdx := by
  change List.Disjoint (List.ofFn (fun index : Fin owned => index.val))
    (((List.ofFn (fun index : Fin borrowed =>
      ({ identity := owned + index.val, dimension := 2 } : QuantumWire))) ++ []).map
        QuantumWire.identity)
  simp only [List.append_nil, List.map_ofFn]
  apply List.disjoint_left.mpr
  intro identity inOwned inBorrowed
  obtain ⟨ownedIndex, rfl⟩ := List.mem_ofFn.mp inOwned
  obtain ⟨borrowedIndex, same⟩ := List.mem_ofFn.mp inBorrowed
  have bound := ownedIndex.isLt
  change owned + borrowedIndex.val = ownedIndex.val at same
  omega

/-- The exact supplied owned and borrowed words, with globally disjoint physical identities. -/
@[reducible] public def context (owned borrowed : Nat) : RuntimeCtx .quantum :=
  (borrowedContext owned borrowed).addOwnedLayout ⟨0⟩ (wordLayout owned).toQuantumLayout
    (by change (⟨0⟩ : StorageKey) ∉ [⟨1⟩]; decide) (disjointWords owned borrowed)

lemma context_wires (owned borrowed : Nat) :
    (wordLayout (owned + borrowed)).toQuantumLayout.wires =
      (context owned borrowed).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change List.ofFn (fun index : Fin (owned + borrowed) =>
      ({ identity := index.val, dimension := 2 } : QuantumWire)) =
    List.ofFn (fun index : Fin owned =>
      ({ identity := index.val, dimension := 2 } : QuantumWire)) ++
      (List.ofFn (fun index : Fin borrowed =>
        ({ identity := owned + index.val, dimension := 2 } : QuantumWire)) ++ [])
  rw [List.append_nil, List.ofFn_add]
  rfl

/-- Big-endian labels preserve the full ordered physical frame, including the borrowed suffix. -/
public def basisEquiv (owned borrowed : Nat) :
    (context owned borrowed).register.Index ≃ (Qubits (owned + borrowed)).Index :=
  (Execution.basisOfEqualWires (wordLayout (owned + borrowed)).toQuantumLayout
    (context owned borrowed).quantumLayout (context_wires owned borrowed)).symm.trans
      (wordLayout (owned + borrowed)).binaryIndexEquiv

/-- Every actual owned and borrowed physical system appears exactly once. -/
public lemma context_physicalIdx (owned borrowed : Nat) :
    (context owned borrowed).physicalIdx = List.range (owned + borrowed) := by
  change (context owned borrowed).quantumWires.map QuantumWire.identity = _
  rw [← RuntimeCtx.quantumLayout_wires, ← context_wires]
  simp only [QuantumLayout.wires, List.map_ofFn]
  change List.ofFn (fun index : Fin (owned + borrowed) => index.val) = _
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

/-- The independent dimension-sensitive qubit storage formula. -/
public def space (width : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then width else 0

/-- Both supplied words remain resident throughout a same-context unitary execution. -/
lemma context_resident (owned borrowed : Nat) :
    (context owned borrowed).residentSpace = space (owned + borrowed) := by
  simp only [context, borrowedContext, RuntimeCtx.residentSpace_addOwnedLayout,
    RuntimeCtx.residentSpace_addBorrowedLayout, RuntimeCtx.residentSpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (wordLayout owned).toQuantumLayout.dimensionCount dimension +
        ((borrowedLayout owned borrowed).toQuantumLayout.dimensionCount dimension + 0) = _
      rw [QubitLayout.toQuantumLayout_dimensionCount, QubitLayout.toQuantumLayout_dimensionCount]
      by_cases same : (2 : ℕ+) = dimension <;> simp [space, same]

/-- The borrowed word is resident without being counted again as owned auxiliary storage. -/
lemma context_auxiliary (owned borrowed : Nat) :
    (context owned borrowed).auxiliarySpace = space owned := by
  simp only [context, borrowedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout,
    RuntimeCtx.auxiliarySpace_addBorrowedLayout, RuntimeCtx.auxiliarySpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (wordLayout owned).toQuantumLayout_dimensionCount dimension

/-- The borrowed word contains precisely its supplied physical wire records. -/
lemma context_borrowedWires (owned borrowed : Nat) :
    (context owned borrowed).borrowedQuantumWires =
      (borrowedLayout owned borrowed).toQuantumLayout.wires := by
  change [] ++ ((borrowedLayout owned borrowed).toQuantumLayout.wires ++ []) = _
  simp only [List.nil_append, List.append_nil]

end

end QuantumAlg.Execution.OwnedBorrowedQubits

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Owned.Qubits
public import QuantumAlg.Core.Execution.Preparation
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import all QuantumAlg.Util.FinPow

/-!
# Native input and internally prepared exponentiation work words

The input owns the exponent and arbitrary XOR target on consecutive physical
identities. One actual basis preparation allocates exactly the two work words
after them, with power one modulo the modulus and auxiliary zero. All systems
remain live and retained. A block preparation is one native instruction whose
declared values specify both words [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.OwnedQubits Nat.FixedWidth

def workKey : StorageKey := ⟨1⟩

/-- Only the two missing work words are allocated after the supplied exponent and target. -/
def workQubitLayout (exponentWidth width : Nat) : QubitLayout (width + width) where
  physical_idx wire := exponentWidth + width + wire.val
  physical_idx_injective := by
    intro left right same
    change exponentWidth + width + left.val = exponentWidth + width + right.val at same
    apply Fin.ext
    omega

def workLayout (exponentWidth width : Nat) : QuantumLayout (width + width) :=
  (workQubitLayout exponentWidth width).toQuantumLayout

theorem gidneyExponentWork_identities (exponentWidth width : Nat) :
    (workLayout exponentWidth width).identities =
      List.range' (exponentWidth + width) (width + width) := by
  change List.ofFn (fun wire : Fin (width + width) => exponentWidth + width + wire.val) = _
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

theorem gidneyExponentWork_fresh (exponentWidth width : Nat) :
    workKey ∉ (context (exponentWidth + width)).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

theorem gidneyExponentWork_disjoint (exponentWidth width : Nat) :
    List.Disjoint (workLayout exponentWidth width).identities
      (context (exponentWidth + width)).physicalIdx := by
  rw [gidneyExponentWork_identities, ownedQubits_physicalIdx]
  apply List.disjoint_left.mpr
  intro wire work original
  have newBound := List.mem_range'.mp work
  have oldBound := List.mem_range.mp original
  omega

/-- Actual post-context after preparation retains the original input and both new work words. -/
public def preparedContext (exponentWidth width : Nat) : RuntimeCtx .quantum :=
  (context (exponentWidth + width)).addOwnedLayout workKey (workLayout exponentWidth width)
    (gidneyExponentWork_fresh exponentWidth width) (gidneyExponentWork_disjoint exponentWidth width)

/-- Compile the canonical identity power and zero auxiliary into the actual two-word layout. -/
def workPreparation (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) : BasisPreparation (workLayout exponentWidth width) :=
  ⟨(workQubitLayout exponentWidth width).binaryIndexEquiv.symm
    (prodEquiv (m := width) (n := width) (unitResidueWord modulus positive 1, 0))⟩

/-- The actual prepared basis has precisely the compiled power and zero auxiliary values. -/
theorem gidneyExponentWork_prepared_words (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (prodEquiv (m := width) (n := width)).symm
      ((workQubitLayout exponentWidth width).binaryIndexEquiv
        (workPreparation exponentWidth width modulus positive).value) =
      (unitResidueWord modulus positive 1, 0) := by
  unfold workPreparation
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Context order places the freshly prepared work before the unchanged supplied input. -/
public theorem gidneyExponentPreparedContext_physical (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).physicalIdx =
      List.range' (exponentWidth + width) (width + width) ++
        List.range (exponentWidth + width) := by
  change ((workLayout exponentWidth width).wires ++
    (context (exponentWidth + width)).quantumWires).map QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (workLayout exponentWidth width).identities ++
    (context (exponentWidth + width)).physicalIdx = _
  rw [gidneyExponentWork_identities, ownedQubits_physicalIdx]

theorem gidneyExponentPreparedContext_contains (exponentWidth width : Nat) :
    List.range (exponentWidth + 3 * width) ⊆
      (preparedContext exponentWidth width).physicalIdx := by
  intro wire present
  rw [gidneyExponentPreparedContext_physical, List.mem_append]
  have bound := List.mem_range.mp present
  by_cases old : wire < exponentWidth + width
  · exact Or.inr (List.mem_range.mpr old)
  · apply Or.inl
    apply List.mem_range'.mpr
    refine ⟨wire - (exponentWidth + width), by omega, ?_⟩
    simp only [Nat.one_mul]
    omega

end

end QuantumAlg.MAU.Exponentiation.Gidney

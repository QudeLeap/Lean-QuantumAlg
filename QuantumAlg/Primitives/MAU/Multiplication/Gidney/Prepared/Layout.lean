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
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# One supplied word and one internally prepared auxiliary word

The input owns physical qubits `0,...,width-1`. The instruction allocates
exactly `width` fresh qubits `width,...,2*width-1`, initialized internally
to zero. Both words remain in the complete output. The logical two-word
encoding is source then auxiliary; its correspondence with the context's
prepended wire order is an explicit physical basis equivalence.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Execution.OwnedQubits

def auxiliaryKey : StorageKey := ⟨1⟩

def auxiliaryQubitLayout (width : Nat) : QubitLayout width where
  physical_idx wire := width + wire.val
  physical_idx_injective := by
    intro left right same
    change width + left.val = width + right.val at same
    apply Fin.ext
    omega

def auxiliaryLayout (width : Nat) : QuantumLayout width :=
  (auxiliaryQubitLayout width).toQuantumLayout

lemma gidneyAuxiliaryLayout_identities (width : Nat) :
    (auxiliaryLayout width).identities = List.range' width width := by
  change List.ofFn (fun wire : Fin width => width + wire.val) = List.range' width width
  apply List.ext_getElem
  · simp
  · intro index _left _right
    simp

lemma gidneyAuxiliary_fresh (width : Nat) : auxiliaryKey ∉ (context width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

lemma gidneyAuxiliary_disjoint (width : Nat) :
    List.Disjoint (auxiliaryLayout width).identities (context width).physicalIdx := by
  rw [gidneyAuxiliaryLayout_identities, ownedQubits_physicalIdx]
  apply List.disjoint_left.mpr
  intro wire newWord oldWord
  have lower := List.mem_range'.mp newWord
  have upper := List.mem_range.mp oldWord
  omega

/-- The actual context after allocating the zero auxiliary word contains exactly both words. -/
public def preparedContext (width : Nat) : RuntimeCtx .quantum :=
  (context width).addOwnedLayout auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)

/-- Compile the auxiliary zero word from its declared physical basis values. -/
def auxiliaryPreparation (width : Nat) : BasisPreparation (auxiliaryLayout width) :=
  BasisPreparation.zero (auxiliaryLayout width)

public lemma gidneyPreparedContext_physical (width : Nat) :
    (preparedContext width).physicalIdx = List.range' width width ++ List.range width := by
  change ((auxiliaryLayout width).wires ++ (context width).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append]
  rw [← layout_identities_eq_map_wires]
  change (auxiliaryLayout width).identities ++ (context width).physicalIdx = _
  rw [gidneyAuxiliaryLayout_identities, ownedQubits_physicalIdx]

lemma gidneyPreparedContext_contains (width : Nat) :
    List.range (2 * width) ⊆ (preparedContext width).physicalIdx := by
  intro wire present
  rw [gidneyPreparedContext_physical, List.mem_append]
  have bound := List.mem_range.mp present
  by_cases old : wire < width
  · exact Or.inr (List.mem_range.mpr old)
  · apply Or.inl
    apply List.mem_range'.mpr
    refine ⟨wire - width, by omega, ?_⟩
    simp only [Nat.one_mul]
    omega

/-- Physical fresh/source fields are regrouped into logical source/auxiliary binary words. -/
def preparedWordBasisEquiv (width : Nat) :
    (preparedContext width).register.Index ≃ (Qubits (width + width)).Index :=
  (Execution.preparedLocalBasisEquiv (context width) auxiliaryKey (auxiliaryLayout width)
    (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)).symm |>.trans
      (Equiv.prodCongr (auxiliaryQubitLayout width).binaryIndexEquiv (basisEquiv width)) |>.trans
        (Equiv.prodComm _ _) |>.trans (prodEquiv (m := width) (n := width))

/-- The actual fresh basis is the all-zero binary word, including width zero. -/
lemma gidneyAuxiliaryPreparation_zero (width : Nat) :
    (auxiliaryQubitLayout width).binaryIndexEquiv (auxiliaryPreparation width).value =
      (0 : Fin (2 ^ width)) := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have bit := (auxiliaryQubitLayout width).binaryIndexEquiv_bit
    (auxiliaryPreparation width).value index.rev
  rw [Fin.rev_rev] at bit
  rw [Fin.val_zero, Nat.zero_testBit]
  exact bit.trans (by rfl)

end

end QuantumAlg.MAU.Multiplication.Gidney

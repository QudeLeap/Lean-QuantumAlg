/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Actual fixed auxiliary preparation beside the original quantum input

The original input occupies exactly the low n physical bits of Work2.
One actual preparation adds all remaining source wires: the n+6 positions
before that input and the four length fields and five controls after it
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-117].
Its values depend only on the modulus: Work1 is `100,p`, its coefficient
length is one, and all remaining new bits are zero. The divisor length
will be computed by the actual native writer after the actual fold.

The preparation tensors these fixed finite values with the complete
unknown input-reference state [dW19, qcnotes.tex:5381,8071]. It does not
prepare from the input label or require any initial clean work from the
caller. Both coherent reference entries and the single actual preparation
event are retained. The later source-label and native-program connection
uses this same allocated frame.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputPreparation

noncomputable section

open Execution

/-- Work1 and the three zero padding positions preceding the original Work2 input. -/
def prefixWidth (width : Nat) : Nat := width + 6

/-- Exactly the actual four length fields and five controls following the input. -/
def suffixWidth (width : Nat) : Nat := 4 * width.size + 5

/-- Every new wire outside the supplied n-bit input, including the large source workspace. -/
def auxiliaryWidth (width : Nat) : Nat := prefixWidth width + suffixWidth width

/-- Keep each supplied input bit at its literal final source physical identity. -/
def inputQubitLayout (width : Nat) : QubitLayout width where
  physical_idx index := prefixWidth width + index.val
  physical_idx_injective := by
    intro left right same
    apply Fin.ext
    change prefixWidth width + left.val = prefixWidth width + right.val at same
    omega

/-- The supplied input consists of these actual dimension-two systems and no auxiliary wire. -/
def inputLayout (width : Nat) : QuantumLayout width :=
  (inputQubitLayout width).toQuantumLayout

/-- Enumerate the exact complement of the supplied contiguous input, in physical order. -/
def auxiliaryPhysicalIndex (width : Nat) (index : Fin (auxiliaryWidth width)) : Nat :=
  if index.val < prefixWidth width then index.val else width + index.val

private theorem auxiliaryPhysicalIndex_injective (width : Nat) :
    Function.Injective (auxiliaryPhysicalIndex width) := by
  intro left right same
  apply Fin.ext
  unfold auxiliaryPhysicalIndex at same
  split at same <;> split at same <;> omega

/-- The preparation uses only the existing source identities outside the original input. -/
def auxiliaryQubitLayout (width : Nat) : QubitLayout (auxiliaryWidth width) where
  physical_idx := auxiliaryPhysicalIndex width
  physical_idx_injective := auxiliaryPhysicalIndex_injective width

/-- Every added source system remains explicitly dimension two. -/
def auxiliaryLayout (width : Nat) : QuantumLayout (auxiliaryWidth width) :=
  (auxiliaryQubitLayout width).toQuantumLayout

/-- The algorithm starts with exactly one supplied owned input register. -/
def before (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (inputLayout width) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem before_physical (width : Nat) :
    (before width).physicalIdx = (inputLayout width).identities := by
  change ((inputLayout width).wires ++ []).map QuantumWire.identity = _
  rw [List.append_nil, ← layout_identities_eq_map_wires]

private theorem input_wires (width : Nat) :
    (inputLayout width).wires = (before width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width).wires = (inputLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- Binary labels identify exactly the originally supplied n physical bits. -/
def inputBasisEquiv (width : Nat) : (before width).register.Index ≃ (Qubits width).Index :=
  (basisOfEqualWires (inputLayout width) (before width).quantumLayout
    (input_wires width)).symm.trans (inputQubitLayout width).binaryIndexEquiv

private def auxiliaryKey : StorageKey := ⟨1⟩

private theorem auxiliary_fresh (width : Nat) : auxiliaryKey ∉ (before width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

private theorem auxiliary_disjoint (width : Nat) :
    List.Disjoint (auxiliaryLayout width).identities (before width).physicalIdx := by
  rw [before_physical]
  apply List.disjoint_left.mpr
  intro wire fresh old
  change wire ∈ List.ofFn (auxiliaryPhysicalIndex width) at fresh
  change wire ∈ List.ofFn (fun index : Fin width => prefixWidth width + index.val) at old
  obtain ⟨newIndex, newPosition⟩ := List.mem_ofFn.mp fresh
  obtain ⟨oldIndex, oldPosition⟩ := List.mem_ofFn.mp old
  have oldBound := oldIndex.isLt
  unfold auxiliaryPhysicalIndex at newPosition
  split at newPosition <;> omega

/-- Every original source wire is live after this fixed auxiliary preparation. -/
def after (width : Nat) : RuntimeCtx .quantum :=
  (before width).addOwnedLayout auxiliaryKey (auxiliaryLayout width)
    (auxiliary_fresh width) (auxiliary_disjoint width)

/-- Runtime order places fresh auxiliary systems before the unchanged original input. -/
theorem after_physical (width : Nat) :
    (after width).physicalIdx =
      (auxiliaryLayout width).identities ++ (inputLayout width).identities := by
  change ((auxiliaryLayout width).wires ++ (before width).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (auxiliaryLayout width).identities ++ (before width).physicalIdx = _
  rw [before_physical]

/-- The declared source encoding counts exactly the supplied input plus all newly prepared wires. -/
theorem complete_width (width : Nat) :
    width + auxiliaryWidth width = (encoding width).width := by
  rw [encoding_width]
  unfold auxiliaryWidth prefixWidth suffixWidth
  omega

/-- The actual live context contains every canonical native source address. -/
theorem range_contained (width : Nat) :
    List.range (encoding width).width ⊆ (after width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  have complete := complete_width width
  rw [after_physical]
  by_cases beforeInput : wire < prefixWidth width
  · apply List.mem_append.mpr
    left
    change wire ∈ List.ofFn (auxiliaryPhysicalIndex width)
    let index : Fin (auxiliaryWidth width) := ⟨wire, by
      unfold auxiliaryWidth
      omega⟩
    exact List.mem_ofFn.mpr ⟨index, by
      change (if wire < prefixWidth width then wire else width + wire) = wire
      rw [if_pos beforeInput]⟩
  · by_cases inInput : wire < prefixWidth width + width
    · apply List.mem_append.mpr
      right
      change wire ∈ List.ofFn (fun index : Fin width => prefixWidth width + index.val)
      let index : Fin width := ⟨wire - prefixWidth width, by omega⟩
      exact List.mem_ofFn.mpr ⟨index, by
        change prefixWidth width + (wire - prefixWidth width) = wire
        omega⟩
    · apply List.mem_append.mpr
      left
      change wire ∈ List.ofFn (auxiliaryPhysicalIndex width)
      let index : Fin (auxiliaryWidth width) := ⟨wire - width, by omega⟩
      exact List.mem_ofFn.mpr ⟨index, by
        change (if wire - width < prefixWidth width then wire - width
          else width + (wire - width)) = wire
        rw [if_neg (by omega)]
        omega⟩

/-- Fixed source initialization at a physical identity; no input value enters this function. -/
def fixedBit (modulus wire : Nat) : Bool :=
  if wire < modulus.size + 3 then
    (BitVec.ofNat (modulus.size + 3) (4 * 2 ^ modulus.size + modulus)).getMsbD wire
  else if 2 * (modulus.size + 3) ≤ wire ∧
      wire < 2 * (modulus.size + 3) + modulus.size.size then
    (BitVec.ofNat modulus.size.size 1).getMsbD (wire - 2 * (modulus.size + 3))
  else false

/-- Prepare the literal fixed auxiliary values on precisely their allocated physical systems. -/
def preparation (modulus : Nat) : BasisPreparation (auxiliaryLayout modulus.size) where
  value index := finTwoEquiv.symm (fixedBit modulus (auxiliaryPhysicalIndex modulus.size index))

/-- One instruction allocates and prepares the fixed source auxiliary wires beside the input. -/
def circuit (modulus : Nat) : Circuit (before modulus.size) (after modulus.size) :=
  .prepare (before modulus.size) auxiliaryKey (auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size) (preparation modulus)

/-- Every newly prepared finite bit is the stated modulus-dependent value at its actual identity. -/
theorem preparation_bit (modulus : Nat) (index : Fin (auxiliaryWidth modulus.size)) :
    finTwoEquiv ((preparation modulus).value index) =
      fixedBit modulus (auxiliaryPhysicalIndex modulus.size index) :=
  finTwoEquiv.apply_symm_apply _

/-- The single actual preparation event belongs to the same fixed operation and actual layout. -/
theorem circuit_eventTrace (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).eventTrace path = [(preparation modulus).event] := rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- Actual fresh/old/reference tensor coordinates for this source allocation. -/
def joined (modulus : Nat) (fresh : (auxiliaryLayout modulus.size).register.Index)
    (old : (Register.prod (before modulus.size).register Reference).Index) :
    (Register.prod (after modulus.size).register Reference).Index :=
  prepareContextBasisEquiv (before modulus.size) Reference auxiliaryKey
    (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (fresh, old)

/-- Every output entry contains the exact pure auxiliary outer product and the old joint matrix. -/
theorem execute_joined_entry (modulus : Nat)
    (state : State (before modulus.size) Reference H)
    (newRow newColumn : (auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size).register Reference).Index) :
    ((circuit modulus).execute Reference state).quantumMarginal.matrix
      (joined modulus newRow oldRow) (joined modulus newColumn oldColumn) =
        ((preparation modulus).normalized.vec newRow *
          star ((preparation modulus).normalized.vec newColumn)) *
            state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepare_joined_entry state auxiliaryKey (auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (preparation modulus) newRow newColumn oldRow oldColumn

private theorem preparation_vec (modulus : Nat)
    (basis : (auxiliaryLayout modulus.size).register.Index) :
    (preparation modulus).normalized.vec basis =
      if basis = (preparation modulus).value then 1 else 0 :=
  NormalizedVector.ket_apply _ _

/-- The complete input-reference coherence is retained on the actually prepared auxiliary basis. -/
theorem execute_prepared_entry (modulus : Nat)
    (state : State (before modulus.size) Reference H)
    (oldRow oldColumn : (Register.prod (before modulus.size).register Reference).Index) :
    ((circuit modulus).execute Reference state).quantumMarginal.matrix
      (joined modulus (preparation modulus).value oldRow)
      (joined modulus (preparation modulus).value oldColumn) =
        state.quantumMarginal.matrix oldRow oldColumn := by
  rw [execute_joined_entry]
  simp only [preparation_vec, ↓reduceIte, star_one, one_mul]

/-- Actual preparation preserves every external-reference matrix entry, not only diagonal mass. -/
theorem execute_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference H) (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((circuit modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  Circuit.prepare_reference_entry state auxiliaryKey (auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (preparation modulus) left right

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputPreparation

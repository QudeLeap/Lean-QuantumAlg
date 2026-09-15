/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Registers
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Place the actual comparison in word/Iter/Ctrl order

The retained input-fold comparison reads Work2 and writes Iter while
restoring the existing Ctrl helper [LYL+26, sec_EEA/sub_4phase.tex:108-117;
G17, paper.tex:380-389]. The actual Gidney program declares flag/word/helper
order. This owner changes its exact logical basis and each native physical
address together to word/flag/helper order, ready for insertion of the
remaining source fields.

No new permutation gate is declared. Reindexing gives the same addressed
comparison its desired coordinates; the original ordered native events,
full arbitrary flag/helper behavior, and exact amplitudes are retained.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonFocus

noncomputable section

/-- The physical focus after moving Iter behind the complete Work2 word. -/
abbrev Data (width : Nat) := Fin (2 ^ width) × (Bool × Bool)

/-- The same actual fields in word/Iter/Ctrl order. -/
def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool)

/-- Reassociate and exchange named fields, retaining their complete values. -/
def fieldEquiv (width : Nat) : Addition.Gidney.Registers width ≃ Data width where
  toFun state := (state.2.1, (state.1, state.2.2))
  invFun state := (state.2.1, (state.1, state.2.2))
  left_inv := by rintro ⟨flag, word, helper⟩; rfl
  right_inv := by rintro ⟨word, flag, helper⟩; rfl

/-- Exact binary block splitting and reassembly, with no cardinality-selected equivalence. -/
def indexEquiv (width : Nat) :
    Fin (2 ^ (1 + (width + 1))) ≃ Fin (2 ^ (width + (1 + 1))) where
  toFun label :=
    let flagRest := (prodEquiv (m := 1) (n := width + 1)).symm label
    let wordHelper := (prodEquiv (m := width) (n := 1)).symm flagRest.2
    prodEquiv (m := width) (n := 1 + 1)
      (wordHelper.1, prodEquiv (m := 1) (n := 1) (flagRest.1, wordHelper.2))
  invFun label :=
    let wordRest := (prodEquiv (m := width) (n := 1 + 1)).symm label
    let flagHelper := (prodEquiv (m := 1) (n := 1)).symm wordRest.2
    prodEquiv (m := 1) (n := width + 1)
      (flagHelper.1, prodEquiv (m := width) (n := 1) (wordRest.1, flagHelper.2))
  left_inv := by
    intro label
    simp
  right_inv := by
    intro label
    simp

/-- The exact index map acts on the same field encoding used by the actual comparison. -/
theorem indexEquiv_encode (width : Nat) (state : Addition.Gidney.Registers width) :
    indexEquiv width ((Addition.Gidney.encoding width).encode state) =
      (encoding width).encode (fieldEquiv width state) := by
  rcases state with ⟨flag, word, helper⟩
  change indexEquiv width (prodEquiv (m := 1) (n := width + 1)
      (BinaryLabelEncoding.bool.encode flag,
        prodEquiv (m := width) (n := 1) (word, BinaryLabelEncoding.bool.encode helper))) =
    prodEquiv (m := width) (n := 1 + 1)
      (word, prodEquiv (m := 1) (n := 1)
        (BinaryLabelEncoding.bool.encode flag, BinaryLabelEncoding.bool.encode helper))
  simp only [indexEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Move the leading flag behind the word and keep every other physical address distinct. -/
def physicalIndex (width index : Nat) : Nat :=
  if index = 0 then width else if index < width + 1 then index - 1 else index

private theorem physicalIndex_injective (width : Nat) :
    Function.Injective (physicalIndex width) := by
  intro left right same
  unfold physicalIndex at same
  split at same <;> split at same
  all_goals try split at same
  all_goals try split at same
  all_goals omega

private theorem physicalIndex_within (width index : Nat) (within : index < width + 2) :
    physicalIndex width index < width + 2 := by
  unfold physicalIndex
  split
  · omega
  · split <;> omega

/-- Transport an existing program's logical basis and each native physical address together. -/
def place (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.Gidney.encoding width).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  let transported := UnitaryCircuit.reindex (indexEquiv width) body
  UnitaryCircuit.relabel transported
    { toFun := physicalIndex width
      map_layout := rfl
      old_nodup := transported.physical_idx_nodup
      new_nodup := transported.physical_idx_nodup.map (physicalIndex_injective width) }

/-- The exact field action accompanying the existing program's coordinate transport. -/
def placeStep {width : Nat}
    (action : Addition.Gidney.Registers width → Addition.Gidney.Registers width)
    (state : Data width) : Data width :=
  fieldEquiv width (action ((fieldEquiv width).symm state))

/-- The transport preserves exact amplitudes for every action certified by the original program. -/
theorem place_realizes (width : Nat)
    {body : UnitaryCircuit (Qubits (Addition.Gidney.encoding width).width)}
    {action : Addition.Gidney.Registers width → Addition.Gidney.Registers width}
    (realizes : UnitaryCircuit.Realizes (Addition.Gidney.encoding width) body action) :
    UnitaryCircuit.Realizes (encoding width) (place width body) (placeStep action) where
  apply_encoded_ket := by
    intro state
    let original := (fieldEquiv width).symm state
    have originalAction := realizes.apply_encoded_ket original
    have placed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (1 + (width + 1))) (S := Qubits (width + (1 + 1)))
      (indexEquiv width) body _ _ originalAction
    rw [indexEquiv_encode, indexEquiv_encode,
      show fieldEquiv width original = state from (fieldEquiv width).apply_symm_apply state]
      at placed
    unfold place
    rw [UnitaryCircuit.Realizes.applyNormalized_relabel]
    exact placed

/-- Every declared original address remains inside the same word and its two existing bits. -/
theorem place_physical_range (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.Gidney.encoding width).width))
    (within : body.physical_idx ⊆ List.range (width + 2)) :
    (place width body).physical_idx ⊆ List.range (width + 2) := by
  intro index present
  change index ∈ body.physical_idx.map (physicalIndex width) at present
  rcases List.mem_map.mp present with ⟨old, oldPresent, rfl⟩
  exact List.mem_range.mpr
    (physicalIndex_within width old (List.mem_range.mp (within oldPresent)))

/-- Reordering the coordinates retains the original actual native event sequence. -/
theorem place_eventTrace (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.Gidney.encoding width).width)) :
    (place width body).eventTrace = body.eventTrace := by
  simp only [place, UnitaryCircuit.relabel_eventTrace]
  exact UnitaryCircuit.reindex_eventTrace
    (R := Qubits (1 + (width + 1))) (S := Qubits (width + (1 + 1)))
    (indexEquiv width) body

/-- The same actual program retains its complete native resource pool. -/
theorem place_eventCost (width : Nat)
    (body : UnitaryCircuit (Qubits (Addition.Gidney.encoding width).width)) :
    (place width body).eventCost = body.eventCost := by
  simp only [place, UnitaryCircuit.relabel_eventCost]
  exact UnitaryCircuit.reindex_eventCost
    (R := Qubits (1 + (width + 1))) (S := Qubits (width + (1 + 1)))
    (indexEquiv width) body

/-- The actual comparison, with its logical basis and primitive addresses transformed together. -/
def program (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  place width (Addition.Gidney.comparisonProgram width pivot)

/-- Exact arithmetic in word-first order, with the helper retained for every input value. -/
def step {width : Nat} (pivot : Nat) (state : Data width) : Data width :=
  (state.1, (state.2.1 ^^ decide (state.1.val < pivot), state.2.2))

/-- The field grouping intertwines the actual comparison specification and the placed one. -/
theorem fieldEquiv_step (width pivot : Nat) (state : Addition.Gidney.Registers width) :
    fieldEquiv width (Addition.Gidney.comparisonOutput pivot state) =
      step pivot (fieldEquiv width state) := rfl

/-- The placed actual native program has exact basis action, without any phase allowance. -/
theorem program_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width pivot) (step pivot.val) :=
  (place_realizes width (Addition.Gidney.gidneyComparison_realizes width pivot)).congrStep
    (by rintro ⟨word, flag, helper⟩; rfl)

/-- All rewritten native addresses stay within the same word and its two existing bits. -/
theorem program_physical_range (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (program width pivot).physical_idx ⊆ List.range (width + 2) :=
  place_physical_range width (Addition.Gidney.comparisonProgram width pivot)
    (by
      rw [Addition.Gidney.gidneyComparison_physical]
      exact List.Subset.refl _)

/-- Reordering coordinates preserves every actual native event in its original order. -/
theorem program_eventTrace (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (program width pivot).eventTrace =
      (Addition.Gidney.comparisonProgram width pivot).eventTrace :=
  place_eventTrace width (Addition.Gidney.comparisonProgram width pivot)

/-- The placed comparison has exactly the original native resource pool. -/
theorem program_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (program width pivot).eventCost =
      (Addition.Gidney.comparisonProgram width pivot).eventCost :=
  place_eventCost width (Addition.Gidney.comparisonProgram width pivot)

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonFocus

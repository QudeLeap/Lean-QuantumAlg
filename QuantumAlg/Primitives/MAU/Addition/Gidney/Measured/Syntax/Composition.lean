/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Branch

/-!
# Chronological composition of the retained native instruction products

Append preserves the exact physical factor order and intermediate encoded
label. All measured and selected native phase characters remain explicit
[G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel}

/-- Splitting an instruction word retains its exact intermediate full encoded label. -/
lemma wordLabel_append (first second : List (Instruction encoding records)) (state : Data) :
    wordLabel (first ++ second) state = wordLabel second (wordLabel first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.labelStep state)

/-- Retained amplitudes multiply on the same chronological intermediate label. -/
lemma wordWeight_append (outcome : Fin records → Fin 2)
    (first second : List (Instruction encoding records)) (state : Data) :
    wordWeight outcome (first ++ second) state =
      wordWeight outcome first state * wordWeight outcome second (wordLabel first state) := by
  induction first generalizing state with
  | nil => simp [wordWeight, wordLabel]
  | cons instruction rest ih =>
      simp only [List.cons_append, wordWeight, wordLabel, ih, mul_assoc]

/-- The physical operator product follows the same order as the native instruction word. -/
lemma wordBranch_append (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (Reference : Register)
    (outcome : Fin records → Fin 2) (first second : List (Instruction encoding records)) :
    wordBranch physical environment Reference outcome (first ++ second) =
      wordBranch physical environment Reference outcome second *
        wordBranch physical environment Reference outcome first := by
  induction first with
  | nil => simp [wordBranch]
  | cons instruction rest ih =>
      simp only [List.cons_append, wordBranch, ih, mul_assoc]

/-- Paid native selected phases do not alter any encoded label. -/
lemma wordLabel_phase_map (pairs : List (EncodedBit encoding × Fin records)) (state : Data) :
    wordLabel (pairs.map fun pair => .phase pair.1 pair.2) state = state := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => exact ih

/-- Their exact phase product reads the original bits, with no dirty-state premise. -/
lemma wordWeight_phase_map (outcome : Fin records → Fin 2)
    (pairs : List (EncodedBit encoding × Fin records)) (state : Data) :
    wordWeight outcome (pairs.map fun pair => .phase pair.1 pair.2) state =
      (pairs.map fun pair => EncodedBit.MeasuredUncompute.character (outcome pair.2)
        (pair.1.get state)).prod := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.map_cons, wordWeight, branchWeight, labelStep, id_eq,
        List.prod_cons, ih]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

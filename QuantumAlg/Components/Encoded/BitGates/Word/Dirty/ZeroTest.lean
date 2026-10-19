/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Dirty.Conjunction.Program

/-!
# Elementary word-zero detection with restored arbitrary work

The tested word has at least two bits. The two-bit case is one Toffoli,
while wider words use the paired conjunction sandwiches. Conjugating by
source X gates tests zero and restores the full source and borrowed work.
No input cleanliness is required [dW19, qcnotes.tex:1335-1337].
-/

namespace QuantumAlg.EncodedBit.Word.ZeroTestLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}
variable (layout : ZeroTestLayout (encoding := encoding) tail)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- An elementary conjunction gate for every width at least two, with arbitrary borrowed work. -/
def borrowedAndGates : List (GateSpec encoding) :=
  if tail = 0 then [finalGate layout] else dirtyConjunctionGates layout

/-- The complete input-independent gate list for a zero predicate. -/
def borrowedZeroGates : List (GateSpec encoding) :=
  sourceXGates layout ++ borrowedAndGates layout ++ (sourceXGates layout).reverse

private lemma finalControl_two (empty : tail = 0) (state : Data) :
    finalControl layout state = sourceConjunction layout state (tail + 2) := by
  subst tail
  apply Bool.eq_iff_iff.mpr
  rw [sourceConjunction_eq_true_iff]
  simp only [finalControl, ↓reduceDIte, Bool.and_eq_true_iff]
  constructor
  · rintro ⟨first, second⟩ index
    fin_cases index
    · exact first
    · exact second
  · intro allBits
    exact ⟨allBits 0, allBits 1⟩

/-- The all-width conjunction circuit changes only the output and restores every borrowed bit. -/
lemma borrowedAndGates_step (state : Data) :
    GateSpec.stepList (borrowedAndGates layout) state =
      if sourceConjunction layout state (tail + 2) then layout.output.flip state else state := by
  by_cases empty : tail = 0
  · rw [borrowedAndGates, if_pos empty]
    change (finalGate layout).step state = _
    rw [finalGate_step_eq_if, finalControl_two layout empty]
  · rw [borrowedAndGates, if_neg empty]
    exact dirtyConjunctionGates_step layout (Nat.pos_of_ne_zero empty) state

private lemma sourceConjunction_sourceX (state : Data) :
    sourceConjunction layout (GateSpec.stepList (sourceXGates layout) state) (tail + 2) =
      decide (∀ index, (layout.source.bit index).get state = false) := by
  apply Bool.eq_iff_iff.mpr
  rw [sourceConjunction_eq_true_iff]
  simp only [sourceXGates_get_source, decide_eq_true_eq]
  apply forall_congr'
  intro index
  cases (layout.source.bit index).get state <;> decide

/-- The literal X/Toffoli circuit xors the zero predicate and restores all remaining coordinates. -/
lemma borrowedZeroGates_step (state : Data) :
    GateSpec.stepList (borrowedZeroGates layout) state =
      if ∀ index, (layout.source.bit index).get state = false
      then layout.output.flip state else state := by
  rw [borrowedZeroGates, GateSpec.stepList_append, GateSpec.stepList_append,
    borrowedAndGates_step, sourceConjunction_sourceX]
  simp only [decide_eq_true_eq]
  split
  · rw [GateSpec.stepList_flip_comm_of_bitDisjoint (sourceXGates layout).reverse layout.output
      (fun gate present => sourceXGates_output_bitDisjoint layout gate
        (List.mem_reverse.mp present)), GateSpec.stepList_reverse_stepList]
  · exact GateSpec.stepList_reverse_stepList (sourceXGates layout) state

/-- The actual complete elementary program realizes the zero predicate on every encoded label. -/
lemma borrowedZeroGates_realizes :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList physical oracles (borrowedZeroGates layout)) environment
      (fun state => if ∀ index, (layout.source.bit index).get state = false
        then layout.output.flip state else state) :=
  GateSpec.realizesList_congrStep physical oracles (environment := environment)
    (borrowedZeroGates layout) (borrowedZeroGates_step layout)

/-- Independent exact elementary gate count for the all-width borrowed-work construction. -/
lemma borrowedZeroGates_length :
    (borrowedZeroGates layout).length =
      2 * (tail + 2) + if tail = 0 then 1 else 4 * tail := by
  by_cases empty : tail = 0
  · simp [borrowedZeroGates, borrowedAndGates, empty, sourceXGates]
  · simp only [borrowedZeroGates, borrowedAndGates, if_neg empty, List.length_append,
      List.length_reverse, sourceXGates, List.length_ofFn,
      dirtyConjunctionGates_length layout (Nat.pos_of_ne_zero empty)]
    omega

end

end QuantumAlg.EncodedBit.Word.ZeroTestLayout

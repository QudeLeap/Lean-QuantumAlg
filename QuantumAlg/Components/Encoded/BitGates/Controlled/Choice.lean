/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-!
# Paid coherent choice between two literal native words

Both fixed words execute with actual positive controls, and two actual
X masks select the negative branch. A single arbitrary dirty work bit
is restored inside each native controlled instruction. Every control
and borrowed-work exclusion is stated on actual physical operands.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Two native controlled words with literal masks implement a coherent retained-bit choice. -/
def choiceGates (control work : EncodedBit encoding) (first second : List (GateSpec encoding))
    (firstControl : ∀ gate, gate ∈ first → bitDisjoint control gate)
    (firstWork : ∀ gate, gate ∈ first → bitDisjoint work gate)
    (secondControl : ∀ gate, gate ∈ second → bitDisjoint control gate)
    (secondWork : ∀ gate, gate ∈ second → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) : List (GateSpec encoding) :=
  (.x control :: listWithDirtyControl control work first firstControl firstWork different) ++
    (.x control :: listWithDirtyControl control work second secondControl secondWork different)

/-- The actual native choice performs exactly the selected complete word and restores its mask. -/
lemma choiceGates_step (control work : EncodedBit encoding)
    (first second : List (GateSpec encoding))
    (firstControl : ∀ gate, gate ∈ first → bitDisjoint control gate)
    (firstWork : ∀ gate, gate ∈ first → bitDisjoint work gate)
    (secondControl : ∀ gate, gate ∈ second → bitDisjoint control gate)
    (secondWork : ∀ gate, gate ∈ second → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (state : Data) :
    stepList (choiceGates control work first second firstControl firstWork
      secondControl secondWork different) state =
      if control.get state then stepList second state else stepList first state := by
  rw [choiceGates, stepList_append]
  change stepList (listWithDirtyControl control work second secondControl secondWork different)
    (control.flip (stepList
      (listWithDirtyControl control work first firstControl firstWork different)
      (control.flip state))) = _
  rw [listWithDirtyControl_step control work first firstControl firstWork different
    (control.flip state), get_flip_self]
  cases selected : control.get state with
  | false =>
      simp only [Bool.not_false, if_true]
      rw [stepList_flip_comm_of_bitDisjoint first control firstControl, flip_flip,
        listWithDirtyControl_step, stepList_get_of_bitDisjoint first control firstControl, selected]
      rfl
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [flip_flip, listWithDirtyControl_step, selected]
      rfl

/-- The emitted choice retains exact phase on arbitrary complete input states. -/
lemma choiceGates_realizes (control work : EncodedBit encoding)
    (first second : List (GateSpec encoding))
    (firstControl : ∀ gate, gate ∈ first → bitDisjoint control gate)
    (firstWork : ∀ gate, gate ∈ first → bitDisjoint work gate)
    (secondControl : ∀ gate, gate ∈ second → bitDisjoint control gate)
    (secondWork : ∀ gate, gate ∈ second → bitDisjoint work gate)
    (different : control.wire ≠ work.wire) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (programList (QubitLayout.canonical _) .empty (choiceGates control work first second
        firstControl firstWork secondControl secondWork different)) environment
      (fun state => if control.get state then stepList second state else stepList first state) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (choiceGates_step control work first second firstControl firstWork
      secondControl secondWork different) environment

end

end QuantumAlg.EncodedBit.GateSpec

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Address

/-!
# Top address selection without another clean enable

The original most significant address bit occupies stack position zero.
An actual X, the zero-half traversal, another X and the one-half traversal
select the original full address and restore every prefix. A k-bit lookup
therefore uses k-1 clean prefixes rather than allocating an enable bit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width wordWidth : Nat}

/-- The original top address bit controls two actual half-table traversals. -/
def splitLookupProgram (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth)) (height : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles |>.seq
    ((enabledLookupProgram frame physical oracles target (table false) (fun _ => true) height).seq
      (((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles).seq
        (enabledLookupProgram frame physical oracles target (table true) (fun _ => true) height)))

/-- XOR the constant at the original top bit and the complete remaining address. -/
def splitLookupStep (frame : SelectorFrame encoding width) (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth)) (state : Data) : Data :=
  Word.xorConstantStep target.word
    (table ((frame.stack ⟨0, by omega⟩).get state)
      (frame.addressLabelAt width 0 (by omega) 0 (by omega) state)) state

private lemma splitLookupStep_composition (frame : SelectorFrame encoding width)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth)) (state : Data) :
    enabledLookupStep frame target (table true) (fun _ => true)
      ((frame.stack ⟨0, by omega⟩).flip
        (enabledLookupStep frame target (table false) (fun _ => true)
          ((frame.stack ⟨0, by omega⟩).flip state))) =
      splitLookupStep frame target table state := by
  have readXor (constant : Fin (2 ^ wordWidth)) (input : Data) :
      (frame.stack ⟨0, by omega⟩).get (Word.xorConstantStep target.word constant input) =
        (frame.stack ⟨0, by omega⟩).get input := (target.xor_preserves constant).2 _ input
  have undo (constant : Fin (2 ^ wordWidth)) (input : Data) :
      (frame.stack ⟨0, by omega⟩).flip
          (Word.xorConstantStep target.word constant ((frame.stack ⟨0, by omega⟩).flip input)) =
        Word.xorConstantStep target.word constant input := by
    rw [target.xor_flip, EncodedBit.flip_flip]
  have leftStep : enabledLookupStep frame target (table false) (fun _ => true)
      ((frame.stack ⟨0, by omega⟩).flip state) =
      if (frame.stack ⟨0, by omega⟩).get state then (frame.stack ⟨0, by omega⟩).flip state
      else Word.xorConstantStep target.word
        (table false (frame.addressLabelAt width 0 (by omega) 0 (by omega) state))
        ((frame.stack ⟨0, by omega⟩).flip state) := by
    dsimp only [enabledLookupStep]
    rw [frame.addressLabelAt_flip_enable, EncodedBit.get_flip_self]
    cases (frame.stack ⟨0, by omega⟩).get state <;> rfl
  rw [leftStep]
  cases value : (frame.stack ⟨0, by omega⟩).get state
  · simp only [Bool.false_eq_true, if_false]
    rw [undo]
    dsimp only [enabledLookupStep, splitLookupStep]
    rw [readXor, value]
    rfl
  · simp only [if_true]
    rw [EncodedBit.flip_flip]
    dsimp only [enabledLookupStep, splitLookupStep]
    rw [value]
    rfl

/-- The actual top-bit optimization gives exact dirty-target XOR on its clean prefix subspace. -/
lemma splitLookupProgram_apply_encoded_ket (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) (environment : oracles.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    (splitLookupProgram frame physical oracles target table height).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
        NormalizedVector.ket (physical.basisEquiv.symm
          (encoding.encode (splitLookupStep frame target table state))) := by
  have firstClean := frame.cleanFrom_flip_enable state clean
  have middleClean := enabledLookupStep_clean frame target (table false) (fun _ => true)
    ((frame.stack ⟨0, by omega⟩).flip state) firstClean
  have lastClean := frame.cleanFrom_flip_enable _ middleClean
  have flipCorrect : UnitaryCircuit.Realizes encoding
      ((GateSpec.x (frame.stack ⟨0, by omega⟩)).program physical oracles) environment
      (frame.stack ⟨0, by omega⟩).flip :=
    GateSpec.realizes physical oracles (.x (frame.stack ⟨0, by omega⟩)) environment
  unfold splitLookupProgram
  rw [UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_seq,
    UnitaryCircuit.applyNormalized_seq, flipCorrect.apply_encoded_ket]
  rw [enabledLookupProgram_apply_encoded_ket _ _ _ _ _ _ _ covered environment _ firstClean]
  rw [flipCorrect.apply_encoded_ket]
  rw [enabledLookupProgram_apply_encoded_ket _ _ _ _ _ _ _ covered environment _ lastClean]
  rw [splitLookupStep_composition]

end

end QuantumAlg.EncodedBit.WindowLookup

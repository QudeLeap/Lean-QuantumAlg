/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Clean
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Word

/-!
# Unitary full-address table XOR with clean selector restoration

The actual selector invokes the physical parallel controlled mask for every
retained static table row. On the clean prefix subspace it XORs the selected
constant into an arbitrary original target word. Every address and prefix
field is preserved [Gid19, main.tex:192-205, 243-252].
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {addressWidth wordWidth : Nat}

/-- The target word occupies distinct original wires outside the complete selector frame. -/
structure LookupTarget (frame : SelectorFrame encoding addressWidth) (wordWidth : Nat) where
  word : Word encoding wordWidth
  distinct : Function.Injective (fun index => (word.bit index).wire)
  outsideAddress : ∀ bit index, (word.bit bit).wire ≠ (frame.address index).wire
  outsideStack : ∀ bit index, (word.bit bit).wire ≠ (frame.stack index).wire

namespace LookupTarget

variable {frame : SelectorFrame encoding addressWidth}

/-- Any constant XOR protects every address, enable and selector prefix field. -/
lemma xor_preserves (target : LookupTarget frame wordWidth) (constant : Fin (2 ^ wordWidth)) :
    frame.Preserves (Word.xorConstantStep target.word constant) := by
  constructor
  · intro index state
    exact Word.xorConstantStep_get_observed_of_target_ne target.word constant
      (frame.address index) (fun bit => target.outsideAddress bit index) state
  · intro index state
    exact Word.xorConstantStep_get_observed_of_target_ne target.word constant
      (frame.stack index) (fun bit => target.outsideStack bit index) state

/-- A constant XOR has no dependence on a selector prefix value. -/
lemma xor_independent (target : LookupTarget frame wordWidth)
    (constant : Fin (2 ^ wordWidth)) :
    frame.IndependentPrefixes (Word.xorConstantStep target.word constant) := by
  intro index state
  rw [← constantMaskTarget_flip target.word constant ((frame.stack index.succ).flip state),
    ← constantMaskTarget_flip target.word constant state]
  exact flipBits_flip _ _ state

end LookupTarget

/-- The actual unitary table program, including all emitted selector and target gates. -/
def enabledLookupProgram (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  frame.program physical oracles
    (fun label => wordMaskProgram physical oracles target.word target.distinct
      (frame.stack ⟨addressWidth, by omega⟩)
      (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height)
    (SelectorTrie.prune addressWidth active)

/-- The selected original full-width address controls XOR into arbitrary target data. -/
def enabledLookupStep (frame : SelectorFrame encoding addressWidth)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (state : Data) : Data :=
  let address := frame.addressLabelAt addressWidth 0 (by omega) 0 (by omega) state
  if (frame.stack ⟨0, by omega⟩).get state && active address then
    Word.xorConstantStep target.word (table address) state else state

/-- The physical selector and masks have this exact action on their stated clean input subspace. -/
lemma enabledLookupProgram_apply_encoded_ket (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (environment : oracles.Interpretation) (state : Data) (clean : frame.CleanFrom 0 state) :
    (enabledLookupProgram frame physical oracles target table active height).applyNormalized
      environment (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
        NormalizedVector.ket (physical.basisEquiv.symm
          (encoding.encode (enabledLookupStep frame target table active state))) := by
  have actual := frame.program_apply_encoded_ket_clean physical oracles
    (fun label => wordMaskProgram physical oracles target.word target.distinct
      (frame.stack ⟨addressWidth, by omega⟩)
      (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height)
    (fun label => Word.xorConstantStep target.word (table label)) environment
    (fun label => wordMaskProgram_realizes physical oracles target.word target.distinct
      (frame.stack ⟨addressWidth, by omega⟩)
      (fun bit => Ne.symm (target.outsideStack bit _)) (table label) height covered environment)
    (fun label => target.xor_preserves (table label))
    (fun label => target.xor_independent (table label))
    (SelectorTrie.prune addressWidth active) state clean
  unfold enabledLookupProgram
  rw [actual]
  dsimp only [conditionalAction, enabledLookupStep]
  rw [frame.selectedActionAt_prune]
  cases enabled : (frame.stack ⟨0, by omega⟩).get state <;>
    cases present : active (frame.addressLabelAt addressWidth 0 (by omega) 0 (by omega) state) <;>
      simp

/-- All original selector fields retain their values, including every clean prefix. -/
lemma enabledLookupStep_preserves (frame : SelectorFrame encoding addressWidth)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) :
    frame.Preserves (enabledLookupStep frame target table active) := by
  constructor
  · intro index state
    dsimp only [enabledLookupStep]
    split
    · exact (target.xor_preserves _).1 index state
    · rfl
  · intro index state
    dsimp only [enabledLookupStep]
    split
    · exact (target.xor_preserves _).2 index state
    · rfl

/-- The exact selected payload restores all initially clean prefixes by unitary execution. -/
lemma enabledLookupStep_clean (frame : SelectorFrame encoding addressWidth)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (state : Data) (clean : frame.CleanFrom 0 state) :
    frame.CleanFrom 0 (enabledLookupStep frame target table active state) :=
  frame.cleanFrom_preserved _ (enabledLookupStep_preserves frame target table active) 0 state clean

end

end QuantumAlg.EncodedBit.WindowLookup

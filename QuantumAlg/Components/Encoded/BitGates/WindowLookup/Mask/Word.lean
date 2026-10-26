/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Resources

/-!
# Parallel controlled constant XOR on the original target word

Only set-bit positions participate in the actual CNOT conjugation. The
original target may contain arbitrary data; every bit outside the selected
mask, including the selector, retains its value. No clean fanout is used.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual selected target positions, in the original constant-bit order. -/
def constantMaskTarget (target : Word encoding width) (constant : Fin (2 ^ width)) :
    Fin (Word.constantOneIndices constant).length → EncodedBit encoding :=
  fun index => target.bit ((Word.constantOneIndices constant).get index)

/-- Filtering an injective target word preserves physical wire injectivity. -/
lemma constantMaskTarget_distinct (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (constant : Fin (2 ^ width)) :
    Function.Injective (fun index => (constantMaskTarget target constant index).wire) := by
  intro first second equal
  exact (Word.constantOneIndices_nodup constant).injective_get (distinct equal)

private lemma constantMaskTarget_prefix (target : Word encoding width)
    (constant : Fin (2 ^ width)) :
    prefixBits (constantMaskTarget target constant) (Word.constantOneIndices constant).length =
      (Word.constantOneIndices constant).map target.bit := by
  unfold prefixBits constantMaskTarget
  simp only [Nat.min_self, Fin.val_cast]
  rw [List.ofFn_comp', List.ofFn_get]

private lemma stepList_x_eq_flipBits (bits : List (EncodedBit encoding)) (state : Data) :
    GateSpec.stepList (bits.map GateSpec.x) state = flipBits bits state := by
  induction bits generalizing state with
  | nil => rfl
  | cons first rest ih => exact ih (first.flip state)

/-- The full propagated physical mask is precisely the existing word XOR action. -/
lemma constantMaskTarget_flip (target : Word encoding width) (constant : Fin (2 ^ width))
    (state : Data) :
    flipBits (prefixBits (constantMaskTarget target constant)
      (Word.constantOneIndices constant).length) state =
        Word.xorConstantStep target constant state := by
  rw [constantMaskTarget_prefix]
  unfold Word.xorConstantStep Word.xorConstantGates
  simpa only [List.map_map, Function.comp_def] using
    (stepList_x_eq_flipBits ((Word.constantOneIndices constant).map target.bit) state).symm

/-- The controlled constant XOR uses only the actual original target positions. -/
def wordMaskProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  maskedXProgram physical oracles (constantMaskTarget target constant)
    (constantMaskTarget_distinct target distinct constant) selector
    (fun index => outside ((Word.constantOneIndices constant).get index)) height

/-- Exact phase and complete dirty-target behavior of the actual parallel masked word. -/
lemma wordMaskProgram_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) (covered : width ≤ 2 ^ height)
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (wordMaskProgram physical oracles target distinct selector outside constant height)
      environment (fun state => if selector.get state then
        Word.xorConstantStep target constant state else state) := by
  have realizes := maskedXProgram_realizes physical oracles (constantMaskTarget target constant)
    (constantMaskTarget_distinct target distinct constant) selector
    (fun index => outside ((Word.constantOneIndices constant).get index)) height
    ((Word.constantOneIndices_length_le constant).trans covered) environment
  refine ⟨fun state => ?_⟩
  unfold wordMaskProgram
  rw [realizes.apply_encoded_ket]
  simp only [constantMaskTarget_flip]

/-- A nonzero mask costs twice its population count minus one actual native CNOTs. -/
lemma wordMaskProgram_eventTrace (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) (covered : width ≤ 2 ^ height) :
    (wordMaskProgram physical oracles target distinct selector outside constant height).eventTrace =
      List.replicate (if (Word.constantOneIndices constant).length = 0 then 0
        else 2 * (Word.constantOneIndices constant).length - 1) (.gate .cnot) :=
  maskedXProgram_eventTrace _ _ _ _ _ _ _
    ((Word.constantOneIndices_length_le constant).trans covered)

/-- The same actual circuit has logarithmic native dependence depth. -/
lemma wordMaskProgram_quantumTime_le (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) :
    UnitaryCircuit.evaluatedEventDepth Resource.Event.quantumDuration
      (wordMaskProgram physical oracles target distinct selector outside constant height) ≤
        2 * height + 1 :=
  maskedXProgram_quantumTime_le _ _ _ _ _ _ _

end

end QuantumAlg.EncodedBit.WindowLookup

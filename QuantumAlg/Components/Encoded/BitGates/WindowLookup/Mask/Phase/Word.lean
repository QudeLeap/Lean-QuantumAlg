/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase.Resources
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Word

/-!
# Actual constant-word parity phases and unary selection

Only the set-bit target positions participate in the native parity fan-in.
On the explicitly promised unary subspace, their parity is the selected
constant bit. The phase law itself holds on arbitrary dirty target words.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The parity of precisely the original target positions selected by the constant word. -/
def wordMaskParity (target : Word encoding width) (constant : Fin (2 ^ width))
    (state : Data) : Bool :=
  bitParity ((Word.constantOneIndices constant).map target.bit) state

/-- The native word phase uses the same actual filtered target positions as masked XOR. -/
def wordMaskParityPhaseProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  maskedParityPhaseProgram physical oracles (constantMaskTarget target constant)
    (constantMaskTarget_distinct target distinct constant) selector
    (fun index => outside ((Word.constantOneIndices constant).get index)) height

/-- The actual word phase is exact and restores every original target value. -/
lemma wordMaskParityPhaseProgram_applyVec (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (selector : EncodedBit encoding)
    (outside : ∀ index, selector.wire ≠ (target.bit index).wire)
    (constant : Fin (2 ^ width)) (height : Nat) (covered : width ≤ 2 ^ height)
    (environment : oracles.Interpretation) (state : Data) :
    UnitaryCircuit.applyVec
      (wordMaskParityPhaseProgram physical oracles target distinct selector outside constant height)
        environment (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if selector.get state = true ∧ wordMaskParity target constant state = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  have actual := maskedParityPhaseProgram_applyVec physical oracles
    (constantMaskTarget target constant)
    (constantMaskTarget_distinct target distinct constant) selector
    (fun index => outside ((Word.constantOneIndices constant).get index)) height
    ((Word.constantOneIndices_length_le constant).trans covered) environment state
  unfold wordMaskParityPhaseProgram
  rw [actual, constantMaskTarget_prefix]
  rfl

private lemma bitParity_oneHot (target : Word encoding width)
    (indices : List (Fin width)) (distinct : indices.Nodup) (label : Fin width) (state : Data)
    (oneHot : ∀ index, (target.bit index).get state = decide (index = label)) :
    bitParity (indices.map target.bit) state = decide (label ∈ indices) := by
  induction indices with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      change ((target.bit first).get state ^^ bitParity (rest.map target.bit) state) = _
      rw [oneHot, ih tailDistinct]
      by_cases same : first = label
      · subst first
        simp [absent]
      · simp [same, Ne.symm same]

/-- A unary input makes the exact physical mask parity equal the selected constant bit. -/
lemma wordMaskParity_oneHot (target : Word encoding width) (constant : Fin (2 ^ width))
    (label : Fin width) (state : Data)
    (oneHot : ∀ index, (target.bit index).get state = decide (index = label)) :
    wordMaskParity target constant state = constant.val.testBit label.val := by
  rw [wordMaskParity, bitParity_oneHot target _ (Word.constantOneIndices_nodup constant)
    label state oneHot]
  by_cases member : label ∈ Word.constantOneIndices constant
  · rw [Word.mem_constantOneIndices] at member
    simp [member]
  · have bitFalse : constant.val.testBit label.val = false := by
      cases bitValue : constant.val.testBit label.val
      · rfl
      · exact (member ((Word.mem_constantOneIndices constant label).mpr bitValue)).elim
    simp [member, bitFalse]

end

end QuantumAlg.EncodedBit.WindowLookup

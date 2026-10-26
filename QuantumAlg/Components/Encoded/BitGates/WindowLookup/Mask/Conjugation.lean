/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Network

/-!
# Actual controlled masked X on arbitrary dirty target words

An inverse target-only CNOT word, one selector-to-pivot CNOT, and the forward
word give the exact controlled mask. No target is initialized or copied to a
new clean system. All dependence claims refer to the original actual gates.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Conjugate the one actual selector CNOT by the original physical layer word. -/
def conjugatedMaskProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (layers : List (CnotLayer encoding)) (selector pivot : EncodedBit encoding)
    (different : selector.wire ≠ pivot.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (layerWordProgram physical oracles (inverseLayerWord layers)).seq
    (((GateSpec.cnot selector pivot different).program physical oracles).seq
      (layerWordProgram physical oracles layers))

private lemma conjugated_step (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (targets : List (EncodedBit encoding))
    (outside : ∀ gate ∈ layerWordGates layers, GateSpec.bitDisjoint selector gate)
    (propagates : ∀ state, GateSpec.stepList (layerWordGates layers) (pivot.flip state) =
      flipBits targets (GateSpec.stepList (layerWordGates layers) state)) (state : Data) :
    GateSpec.stepList (layerWordGates layers)
      (cnotStep selector pivot (GateSpec.stepList (layerWordGates layers).reverse state)) =
      if selector.get state then flipBits targets state else state := by
  have backward_get := GateSpec.stepList_get_of_bitDisjoint
    (layerWordGates layers).reverse selector
    (fun gate member => outside gate (List.mem_reverse.mp member)) state
  have cancel := GateSpec.stepList_reverse_stepList (layerWordGates layers).reverse state
  rw [List.reverse_reverse] at cancel
  unfold cnotStep
  rw [backward_get]
  split
  · rw [propagates, cancel]
  · exact cancel

/-- The conjugation has its exact all-input controlled-X action on the complete bank. -/
lemma conjugatedMaskProgram_realizes (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire)
    (targets : List (EncodedBit encoding))
    (outside : ∀ gate ∈ layerWordGates layers, GateSpec.bitDisjoint selector gate)
    (propagates : ∀ state, GateSpec.stepList (layerWordGates layers) (pivot.flip state) =
      flipBits targets (GateSpec.stepList (layerWordGates layers) state))
    (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (conjugatedMaskProgram physical oracles layers selector pivot different) environment
      (fun state => if selector.get state then flipBits targets state else state) := by
  have backward := layerWordProgram_realizes physical oracles (inverseLayerWord layers) environment
  rw [inverseLayerWord_gates] at backward
  have composed := UnitaryCircuit.Realizes.seq backward
    (UnitaryCircuit.Realizes.seq
      (GateSpec.realizes physical oracles (.cnot selector pivot different) environment)
      (layerWordProgram_realizes physical oracles layers environment))
  refine ⟨fun state => ?_⟩
  unfold conjugatedMaskProgram
  rw [composed.apply_encoded_ket]
  rw [show GateSpec.step (.cnot selector pivot different) = cnotStep selector pivot from rfl]
  rw [conjugated_step layers selector pivot targets outside propagates]

variable {count : Nat}

private lemma doublingWord_outside (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (gate : GateSpec encoding)
    (member : gate ∈ layerWordGates (doublingWord target distinct height)) :
    GateSpec.bitDisjoint selector gate := by
  induction height with
  | zero => simp [doublingWord, layerWordGates] at member
  | succ height ih =>
      simp only [doublingWord, layerWordGates, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_append] at member
      rcases member with old | current
      · exact ih old
      · obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp current
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp edgePresent
        exact ⟨Ne.symm (outside _), Ne.symm (outside _)⟩

private lemma prefixBits_one (target : Fin count → EncodedBit encoding) (positive : 0 < count) :
    prefixBits target 1 = [target ⟨0, positive⟩] := by
  unfold prefixBits
  simp only [Nat.min_eq_left positive, List.ofFn_succ, List.ofFn_zero, Fin.val_cast, Fin.val_zero]

private lemma doublingWord_root (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (positive : 0 < count) (height : Nat) (covered : count ≤ 2 ^ height) (state : Data) :
    GateSpec.stepList (layerWordGates (doublingWord target distinct height))
      ((target ⟨0, positive⟩).flip state) =
      flipBits (prefixBits target count)
        (GateSpec.stepList (layerWordGates (doublingWord target distinct height)) state) := by
  have same := doublingWord_propagates target distinct height state
  rw [prefixBits_one target positive] at same
  simpa only [flipBits, prefixBits, Nat.min_eq_right covered, Nat.min_self, Fin.val_cast] using same

/-- The canonical physical masked-X word; an empty mask executes identity. -/
def maskedXProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  if positive : 0 < count then
    conjugatedMaskProgram physical oracles (doublingWord target distinct height)
      selector (target ⟨0, positive⟩) (outside _)
  else UnitaryCircuit.identity _ _ _

/-- Arbitrary original target values are XORed with the complete mask, with exact phase. -/
lemma maskedXProgram_realizes (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (maskedXProgram physical oracles target distinct selector outside height) environment
      (fun state => if selector.get state then
        flipBits (prefixBits target count) state else state) := by
  unfold maskedXProgram
  split
  · exact conjugatedMaskProgram_realizes physical oracles _ selector _ _ _
      (doublingWord_outside target distinct selector outside height)
      (doublingWord_root target distinct ‹0 < count› height covered) environment
  · have zero : count = 0 := by omega
    subst count
    simp only [prefixBits, Nat.min_zero, List.ofFn_zero, flipBits, ite_self]
    refine ⟨fun state => ?_⟩
    exact (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model oracles
      encoding physical environment).apply_encoded_ket state

/-- The native quantum time is logarithmic in mask width, without clean fanout storage. -/
lemma maskedXProgram_quantumTime_le (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) :
    (maskedXProgram physical oracles target distinct selector outside height).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 2 * height + 1 := by
  unfold maskedXProgram
  split
  · have forward := layerWordProgram_quantumTime_le physical oracles
      (doublingWord target distinct height)
    have backward := layerWordProgram_quantumTime_le physical oracles
      (inverseLayerWord (doublingWord target distinct height))
    rw [doublingWord_length] at forward
    rw [inverseLayerWord_length, doublingWord_length] at backward
    rw [conjugatedMaskProgram, UnitaryCircuit.evaluatedEventDepth_seq,
      UnitaryCircuit.evaluatedEventDepth_seq]
    have center : ((GateSpec.cnot selector (target ⟨0, ‹0 < count›⟩)
        (outside _)).program physical oracles).evaluatedEventDepth
          Resource.Event.quantumDuration = 1 := by rfl
    rw [center]
    omega
  · exact Nat.zero_le _

end

end QuantumAlg.EncodedBit.WindowLookup

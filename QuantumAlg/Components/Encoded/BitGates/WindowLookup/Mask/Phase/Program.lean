/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Phase.Doubling

/-!
# Actual controlled masked parity phase with restored dirty targets

A target-only physical parity fan-in, literal H/CNOT/H at its original pivot,
and the inverse fan-in emit the exact selector-controlled mask-parity sign.
Every original target value is restored, without introducing a clean system.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Execute the actual parity word, addressed controlled Z, and the inverse parity word. -/
def conjugatedParityPhaseProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (layers : List (CnotLayer encoding)) (selector pivot : EncodedBit encoding)
    (different : selector.wire ≠ pivot.wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  (layerWordProgram physical oracles layers).seq
    ((selector.controlledZ physical oracles pivot different).seq
      (layerWordProgram physical oracles (inverseLayerWord layers)))

/-- The literal parity conjugation has its exact all-input phase and restores every system. -/
lemma conjugatedParityPhaseProgram_applyVec (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (layers : List (CnotLayer encoding))
    (selector pivot : EncodedBit encoding) (different : selector.wire ≠ pivot.wire)
    (parity : Data → Bool)
    (preserves : ∀ state, selector.get (GateSpec.stepList (layerWordGates layers) state) =
      selector.get state)
    (readsParity : ∀ state, pivot.get (GateSpec.stepList (layerWordGates layers) state) =
      parity state)
    (environment : oracles.Interpretation) (state : Data) :
    (conjugatedParityPhaseProgram physical oracles layers selector pivot different).applyVec
      environment (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if selector.get state = true ∧ parity state = true then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  have forward (input : Data) :
      (layerWordProgram physical oracles layers).applyVec environment
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode input))).vec =
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm
            (encoding.encode (GateSpec.stepList (layerWordGates layers) input)))).vec := by
    exact congrArg NormalizedVector.vec
      ((layerWordProgram_realizes physical oracles layers environment).apply_encoded_ket input)
  have backward (input : Data) :
      (layerWordProgram physical oracles (inverseLayerWord layers)).applyVec environment
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode input))).vec =
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode
            (GateSpec.stepList (layerWordGates (inverseLayerWord layers)) input)))).vec := by
    exact congrArg NormalizedVector.vec (UnitaryCircuit.Realizes.apply_encoded_ket
      (layerWordProgram_realizes physical oracles (inverseLayerWord layers) environment) input)
  unfold conjugatedParityPhaseProgram
  rw [UnitaryCircuit.applyVec_seq, forward, UnitaryCircuit.applyVec_seq,
    controlledZ_applyVec_encoded_ket, UnitaryCircuit.applyVec_smul, backward,
    inverseLayerWord_gates, GateSpec.stepList_reverse_stepList, preserves, readsParity]

variable {count : Nat}

private lemma parityFanInWord_outside (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (gate : GateSpec encoding)
    (member : gate ∈ layerWordGates (parityFanInWord (doublingWord target distinct height))) :
    GateSpec.bitDisjoint selector gate := by
  induction height with
  | zero => simp [doublingWord, parityFanInWord, layerWordGates] at member
  | succ height ih =>
      have unroll : parityFanInWord (doublingWord target distinct (height + 1)) =
          (doublingLayer target distinct (2 ^ height) (Nat.pow_pos (by decide))).transpose ::
            parityFanInWord (doublingWord target distinct height) := by
        simp only [doublingWord, parityFanInWord, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.map_cons,
          List.cons_append, List.nil_append]
      rw [unroll] at member
      simp only [layerWordGates, List.flatMap_cons, List.mem_append] at member
      rcases member with current | previous
      · obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp current
        obtain ⟨original, originalPresent, rfl⟩ := List.mem_map.mp edgePresent
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp originalPresent
        exact ⟨Ne.symm (outside _), Ne.symm (outside _)⟩
      · exact ih previous

/-- The actual logarithmic controlled mask-parity program, including the empty-mask identity. -/
def maskedParityPhaseProgram (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  if positive : 0 < count then
    conjugatedParityPhaseProgram physical oracles
      (parityFanInWord (doublingWord target distinct height)) selector (target ⟨0, positive⟩)
        (outside _)
  else UnitaryCircuit.identity _ _ _

/-- All original dirty targets are restored and the exact complete-mask sign is retained. -/
lemma maskedParityPhaseProgram_applyVec (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (selector : EncodedBit encoding) (outside : ∀ index, selector.wire ≠ (target index).wire)
    (height : Nat) (covered : count ≤ 2 ^ height) (environment : oracles.Interpretation)
    (state : Data) :
    (maskedParityPhaseProgram physical oracles target distinct selector outside height).applyVec
      environment (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec =
      (if selector.get state = true ∧ bitParity (prefixBits target count) state = true
        then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  unfold maskedParityPhaseProgram
  split
  · exact conjugatedParityPhaseProgram_applyVec physical oracles _ selector _ _ _
      (GateSpec.stepList_get_of_bitDisjoint _ selector
        (parityFanInWord_outside target distinct selector outside height))
      (parityFanInWord_pivot target distinct _ height covered) environment state
  · have empty : count = 0 := by omega
    subst count
    simp only [prefixBits, Nat.min_self, List.ofFn_zero, bitParity, Bool.false_eq_true,
      and_false, if_false, one_smul, UnitaryCircuit.applyVec_identity]

end

end QuantumAlg.EncodedBit.WindowLookup

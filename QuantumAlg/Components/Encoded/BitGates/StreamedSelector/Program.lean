/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Protection
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Semantics
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.Flags

/-! # Actual native streaming traversal with controlled payloads and boundary toggles -/

namespace QuantumAlg.EncodedBit.StreamedSelector

noncomputable section

open WindowLookup GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Native payloads keep every physical selector wire disjoint from their source actions. -/
structure PayloadFamily (frame : SelectorFrame encoding width) where
  payload : Fin (2 ^ width) → ControlledPayload encoding
  activeAddress : ∀ label index,
    (payload label).active.wire ≠ (frame.address index).wire
  activeStack : ∀ label index,
    (payload label).active.wire ≠ (frame.stack index).wire
  sourceAddress : ∀ label index gate, gate ∈ (payload label).source →
    bitDisjoint (frame.address index) gate
  sourceStack : ∀ label index gate, gate ∈ (payload label).source →
    bitDisjoint (frame.stack index) gate

namespace PayloadFamily

variable {frame : SelectorFrame encoding width}

/-- The actual leaf prefix controls the final moving-flag CNOT. -/
def callback (family : PayloadFamily frame) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (label : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  programList physical oracles ((family.payload label).callbackGates
    (frame.stack ⟨width, by omega⟩) (family.activeStack label _).symm)

/-- Compile the original native unary traversal on its unchanged carrier. -/
def program (family : PayloadFamily frame) (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (tree : SelectorTrie width) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  frame.program physical oracles (family.callback physical oracles) tree

private lemma preserves (family : PayloadFamily frame) (label : Fin (2 ^ width))
    (selected : Bool) : frame.Preserves ((family.payload label).callbackStep selected) :=
  (family.payload label).callbackStep_preserves frame (family.activeAddress label)
    (family.activeStack label) (family.sourceAddress label) (family.sourceStack label) selected

private lemma independent (family : PayloadFamily frame) (label : Fin (2 ^ width))
    (selected : Bool) :
    frame.IndependentPrefixes ((family.payload label).callbackStep selected) :=
  (family.payload label).callbackStep_independent frame
    (fun index => family.activeStack label index.succ)
    (fun index => family.sourceStack label index.succ) selected

/-- Exact native semantics retain every visit, including all false-selection actions. -/
lemma program_apply_encoded_ket (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) (tree : SelectorTrie width)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    (family.program physical oracles tree).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
      NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode
        (foldAt frame (fun label => (family.payload label).callbackStep) tree 0 (by omega) 0
          (by omega) ((frame.stack ⟨0, by omega⟩).get state) state))) := by
  apply program_apply_encoded_ket_streamed_clean frame physical oracles
    (family.callback physical oracles) (fun label => (family.payload label).callbackStep)
    environment
  · intro label
    exact (family.payload label).callback_realizes _ (family.activeStack label _).symm
      (family.sourceStack label _) physical oracles environment
  · exact family.preserves
  · exact family.independent
  · exact clean

/-- The actual circuit's moving boundary is precisely the original full-width quantum address. -/
lemma program_apply_encoded_ket_flags (family : PayloadFamily frame)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (environment : oracles.Interpretation) (tree : SelectorTrie width)
    (state : Data) (clean : frame.CleanFrom 0 state) :
    (family.program physical oracles tree).applyNormalized environment
      (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode state))) =
      NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode
        ((labelsAt tree 0 (by omega)).foldl (fun value label =>
          (family.payload label).callbackStep
            (((frame.stack ⟨0, by omega⟩).get state) && decide
              (label = frame.addressLabelAt width 0 (by omega) 0 (by omega) state)) value)
          state))) := by
  rw [family.program_apply_encoded_ket physical oracles environment tree state clean]
  rw [foldAt_eq_bits frame (fun label => (family.payload label).callbackStep) family.preserves
    (fun index => (frame.address index).get state) tree 0 (by omega) 0 (by omega)
    ((frame.stack ⟨0, by omega⟩).get state) state (fun _ => rfl)]
  rw [foldBitsAt_eq_label_flags frame _ state (fun _ => rfl)]

end PayloadFamily

end

end QuantumAlg.EncodedBit.StreamedSelector

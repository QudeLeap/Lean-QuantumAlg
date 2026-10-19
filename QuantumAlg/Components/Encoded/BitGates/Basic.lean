/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.QubitPrimitive
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.NormNum

/-!
# Encoded semantic bits

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

/-- A semantic Boolean component of an encoded data type, tied to one concrete
wire of the binary basis-label encoding. -/
structure EncodedBit {Data : Type} (encoding : BinaryLabelEncoding Data) where
  /-- Wire containing this bit in the encoded computational-basis label. -/
  wire : Fin encoding.width
  /-- Semantic Boolean readout of the bit. -/
  get : Data -> Bool
  /-- Semantic update corresponding to flipping exactly this bit. -/
  flip : Data -> Data
  /-- The semantic readout agrees with the encoded basis bit. -/
  get_eq :
    ∀ x : Data,
      (encoding.encode x).val.testBit (WireAddress.bitIndex wire).val = get x
  /-- The semantic flip agrees with flipping the corresponding encoded wire. -/
  encode_flip :
    ∀ x : Data,
      encoding.encode (flip x) = WireAddress.flipBit wire (encoding.encode x)

namespace EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Semantic action of CNOT for encoded semantic bits. -/
def cnotStep (control target : EncodedBit encoding) (x : Data) : Data :=
  if control.get x then target.flip x else x

/-- Semantic action of Toffoli for encoded semantic bits. -/
def toffoliStep (controlA controlB target : EncodedBit encoding) (x : Data) :
    Data :=
  if controlA.get x && controlB.get x then target.flip x else x

/-- Flipping an encoded bit toggles its own semantic readout. -/
lemma get_flip_self (bit : EncodedBit encoding) (x : Data) :
    bit.get (bit.flip x) = !bit.get x := by
  rw [← bit.get_eq (bit.flip x), bit.encode_flip x]
  rw [WireAddress.bit_flipBit_self, bit.get_eq x]

/-- Flipping one encoded bit preserves the readout of a distinct wire. -/
lemma get_flip_of_wire_ne (target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (target.flip x) = observed.get x := by
  rw [← observed.get_eq (target.flip x), target.encode_flip x]
  rw [WireAddress.bit_flipBit_of_ne hne, observed.get_eq x]

/-- CNOT toggles its target readout exactly when the control readout is true. -/
lemma cnotStep_get_target (control target : EncodedBit encoding) (x : Data) :
    target.get (cnotStep control target x) =
      (target.get x ^^ control.get x) := by
  by_cases hcontrol : control.get x
  · rw [cnotStep, if_pos hcontrol, get_flip_self, hcontrol]
    cases target.get x <;> rfl
  · rw [cnotStep, if_neg hcontrol]
    simp [hcontrol]

/-- CNOT preserves the readout of any encoded bit whose wire is not the
target wire. -/
lemma cnotStep_get_of_target_ne (control target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (cnotStep control target x) = observed.get x := by
  unfold cnotStep
  by_cases hcontrol : control.get x
  · simp [hcontrol, get_flip_of_wire_ne target observed hne]
  · simp [hcontrol]

/-- Toffoli toggles its target readout exactly when both control readouts are
true. -/
lemma toffoliStep_get_target
    (controlA controlB target : EncodedBit encoding) (x : Data) :
    target.get (toffoliStep controlA controlB target x) =
      (target.get x ^^ (controlA.get x && controlB.get x)) := by
  by_cases hcontrols : controlA.get x && controlB.get x
  · rw [toffoliStep, if_pos hcontrols, get_flip_self, hcontrols]
    cases target.get x <;> rfl
  · rw [toffoliStep, if_neg hcontrols]
    simp [hcontrols]

/-- Toffoli preserves the readout of any encoded bit whose wire is not the
target wire. -/
lemma toffoliStep_get_of_target_ne
    (controlA controlB target observed : EncodedBit encoding)
    (hne : target.wire ≠ observed.wire) (x : Data) :
    observed.get (toffoliStep controlA controlB target x) =
      observed.get x := by
  unfold toffoliStep
  by_cases hcontrols : controlA.get x && controlB.get x
  · simp [hcontrols, get_flip_of_wire_ne target observed hne]
  · simp [hcontrols]

/-- Relabel an encoded bit along an equivalence of semantic label types. -/
def relabel {Other : Type} (bit : EncodedBit encoding) (layout : Other ≃ Data) :
    EncodedBit (encoding.relabel layout) where
  wire := bit.wire
  get := fun x => bit.get (layout x)
  flip := fun x => layout.symm (bit.flip (layout x))
  get_eq := by
    intro x
    simpa [BinaryLabelEncoding.relabel] using bit.get_eq (layout x)
  encode_flip := by
    intro x
    simpa [BinaryLabelEncoding.relabel] using bit.encode_flip (layout x)

variable {layout : QubitLayout encoding.width} {oracles : OracleModel}

/-- One addressed X/NOT gate realizes the semantic flip for an encoded bit. -/
lemma x_realizes (bit : EncodedBit encoding) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.x bit.wire).circuit layout oracles) environment bit.flip where
  apply_encoded_ket := by
    intro x
    rw [QubitPrimitive.circuit_applyNormalized_ket]
    apply congrArg (fun label : Fin (2 ^ encoding.width) =>
      NormalizedVector.ket (R := layout.toQuantum.register) (layout.basisEquiv.symm label))
    exact (bit.encode_flip x).symm

/-- One addressed CNOT gate realizes semantic controlled flip for encoded bits. -/
lemma cnot_realizes (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.cnot control.wire target.wire hct).circuit layout oracles) environment
      (cnotStep control target) where
  apply_encoded_ket := by
    intro x
    rw [QubitPrimitive.circuit_applyNormalized_ket]
    apply congrArg (fun label : Fin (2 ^ encoding.width) =>
      NormalizedVector.ket (R := layout.toQuantum.register) (layout.basisEquiv.symm label))
    by_cases hcontrol : control.get x
    · simp [QubitPrimitive.applyLabel, WireAddress.cnotMap,
        control.get_eq x, cnotStep, hcontrol, target.encode_flip]
    · simp [QubitPrimitive.applyLabel, WireAddress.cnotMap,
        control.get_eq x, cnotStep, hcontrol]

/-- One addressed Toffoli gate realizes semantic double-controlled flip for
encoded bits. -/
lemma toffoli_realizes (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire) (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.toffoli controlA.wire controlB.wire target.wire
        hab ha hb).circuit layout oracles) environment
      (toffoliStep controlA controlB target) where
  apply_encoded_ket := by
    intro x
    rw [QubitPrimitive.circuit_applyNormalized_ket]
    apply congrArg (fun label : Fin (2 ^ encoding.width) =>
      NormalizedVector.ket (R := layout.toQuantum.register) (layout.basisEquiv.symm label))
    by_cases hcontrols : controlA.get x && controlB.get x
    · simp [QubitPrimitive.applyLabel, WireAddress.toffoliMap,
        controlA.get_eq x, controlB.get_eq x, toffoliStep, hcontrols,
        target.encode_flip]
    · simp [QubitPrimitive.applyLabel, WireAddress.toffoliMap,
        controlA.get_eq x, controlB.get_eq x, toffoliStep, hcontrols]

/-- Proof that the actual X circuit realizes the encoded semantic flip. -/
lemma xWitness (bit : EncodedBit encoding) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.x bit.wire).circuit layout oracles) environment bit.flip :=
  x_realizes bit environment

/-- Proof that the actual CNOT circuit realizes semantic controlled flip. -/
lemma cnotWitness (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.cnot control.wire target.wire hct).circuit layout oracles) environment
      (cnotStep control target) :=
  cnot_realizes control target hct environment

/-- Proof that the actual Toffoli circuit realizes semantic double control. -/
lemma toffoliWitness (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire) (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      ((QubitPrimitive.toffoli controlA.wire controlB.wire target.wire
        hab ha hb).circuit layout oracles) environment
      (toffoliStep controlA controlB target) :=
  toffoli_realizes controlA controlB target hab ha hb environment

/-- Flipping an encoded bit twice restores the semantic state. -/
lemma flip_flip (bit : EncodedBit encoding) (x : Data) :
    bit.flip (bit.flip x) = x := by
  apply encoding.encode_injective
  rw [bit.encode_flip, bit.encode_flip, WireAddress.flipBit_flipBit]

/-- Semantic flips of encoded bits commute. -/
lemma flip_comm (left right : EncodedBit encoding) (x : Data) :
    left.flip (right.flip x) = right.flip (left.flip x) := by
  apply encoding.encode_injective
  rw [left.encode_flip, right.encode_flip, right.encode_flip,
    left.encode_flip, WireAddress.flipBit_comm]

/-- A semantic CNOT step is self-inverse. -/
lemma cnotStep_cnotStep
    (control target : EncodedBit encoding)
    (hct : control.wire ≠ target.wire) (x : Data) :
    cnotStep control target (cnotStep control target x) = x := by
  unfold cnotStep
  by_cases hcontrol : control.get x
  · rw [if_pos hcontrol]
    have hcontrol' : control.get (target.flip x) = true := by
      rw [get_flip_of_wire_ne target control (Ne.symm hct), hcontrol]
    rw [if_pos hcontrol']
    exact flip_flip target x
  · rw [if_neg hcontrol]
    rw [if_neg hcontrol]

/-- A semantic Toffoli step is self-inverse. -/
lemma toffoliStep_toffoliStep
    (controlA controlB target : EncodedBit encoding)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) (x : Data) :
    toffoliStep controlA controlB target
        (toffoliStep controlA controlB target x) = x := by
  have ha' : controlA.get (target.flip x) = controlA.get x := by
    rw [get_flip_of_wire_ne target controlA (Ne.symm ha)]
  have hb' : controlB.get (target.flip x) = controlB.get x := by
    rw [get_flip_of_wire_ne target controlB (Ne.symm hb)]
  unfold toffoliStep
  cases hA : controlA.get x <;>
    cases hB : controlB.get x <;>
    simp [hA, hB, ha', hb', flip_flip]

end EncodedBit

end

end QuantumAlg

end

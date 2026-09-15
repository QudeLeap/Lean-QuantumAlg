/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Registers

/-!
# Exact binary encoding of both arithmetic windows and their complete complement

The first factor is the actual TTK Work2-source/Work1-target/Sign interface.
The complement explicitly encodes both word prefixes and suffixes, all
four length words, both phases, Iter, and Ctrl. Literal field splitting
and reassembly define the basis equivalence; no cardinality-only cast or
input-dependent allocation is used
[LYL+26, sec_EEA/sub_regshare.tex:16-26,263-278;
TTK09, qic-loglogaddition-quant.tex:285-318].

The existing Ctrl and arbitrary Iter bits have concrete lenses in this
same encoding. They can be used by the subsequent native controlled gate
list while the whole grouped frame is transported to its original wires.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowEncoding

noncomputable section

open ArithmeticWindowRegisters BinaryLabelEncoding

/-- Encode every physical bit outside the two selected windows and Sign. -/
@[implicit_reducible]
def complementEncoding {width : Nat} (window : Window width) :
    BinaryLabelEncoding (Complement window) :=
  prod (prod (wordEncoding window.above) (wordEncoding window.below))
    (prod (prod (wordEncoding window.above) (wordEncoding window.below))
      (prod (lengthPairEncoding width) (prod (lengthPairEncoding width) flagEncoding)))

private theorem complement_surjective {width : Nat} (window : Window width) :
    Function.Surjective (complementEncoding window).encode :=
  prod_surjective _ _
    (prod_surjective _ _ (word_surjective _) (word_surjective _))
    (prod_surjective _ _
      (prod_surjective _ _ (word_surjective _) (word_surjective _))
      (prod_surjective _ _
        (prod_surjective _ _ (word_surjective _) (word_surjective _))
        (prod_surjective _ _
          (prod_surjective _ _ (word_surjective _) (word_surjective _))
          (prod_surjective _ _
            (prod_surjective _ _ bool_surjective bool_surjective)
            (prod_surjective _ _ bool_surjective bool_surjective)))))

private theorem focus_surjective (length : Nat) :
    Function.Surjective (Addition.TTK.overflowEncoding length).encode :=
  prod_surjective _ _
    (prod_surjective _ _ Function.surjective_id Function.surjective_id) bool_surjective

/-- Complete actual binary encoding, retaining all fields of the source frame. -/
@[implicit_reducible]
def groupedEncoding {width : Nat} (window : Window width) :
    BinaryLabelEncoding (Addition.TTK.OverflowRegisters window.length × Complement window) :=
  prod (Addition.TTK.overflowEncoding window.length) (complementEncoding window)

/-- The grouped carrier contains exactly the original number of physical source bits. -/
theorem groupedEncoding_width {width : Nat} (window : Window width) :
    (groupedEncoding window).width = (encoding width).width := by
  rw [encoding_width]
  change (window.length + window.length + 1) +
    ((window.above + window.below) + ((window.above + window.below) +
      ((width.size + width.size) + ((width.size + width.size) + ((1 + 1) + (1 + 1)))))) = _
  have complete := window.complete
  omega

private def groupedLabelEquiv {width : Nat} (window : Window width) :
    (Addition.TTK.OverflowRegisters window.length × Complement window) ≃
      (Qubits (groupedEncoding window).width).Index :=
  Equiv.ofBijective (groupedEncoding window).encode
    ⟨(groupedEncoding window).encode_injective,
      prod_surjective _ _ (focus_surjective window.length) (complement_surjective window)⟩

private def registerLabelEquiv (width : Nat) :
    Registers width ≃ (Qubits (encoding width).width).Index :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, encoding_surjective width⟩

/-- Decode the actual complete pieces and reassemble their original full source-register label. -/
def indexEquiv {width : Nat} (window : Window width) :
    (Qubits (groupedEncoding window).width).Index ≃ (Qubits (encoding width).width).Index :=
  (groupedLabelEquiv window).symm.trans
    ((grouping window).symm.trans (registerLabelEquiv width))

/-- Full actual field reassembly, rather than a basis map inferred from equal dimensions. -/
theorem indexEquiv_encode {width : Nat} (window : Window width) (state : Registers width) :
    indexEquiv window ((groupedEncoding window).encode (grouping window state)) =
      (encoding width).encode state := by
  change registerLabelEquiv width ((grouping window).symm
    ((groupedLabelEquiv window).symm (groupedLabelEquiv window (grouping window state)))) =
      registerLabelEquiv width state
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Encode the existing final four complement flags in their retained order. -/
private def complementFlag {width : Nat} (window : Window width)
    (bit : EncodedBit flagEncoding) : EncodedBit (complementEncoding window) :=
  prodRightBit _ _ (prodRightBit _ _ (prodRightBit _ _ (prodRightBit _ _ bit)))

/-- The control used by the native arithmetic is the original Ctrl in the complete complement. -/
def controlBit {width : Nat} (window : Window width) : EncodedBit (groupedEncoding window) :=
  prodRightBit _ _ (complementFlag window (prodRightBit _ _ (prodRightBit _ _ boolBit)))

/-- The one borrowed bit for dirty control is the original retained Iter, not a prepared zero. -/
def workBit {width : Nat} (window : Window width) : EncodedBit (groupedEncoding window) :=
  prodRightBit _ _ (complementFlag window (prodRightBit _ _ (prodLeftBit _ _ boolBit)))

theorem controlBit_get {width : Nat} (window : Window width) (state : Registers width) :
    (controlBit window).get (grouping window state) = state.control := rfl

theorem workBit_get {width : Nat} (window : Window width) (state : Registers width) :
    (workBit window).get (grouping window state) = state.flags.iteration := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticWindowEncoding

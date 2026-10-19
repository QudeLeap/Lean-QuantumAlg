/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.Modular.Additive

/-!
# Canonical modular encodings for the typed classical machine

The Core residue shape is deliberately nominal: it stores one raw word-width
encoding and carries no modulus proof.  This module is the semantic boundary
that relates such raw machine values to intrinsically canonical residues for a
fixed `ModulusSpec`.
-/

section

namespace QuantumAlg
namespace ClassicalRoutines

namespace Modular

open ClassicalAlgorithms.Modular

/-- Nominal machine shape used to store one canonical modular representative.

Canonicality is supplied by `Encoding.IsCanonical` or `Encoding.Represents`,
not by the raw Core shape itself. -/
abbrev ResidueShape (width : Nat) : CShape :=
  .canonicalResidue width

namespace Encoding

/-- A raw residue encoding is canonical for `spec` exactly when its represented
natural number is below the mathematical modulus. -/
def IsCanonical {width : Nat} (spec : ModulusSpec width)
    (value : CShape.Value (ResidueShape width)) : Prop :=
  value.residueEncoding.val < spec.modulus

/-- Relate one raw machine encoding to one intrinsic semantic residue. -/
def Represents {width : Nat} {spec : ModulusSpec width}
    (encoded : CShape.Value (ResidueShape width))
    (value : Residue spec) : Prop :=
  encoded.residueEncoding.val = value.val

/-- Encode an intrinsic residue in the nominal machine shape without changing
its canonical representative. -/
def encodeResidue {width : Nat} {spec : ModulusSpec width}
    (value : Residue spec) : CShape.Value (ResidueShape width) :=
  CShape.packCanonicalResidue width (encodeWord value.toWord)

/-- Decode a raw residue encoding only after receiving its modulus-specific
canonicality proof. -/
def decodeResidue {width : Nat} (spec : ModulusSpec width)
    (value : CShape.Value (ResidueShape width))
    (canonical : IsCanonical spec value) : Residue spec :=
  ⟨value.residueEncoding.val, canonical⟩

/-- A proof-carrying public encoding for one fixed modulus specification. -/
structure CanonicalEncoding {width : Nat} (spec : ModulusSpec width) where
  /-- The nominal value admitted by the typed machine. -/
  value : CShape.Value (ResidueShape width)
  /-- The semantic range proof absent from the nominal Core representation. -/
  canonical : IsCanonical spec value

@[simp] lemma modularEncode_residueEncoding {width : Nat}
    {spec : ModulusSpec width} (value : Residue spec) :
    (encodeResidue value).residueEncoding.val = value.val :=
  rfl

lemma modularEncode_isCanonical {width : Nat}
    {spec : ModulusSpec width} (value : Residue spec) :
    IsCanonical spec (encodeResidue value) := by
  change value.val < spec.modulus
  exact value.isLt

lemma modularEncode_represents {width : Nat}
    {spec : ModulusSpec width} (value : Residue spec) :
    Represents (encodeResidue value) value :=
  rfl

lemma modularRepresents_isCanonical {width : Nat}
    {spec : ModulusSpec width}
    {encoded : CShape.Value (ResidueShape width)} {value : Residue spec}
    (represents : Represents encoded value) :
    IsCanonical spec encoded := by
  change encoded.residueEncoding.val < spec.modulus
  rw [represents]
  exact value.isLt

@[simp] lemma modularDecode_residueEncoding {width : Nat}
    (spec : ModulusSpec width)
    (value : CShape.Value (ResidueShape width))
    (canonical : IsCanonical spec value) :
    (decodeResidue spec value canonical).val = value.residueEncoding.val :=
  rfl

@[simp] lemma modularDecode_encode {width : Nat}
    {spec : ModulusSpec width} (value : Residue spec) :
    decodeResidue spec (encodeResidue value)
        (modularEncode_isCanonical value) = value := by
  apply Fin.ext
  rfl

/-- Package an intrinsic residue as a proof-carrying machine encoding. -/
def CanonicalEncoding.ofResidue {width : Nat} {spec : ModulusSpec width}
    (value : Residue spec) : CanonicalEncoding spec where
  value := encodeResidue value
  canonical := modularEncode_isCanonical value

/-- Recover the intrinsic residue carried by a proved machine encoding. -/
def CanonicalEncoding.toResidue {width : Nat} {spec : ModulusSpec width}
    (encoding : CanonicalEncoding spec) : Residue spec :=
  decodeResidue spec encoding.value encoding.canonical

@[simp] lemma modularCanonicalEncoding_toResidue_ofResidue
    {width : Nat} {spec : ModulusSpec width} (value : Residue spec) :
    (CanonicalEncoding.ofResidue value).toResidue = value :=
  modularDecode_encode value

lemma modularCanonicalEncoding_represents {width : Nat}
    {spec : ModulusSpec width} (encoding : CanonicalEncoding spec) :
    Represents encoding.value encoding.toResidue :=
  rfl

end Encoding

end Modular

end ClassicalRoutines
end QuantumAlg

end

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Data.ZMod.Basic

/-!
# Binary residue-register encoding

This module records the quantum-free convention for using a binary register
label `Fin (2^n)` as storage for residues modulo `N`. The register label follows
the library-wide big-endian computational-basis convention; the arithmetic
content here is only the natural-number label and its reduction modulo `N`.

This is the register-level convention behind the reversible modular arithmetic
networks that store residues in computational-basis registers before composing
modular addition, multiplication, and exponentiation [VBE95,
9511018.tex:107-115, 276-286] [Bea02, arxivfact.tex:97-118].
-/

@[expose] public section

namespace QuantumAlg

/-- A binary register large enough to store every residue modulo `N`.

The label type is `Fin (2^n)`. Labels below `N` are valid canonical residue
representatives; labels at least `N` are padding labels and decode by reduction
modulo `N`. -/
structure BinaryResidueEncoding (N n : ℕ) where
  modulus_pos : 0 < N
  register_fits : N ≤ 2 ^ n

namespace BinaryResidueEncoding

/-- A register label is canonical when its natural value is below the modulus. -/
def IsValid {N n : ℕ} (E : BinaryResidueEncoding N n) (x : Fin (2 ^ n)) : Prop :=
  let _h := E.modulus_pos
  x.val < N

instance instDecidableIsValid {N n : ℕ} (E : BinaryResidueEncoding N n)
    (x : Fin (2 ^ n)) : Decidable (E.IsValid x) :=
  inferInstanceAs (Decidable (x.val < N))

/-- Decode a binary register label as a residue modulo `N`.

Padding labels are intentionally reduced modulo `N`; canonical round-tripping is
available through `encode_decode_of_valid`. -/
def decode {N n : ℕ} (E : BinaryResidueEncoding N n) (x : Fin (2 ^ n)) : ZMod N :=
  let _h := E.modulus_pos
  (x.val : ZMod N)

/-- Encode a residue modulo `N` as its canonical binary register label. -/
def encode {N n : ℕ} (E : BinaryResidueEncoding N n) (z : ZMod N) : Fin (2 ^ n) :=
  haveI : NeZero N := ⟨ne_of_gt E.modulus_pos⟩
  ⟨z.val, lt_of_lt_of_le (ZMod.val_lt z) E.register_fits⟩

@[simp]
theorem encode_val {N n : ℕ} (E : BinaryResidueEncoding N n) (z : ZMod N) :
    (E.encode z).val = z.val := rfl

@[simp]
theorem decode_val {N n : ℕ} (E : BinaryResidueEncoding N n) (x : Fin (2 ^ n)) :
    (E.decode x).val = x.val % N := by
  simp [decode, ZMod.val_natCast]

/-- Encoding always produces a canonical register label. -/
theorem encode_isValid {N n : ℕ} (E : BinaryResidueEncoding N n) (z : ZMod N) :
    E.IsValid (E.encode z) := by
  haveI : NeZero N := ⟨ne_of_gt E.modulus_pos⟩
  simpa [IsValid, encode] using ZMod.val_lt z

@[simp]
theorem decode_encode {N n : ℕ} (E : BinaryResidueEncoding N n) (z : ZMod N) :
    E.decode (E.encode z) = z := by
  haveI : NeZero N := ⟨ne_of_gt E.modulus_pos⟩
  simp [decode, encode]

/-- Valid canonical labels round-trip through `decode` and `encode`. -/
theorem encode_decode_of_valid {N n : ℕ} (E : BinaryResidueEncoding N n)
    (x : Fin (2 ^ n)) (hx : E.IsValid x) :
    E.encode (E.decode x) = x := by
  apply Fin.ext
  have hmod : x.val % N = x.val := Nat.mod_eq_of_lt hx
  rw [encode_val, decode_val, hmod]

end BinaryResidueEncoding

end QuantumAlg

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.WireAddress
public import QuantumAlg.Util.FinPow
import all QuantumAlg.Util.ResidueEncoding
public import Mathlib.Algebra.Order.Monoid.NatCast

/-!
# Binary computational-basis encodings

This Components-layer module defines faithful binary encodings shared by the
sealed qubit gate set and its encoded-bit lemma libraries.  Model-independent
wire-address operations live in Core.
-/

section

namespace QuantumAlg

noncomputable section

/-- Faithful encoding into binary computational-basis labels. -/
public structure BinaryLabelEncoding (Data : Type) where
  /-- Number of qubits occupied by an encoded value. -/
  width : Nat
  /-- Computational-basis label assigned to a semantic value. -/
  encode : Data → Fin (2 ^ width)
  /-- Distinct semantic values receive distinct basis labels. -/
  encode_injective : Function.Injective encode

namespace BinaryLabelEncoding

/-- One-qubit encoding of Booleans, with `false` at zero and `true` at one. -/
def bool : BinaryLabelEncoding Bool where
  width := 1
  encode := fun b => if b then 1 else 0
  encode_injective := by
    intro x y h
    cases x <;> cases y <;> simp at h <;> rfl

/-- Build an encoding from an equivalence with all basis labels of `n` qubits. -/
@[implicit_reducible]
def ofEquiv {Data : Type} {n : Nat} (layout : Data ≃ Fin (2 ^ n)) :
    BinaryLabelEncoding Data where
  width := n
  encode := layout
  encode_injective := layout.injective

/-- Transport an encoding along an equivalence of semantic value types. -/
def relabel {Data Other : Type} (encoding : BinaryLabelEncoding Data)
    (layout : Other ≃ Data) : BinaryLabelEncoding Other where
  width := encoding.width
  encode := fun x => encoding.encode (layout x)
  encode_injective := by
    intro x y h
    apply layout.injective
    exact encoding.encode_injective h

/-- Identity encoding of the complete `n`-qubit basis-label type. -/
@[implicit_reducible]
def finIdentity (n : Nat) : BinaryLabelEncoding (Fin (2 ^ n)) :=
  ofEquiv (Equiv.refl (Fin (2 ^ n)))

/-- Use a binary residue encoding as a faithful basis-label encoding of `ZMod N`. -/
def ofResidueEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding (ZMod N) where
  width := n
  encode := E.encode
  encode_injective := by
    intro x y h
    have hdecode := congrArg E.decode h
    simpa using hdecode

/-- Restrict a binary residue encoding to the unit group of `ZMod N`. -/
def ofUnitResidueEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding ((ZMod N)ˣ) where
  width := n
  encode := fun u => E.encode (u : ZMod N)
  encode_injective := by
    intro x y h
    apply Units.ext
    have hdecode := congrArg E.decode h
    simpa using hdecode

/-- Concatenate two encodings in big-endian tensor-product order. -/
@[implicit_reducible]
def prod {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) : BinaryLabelEncoding (Left × Right) where
  width := left.width + right.width
  encode := fun x => prodEquiv (left.encode x.1, right.encode x.2)
  encode_injective := by
    intro x y h
    have hpair : (left.encode x.1, right.encode x.2) =
        (left.encode y.1, right.encode y.2) := prodEquiv.injective h
    exact Prod.ext
      (left.encode_injective (congrArg Prod.fst hpair))
      (right.encode_injective (congrArg Prod.snd hpair))

/-- Encode any finite type into a width whose basis cardinality is large enough. -/
def ofFintypeCardLe (Data : Type) [Fintype Data] (width : Nat)
    (hcard : Fintype.card Data ≤ 2 ^ width) : BinaryLabelEncoding Data where
  width := width
  encode := fun x =>
    ⟨(Fintype.equivFin Data x).val,
      Nat.lt_of_lt_of_le (Fintype.equivFin Data x).isLt hcard⟩
  encode_injective := by
    intro x y h
    apply (Fintype.equivFin Data).injective
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa using hval

@[simp] theorem ofEquiv_width {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) : (ofEquiv layout).width = n := rfl

@[simp] theorem ofEquiv_encode {Data : Type} {n : Nat}
    (layout : Data ≃ Fin (2 ^ n)) (x : Data) : (ofEquiv layout).encode x = layout x := rfl

@[simp] theorem relabel_width {Data Other : Type}
    (encoding : BinaryLabelEncoding Data) (layout : Other ≃ Data) :
    (encoding.relabel layout).width = encoding.width := rfl

@[simp] theorem relabel_encode {Data Other : Type}
    (encoding : BinaryLabelEncoding Data) (layout : Other ≃ Data) (x : Other) :
    (encoding.relabel layout).encode x = encoding.encode (layout x) := rfl

@[simp] theorem finIdentity_width (n : Nat) : (finIdentity n).width = n := rfl

@[simp] theorem finIdentity_encode (n : Nat) (x : Fin (2 ^ n)) :
    (finIdentity n).encode x = x := rfl

@[simp] theorem bool_width : bool.width = 1 := rfl

@[simp] theorem bool_encode_false : bool.encode false = 0 := rfl

@[simp] theorem bool_encode_true : bool.encode true = 1 := rfl

@[simp] theorem ofResidueEncoding_width {N n : Nat} (E : BinaryResidueEncoding N n) :
    (ofResidueEncoding E).width = n := rfl

@[simp] theorem ofResidueEncoding_encode {N n : Nat} (E : BinaryResidueEncoding N n)
    (z : ZMod N) : (ofResidueEncoding E).encode z = E.encode z := rfl

@[simp] theorem prod_width {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) :
    (prod left right).width = left.width + right.width := rfl

@[simp] theorem prod_encode {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right) (x : Left × Right) :
    (prod left right).encode x = prodEquiv (left.encode x.1, right.encode x.2) := rfl

theorem encode_inj {Data : Type} (encoding : BinaryLabelEncoding Data)
    {x y : Data} (h : encoding.encode x = encoding.encode y) : x = y :=
  encoding.encode_injective h

end BinaryLabelEncoding

end

end QuantumAlg

end

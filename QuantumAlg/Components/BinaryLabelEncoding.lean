/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.ResidueEncoding
import Mathlib.Data.Nat.Bitwise

/-!
# Binary computational-basis encodings

This Components-layer module defines the basis-label operations and faithful
binary encodings shared by the sealed qubit gate set and its encoded-bit lemma
libraries.  It contains no circuit language and no resource metadata.
-/

section

namespace QuantumAlg

noncomputable section

namespace WireAddress

/-- Big-endian bit index for a physical wire; wire zero is most significant. -/
def bitIndex {n : Nat} (wire : Fin n) : Fin n :=
  ⟨n - 1 - wire.val, by omega⟩

theorem bitIndex_injective {n : Nat} : Function.Injective (bitIndex (n := n)) := by
  intro left right h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [bitIndex] at hv
  omega

/-- Convert a little-endian index to the library's big-endian wire address. -/
def littleEndianWire {n : Nat} (bit : Fin n) : Fin n :=
  bitIndex bit

@[simp]
theorem bitIndex_littleEndianWire {n : Nat} (bit : Fin n) :
    bitIndex (littleEndianWire bit) = bit := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

@[simp]
theorem littleEndianWire_bitIndex {n : Nat} (wire : Fin n) :
    littleEndianWire (bitIndex wire) = wire := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

/-- Flip one addressed wire of a computational-basis label. -/
def flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ (bitIndex target).val,
    Nat.xor_lt_two_pow x.isLt
      (Nat.pow_lt_pow_right one_lt_two (bitIndex target).isLt)⟩

theorem bit_flipBit {n : Nat} (target bit : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      (x.val.testBit (bitIndex bit).val ^^ decide (target = bit)) := by
  change (x.val ^^^ 2 ^ (bitIndex target).val).testBit (bitIndex bit).val =
    (x.val.testBit (bitIndex bit).val ^^ decide (target = bit))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact ⟨fun h => bitIndex_injective (Fin.val_injective h), fun h => by cases h; rfl⟩

theorem bit_flipBit_self {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex target).val =
      !x.val.testBit (bitIndex target).val := by
  simp [bit_flipBit]

theorem bit_flipBit_of_ne {n : Nat} {target bit : Fin n} (hne : target ≠ bit)
    (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      x.val.testBit (bitIndex bit).val := by
  simp [bit_flipBit, hne]

theorem flipBit_flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    flipBit target (flipBit target x) = x := by
  unfold flipBit
  ext
  simp

theorem flipBit_comm {n : Nat} (left right : Fin n) (x : Fin (2 ^ n)) :
    flipBit left (flipBit right x) = flipBit right (flipBit left x) := by
  unfold flipBit
  ext
  change (x.val ^^^ 2 ^ (bitIndex right).val) ^^^ 2 ^ (bitIndex left).val =
    (x.val ^^^ 2 ^ (bitIndex left).val) ^^^ 2 ^ (bitIndex right).val
  rw [Nat.xor_assoc, Nat.xor_assoc,
    Nat.xor_comm (2 ^ (bitIndex right).val) (2 ^ (bitIndex left).val)]

/-- Addressed X action. -/
def xMap {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  flipBit target x

/-- Addressed X basis-label permutation. -/
def xPerm {n : Nat} (target : Fin n) : Equiv.Perm (Fin (2 ^ n)) where
  toFun := xMap target
  invFun := xMap target
  left_inv := flipBit_flipBit target
  right_inv := flipBit_flipBit target

/-- Addressed CNOT action. -/
def cnotMap {n : Nat} (control target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if x.val.testBit (bitIndex control).val then flipBit target x else x

theorem cnotMap_cnotMap {n : Nat} {control target : Fin n} (hct : control ≠ target)
    (x : Fin (2 ^ n)) : cnotMap control target (cnotMap control target x) = x := by
  unfold cnotMap
  by_cases hc : x.val.testBit (bitIndex control).val
  · simp [hc, bit_flipBit_of_ne (target := target) (bit := control) (Ne.symm hct),
      flipBit_flipBit]
  · simp [hc]

/-- Addressed CNOT basis-label permutation. -/
def cnotPerm {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := cnotMap control target
  invFun := cnotMap control target
  left_inv := cnotMap_cnotMap hct
  right_inv := cnotMap_cnotMap hct

/-- Addressed Toffoli action. -/
def toffoliMap {n : Nat} (controlA controlB target : Fin n) (x : Fin (2 ^ n)) :
    Fin (2 ^ n) :=
  if x.val.testBit (bitIndex controlA).val && x.val.testBit (bitIndex controlB).val then
    flipBit target x
  else x

theorem toffoliMap_toffoliMap {n : Nat} {controlA controlB target : Fin n}
    (ha : controlA ≠ target) (hb : controlB ≠ target) (x : Fin (2 ^ n)) :
    toffoliMap controlA controlB target (toffoliMap controlA controlB target x) = x := by
  unfold toffoliMap
  by_cases hgate :
      x.val.testBit (bitIndex controlA).val && x.val.testBit (bitIndex controlB).val
  · have haBit :
        (flipBit target x).val.testBit (bitIndex controlA).val =
          x.val.testBit (bitIndex controlA).val :=
      bit_flipBit_of_ne (target := target) (bit := controlA) (Ne.symm ha) x
    have hbBit :
        (flipBit target x).val.testBit (bitIndex controlB).val =
          x.val.testBit (bitIndex controlB).val :=
      bit_flipBit_of_ne (target := target) (bit := controlB) (Ne.symm hb) x
    simp [hgate, haBit, hbBit, flipBit_flipBit]
  · simp [hgate]

/-- Addressed Toffoli basis-label permutation; pairwise-distinctness witnesses
certify the three wire roles while the permutation uses the two control-target
inequalities. -/
@[nolint unusedArguments]
def toffoliPerm {n : Nat} (controlA controlB target : Fin n)
    (_hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := toffoliMap controlA controlB target
  invFun := toffoliMap controlA controlB target
  left_inv := toffoliMap_toffoliMap ha hb
  right_inv := toffoliMap_toffoliMap ha hb

end WireAddress

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

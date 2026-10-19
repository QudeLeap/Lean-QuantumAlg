/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Bitwise
public import Mathlib.Logic.Equiv.Defs

/-!
# Binary wire addresses

Model-independent operations on big-endian computational-basis labels.  This
Core module is shared by physical circuit placement and higher-level binary
encodings.
-/

section

namespace QuantumAlg.WireAddress

/-- Big-endian bit index for a physical wire; wire zero is most significant. -/
@[expose] public def bitIndex {n : Nat} (wire : Fin n) : Fin n :=
  ⟨n - 1 - wire.val, by omega⟩

public lemma bitIndex_val {n : Nat} (wire : Fin n) :
    (bitIndex wire).val = n - 1 - wire.val := rfl

public lemma bitIndex_injective {n : Nat} : Function.Injective (bitIndex (n := n)) := by
  intro left right h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [bitIndex] at hv
  omega

/-- Convert a little-endian index to the library's big-endian wire address. -/
@[expose] public def littleEndianWire {n : Nat} (bit : Fin n) : Fin n :=
  bitIndex bit

@[simp]
public lemma bitIndex_littleEndianWire {n : Nat} (bit : Fin n) :
    bitIndex (littleEndianWire bit) = bit := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

@[simp]
public lemma littleEndianWire_bitIndex {n : Nat} (wire : Fin n) :
    littleEndianWire (bitIndex wire) = wire := by
  apply Fin.ext
  dsimp [bitIndex, littleEndianWire]
  omega

/-- Flip one addressed wire of a computational-basis label. -/
@[expose] public def flipBit {n : Nat} (target : Fin n)
    (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨x.val ^^^ 2 ^ (bitIndex target).val,
    Nat.xor_lt_two_pow x.isLt
      (Nat.pow_lt_pow_right Nat.one_lt_two (bitIndex target).isLt)⟩

public lemma bit_flipBit {n : Nat} (target bit : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      (x.val.testBit (bitIndex bit).val ^^ decide (target = bit)) := by
  change (x.val ^^^ 2 ^ (bitIndex target).val).testBit (bitIndex bit).val =
    (x.val.testBit (bitIndex bit).val ^^ decide (target = bit))
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  congr 1
  rw [decide_eq_decide]
  exact ⟨fun h => bitIndex_injective (Fin.ext h), fun h => by cases h; rfl⟩

public lemma bit_flipBit_self {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex target).val =
      !x.val.testBit (bitIndex target).val := by
  simp [bit_flipBit]

public lemma bit_flipBit_of_ne {n : Nat} {target bit : Fin n} (hne : target ≠ bit)
    (x : Fin (2 ^ n)) :
    (flipBit target x).val.testBit (bitIndex bit).val =
      x.val.testBit (bitIndex bit).val := by
  simp [bit_flipBit, hne]

public lemma flipBit_flipBit {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    flipBit target (flipBit target x) = x := by
  unfold flipBit
  ext
  simp

public lemma flipBit_comm {n : Nat} (left right : Fin n) (x : Fin (2 ^ n)) :
    flipBit left (flipBit right x) = flipBit right (flipBit left x) := by
  unfold flipBit
  ext
  change (x.val ^^^ 2 ^ (bitIndex right).val) ^^^ 2 ^ (bitIndex left).val =
    (x.val ^^^ 2 ^ (bitIndex left).val) ^^^ 2 ^ (bitIndex right).val
  rw [Nat.xor_assoc, Nat.xor_assoc,
    Nat.xor_comm (2 ^ (bitIndex right).val) (2 ^ (bitIndex left).val)]

/-- Addressed X action. -/
@[expose] public def xMap {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  flipBit target x

/-- Addressed X basis-label permutation. -/
@[expose] public def xPerm {n : Nat} (target : Fin n) : Equiv.Perm (Fin (2 ^ n)) where
  toFun := xMap target
  invFun := xMap target
  left_inv := flipBit_flipBit target
  right_inv := flipBit_flipBit target

@[simp] public lemma xPerm_apply {n : Nat} (target : Fin n) (x : Fin (2 ^ n)) :
    xPerm target x = flipBit target x := rfl

/-- Addressed CNOT action. -/
@[expose] public def cnotMap {n : Nat} (control target : Fin n) (x : Fin (2 ^ n)) : Fin (2 ^ n) :=
  if x.val.testBit (bitIndex control).val then flipBit target x else x

public lemma cnotMap_cnotMap {n : Nat} {control target : Fin n} (hct : control ≠ target)
    (x : Fin (2 ^ n)) : cnotMap control target (cnotMap control target x) = x := by
  unfold cnotMap
  by_cases hc : x.val.testBit (bitIndex control).val
  · simp [hc, bit_flipBit_of_ne (target := target) (bit := control) (Ne.symm hct),
      flipBit_flipBit]
  · simp [hc]

/-- Addressed CNOT basis-label permutation. -/
@[expose] public def cnotPerm {n : Nat} (control target : Fin n) (hct : control ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := cnotMap control target
  invFun := cnotMap control target
  left_inv := cnotMap_cnotMap hct
  right_inv := cnotMap_cnotMap hct

@[simp] public lemma cnotPerm_apply {n : Nat} (control target : Fin n)
    (hct : control ≠ target) (x : Fin (2 ^ n)) :
    cnotPerm control target hct x = cnotMap control target x := rfl

/-- Addressed Toffoli action. -/
@[expose] public def toffoliMap {n : Nat} (controlA controlB target : Fin n) (x : Fin (2 ^ n)) :
    Fin (2 ^ n) :=
  if x.val.testBit (bitIndex controlA).val && x.val.testBit (bitIndex controlB).val then
    flipBit target x
  else x

public lemma toffoliMap_toffoliMap {n : Nat} {controlA controlB target : Fin n}
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
@[expose] public def toffoliPerm {n : Nat} (controlA controlB target : Fin n)
    (_hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun := toffoliMap controlA controlB target
  invFun := toffoliMap controlA controlB target
  left_inv := toffoliMap_toffoliMap ha hb
  right_inv := toffoliMap_toffoliMap ha hb

@[simp] public lemma toffoliPerm_apply {n : Nat} (controlA controlB target : Fin n)
    (hab : controlA ≠ controlB) (ha : controlA ≠ target) (hb : controlB ≠ target)
    (x : Fin (2 ^ n)) :
    toffoliPerm controlA controlB target hab ha hb x =
      toffoliMap controlA controlB target x := rfl

end QuantumAlg.WireAddress

end

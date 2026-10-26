/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower
import Mathlib.Tactic.NormNum

/-!
# Exact capacity and sparse complement for P-256 field arithmetic

The modulus is derived from its binary capacity and sparse complement.
Arithmetic operands range over every canonical residue, including zero.
No primality or unit-input certificate is needed by addition and doubling.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256

/-- Width of each physical field word. -/
def width : Nat := 256

/-- Capacity of one complete field word. -/
def capacity : Nat := 2 ^ width

/-- The sparse difference between the binary capacity and the field modulus. -/
def complement : Nat := 2 ^ 224 - 2 ^ 192 - 2 ^ 96 + 1

/-- Exact P-256 field modulus, derived from the sparse complement. -/
def modulus : Nat := capacity - complement

lemma complement_positive : 0 < complement := by
  norm_num [complement]

lemma complement_lt_capacity : complement < capacity := by
  norm_num [complement, capacity, width]

lemma complement_lt_modulus : complement < modulus := by
  norm_num [complement, modulus, capacity, width]

lemma modulus_positive : 0 < modulus := by
  norm_num [modulus, complement, capacity, width]

lemma modulus_lt_capacity : modulus < capacity := by
  have positive := complement_positive
  have bounded := complement_lt_capacity
  unfold modulus
  omega

lemma modulus_add_complement : modulus + complement = capacity := by
  unfold modulus
  exact Nat.sub_add_cancel complement_lt_capacity.le

/-- The derived low-level modulus agrees with the standard four-power formula. -/
lemma modulus_eq_standard :
    modulus = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1 := by
  norm_num [modulus, complement, capacity, width]

lemma modulus_odd : modulus % 2 = 1 := by
  norm_num [modulus, complement, capacity, width]

lemma complement_odd : complement % 2 = 1 := by
  norm_num [complement]

/-- The even correction leaves the new low control bit untouched. -/
lemma even_correction_eq :
    complement - 1 = 2 ^ 224 - 2 ^ 192 - 2 ^ 96 := by
  unfold complement
  omega

/-- One physical unsigned field word, without an extra residue invariant. -/
abbrev Word := Fin capacity

/-- The original canonical-residue predicate on a physical word. -/
def Canonical (value : Word) : Prop := value.val < modulus

/-- Encode a mathematical canonical residue in the unchanged physical word. -/
def residueWord (value : Fin modulus) : Word :=
  ⟨value.val, value.isLt.trans modulus_lt_capacity⟩

lemma residueWord_canonical (value : Fin modulus) : Canonical (residueWord value) :=
  value.isLt

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256

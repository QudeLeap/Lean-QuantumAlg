/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Index plumbing for `Fin (2 ^ n)` registers (quantum-free)

The big-endian pairing of computational-basis labels used to compose qubit
registers, factored out of the quantum framework so it carries no dependency
on `Gate`/`PureState`.

## Main definition

- `QuantumAlg.prodEquiv` — `Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n))`,
  `(x, y) ↦ y + 2 ^ n * x`, so the first (lower-qubit-index) factor carries
  the most significant bits.

Pinned Mathlib API: `finProdFinEquiv` (`(x, y) ↦ y + n * x`), `finCongr`.
-/

@[expose] public section

namespace QuantumAlg

variable {m n : ℕ}

/-- Big-endian pairing of basis labels: `(x, y) ↦ y + 2 ^ n * x`, so the
first (lower-qubit-index) factor carries the most significant bits. -/
def prodEquiv : Fin (2 ^ m) × Fin (2 ^ n) ≃ Fin (2 ^ (m + n)) :=
  finProdFinEquiv.trans (finCongr (pow_add (2 : ℕ) m n).symm)

/-! ## Bit reconstruction helpers -/

/-- Reconstructing a natural number from `n + 1` little-endian bits can be
split into the lower `n` bits plus the final most-significant bit. -/
theorem nat_ofBits_succ_last {n : ℕ} (f : Fin (n + 1) → Bool) :
    Nat.ofBits f =
      Nat.ofBits (f ∘ Fin.castSucc) +
        2 ^ n * (f (Fin.last n)).toNat := by
  induction n with
  | zero =>
      rw [Nat.ofBits_succ]
      simp
  | succ n ih =>
      rw [Nat.ofBits_succ]
      rw [ih (f ∘ Fin.succ)]
      rw [Nat.ofBits_succ]
      have hcomp :
          (f ∘ Fin.succ) ∘ Fin.castSucc =
            (f ∘ Fin.castSucc) ∘ Fin.succ := by
        funext i
        rfl
      rw [hcomp]
      simp [Fin.succ_last, Nat.pow_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]

/-- Reconstructing bits after appending a high slice equals the low-slice value
plus the high-slice value shifted by the low-slice width. -/
theorem nat_ofBits_append {m n : ℕ} (lo : Fin m → Bool) (hi : Fin n → Bool) :
    Nat.ofBits (Fin.append lo hi) =
      Nat.ofBits lo + 2 ^ m * Nat.ofBits hi := by
  induction n with
  | zero =>
      have hfun :
          Fin.append lo hi =
            lo ∘ Fin.cast (Nat.add_zero m) := by
        funext i
        refine Fin.addCases (fun l => ?_) (fun r => ?_) i
        · rw [Fin.append_left]
          simp
        · exact r.elim0
      rw [hfun]
      apply congrArg Nat.ofBits
      funext i
      rfl
  | succ n ih =>
      let f : Fin (m + n + 1) → Bool :=
        (Fin.append lo hi) ∘ Fin.cast (Nat.add_succ m n).symm
      have hcast :
          Nat.ofBits (Fin.append lo hi) = Nat.ofBits f := by
        simp [f]
      rw [hcast]
      rw [nat_ofBits_succ_last f]
      have hlow :
          f ∘ Fin.castSucc = Fin.append lo (hi ∘ Fin.castSucc) := by
        funext i
        refine Fin.addCases (fun l => ?_) (fun r => ?_) i
        · have hidx :
              Fin.cast (Nat.add_succ m n).symm
                  (Fin.castSucc (Fin.castAdd n l)) =
                Fin.castAdd (n + 1) l := by
            ext
            simp
          dsimp [f]
          rw [Fin.append_left]
          change Fin.append lo hi
              (Fin.cast (Nat.add_succ m n).symm
                (Fin.castSucc (Fin.castAdd n l))) =
            lo l
          rw [hidx, Fin.append_left]
        · have hidx :
              Fin.cast (Nat.add_succ m n).symm
                  (Fin.castSucc (Fin.natAdd m r)) =
                Fin.natAdd m (Fin.castSucc r) := by
            ext
            simp
          dsimp [f]
          rw [Fin.append_right]
          rw [Fin.append_right]
          rfl
      have hlast : f (Fin.last (m + n)) = hi (Fin.last n) := by
        have hlast_index :
            Fin.cast (Nat.add_succ m n).symm (Fin.last (m + n)) =
              Fin.natAdd m (Fin.last n) := by
          ext
          simp [Fin.last]
        change Fin.append lo hi
            (Fin.cast (Nat.add_succ m n).symm (Fin.last (m + n))) =
          hi (Fin.last n)
        rw [hlast_index]
        rw [Fin.append_right]
      rw [hlow, ih (hi ∘ Fin.castSucc), hlast]
      rw [nat_ofBits_succ_last hi]
      rw [Nat.mul_add, Nat.pow_add]
      ac_rfl

/-- The big-endian product equivalence is the little-endian bit append of the
right/low slice followed by the left/high slice. -/
theorem prodEquiv_val_eq_ofBits_append {m n : ℕ}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) :
    (prodEquiv (m := m) (n := n) (left, right)).val =
      Nat.ofBits
        (Fin.append
          (fun i : Fin n => right.val.testBit i.val)
          (fun i : Fin m => left.val.testBit i.val)) := by
  rw [nat_ofBits_append]
  rw [Nat.ofBits_testBit, Nat.ofBits_testBit]
  rw [Nat.mod_eq_of_lt right.isLt, Nat.mod_eq_of_lt left.isLt]
  rfl

/-- The low little-endian bits of `prodEquiv (left, right)` come from the
right product component. -/
theorem prodEquiv_testBit_right {m n : ℕ}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) (bit : Fin n) :
    (prodEquiv (m := m) (n := n) (left, right)).val.testBit bit.val =
      right.val.testBit bit.val := by
  rw [prodEquiv_val_eq_ofBits_append]
  rw [Nat.testBit_ofBits_lt]
  · have hidx :
        (⟨bit.val, by omega⟩ : Fin (n + m)) = Fin.castAdd m bit := by
      rfl
    rw [hidx, Fin.append_left]
  · omega

/-- The high little-endian bits of `prodEquiv (left, right)` come from the
left product component. -/
theorem prodEquiv_testBit_left {m n : ℕ}
    (left : Fin (2 ^ m)) (right : Fin (2 ^ n)) (bit : Fin m) :
    (prodEquiv (m := m) (n := n) (left, right)).val.testBit (n + bit.val) =
      left.val.testBit bit.val := by
  rw [prodEquiv_val_eq_ofBits_append]
  rw [Nat.testBit_ofBits_lt]
  · have hidx :
        (⟨n + bit.val, by omega⟩ : Fin (n + m)) = Fin.natAdd n bit := by
      rfl
    rw [hidx, Fin.append_right]
  · omega

end QuantumAlg

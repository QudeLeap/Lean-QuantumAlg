/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Classical.TerminalDecode
import Mathlib.Tactic

/-!
# Terminal phase fibers of the native source measurement

The native readout observes precisely the high-order phase register. Each
phase outcome fiber retains all target-register basis labels.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

/-- Big-endian phase outcome corresponding to one source phase label. -/
def phaseOutcome (t : Nat) (value : Fin (2 ^ t)) : TerminalZMeasure.Outcome t :=
  fun outputIndex => value.val.testBit (t - 1 - outputIndex.val)

/-- Big-endian decoding recovers the original phase label. -/
lemma fullRegisterIndex_phaseOutcome (t : Nat) (value : Fin (2 ^ t)) :
    ClassicalAlgorithms.TerminalDecode.fullRegisterIndex
      (phaseOutcome t value) = value := by
  apply Fin.val_injective
  rw [ClassicalAlgorithms.TerminalDecode.fullRegisterIndex_val]
  have hbits :
      (phaseOutcome t value) ∘ Fin.rev =
        fun bit : Fin t => value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, phaseOutcome]
    apply congrArg value.val.testBit
    calc
      t - 1 - (Fin.rev bit).val = t - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

/-! ## Terminal-measurement fibers -/

lemma phaseOutcome_injective (t : Nat) :
    Function.Injective (phaseOutcome t) := by
  intro left right h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < t
  · let outputIndex : Fin t := ⟨t - 1 - bit, by omega⟩
    have hreverse : t - 1 - outputIndex.val = bit := by
      dsimp [outputIndex]
      omega
    have hout := congrFun h outputIndex
    simpa [phaseOutcome, hreverse] using hout
  · have htbit : t ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ t ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) htbit
    rw [Nat.testBit_eq_false_of_lt (left.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (right.isLt.trans_le hpow)]

lemma phaseOutcome_bijective (t : Nat) :
    Function.Bijective (phaseOutcome t) := by
  apply (Fintype.bijective_iff_injective_and_card (phaseOutcome t)).2
  refine ⟨phaseOutcome_injective t, ?_⟩
  simp

@[simp] lemma sourceMeasurement_readout_prod {t m : Nat}
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (measurement t m).readout (prodEquiv (c, y)) =
      phaseOutcome t c := by
  funext outputIndex
  change (prodEquiv (c, y)).val.testBit
      (t + m - 1 - outputIndex.val) =
    c.val.testBit (t - 1 - outputIndex.val)
  have hindex :
      t + m - 1 - outputIndex.val =
        m + (t - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left c y
    ⟨t - 1 - outputIndex.val, by omega⟩

lemma sourceMeasurement_readout_eq_outcome_iff {t m : Nat}
    (basis : Fin (2 ^ (t + m))) (c : Fin (2 ^ t)) :
    (measurement t m).readout basis = phaseOutcome t c ↔
      (prodEquiv.symm basis).1 = c := by
  have hself :
      (measurement t m).readout basis =
        phaseOutcome t (prodEquiv.symm basis).1 := by
    simpa using sourceMeasurement_readout_prod
      (m := m) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact phaseOutcome_injective t (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (phaseOutcome t) h)

/-- Embed the unmeasured target-register basis into one phase-readout fiber. -/
def sourceFiberEmbedding {t m : Nat} (c : Fin (2 ^ t)) :
    Fin (2 ^ m) ↪ Fin (2 ^ (t + m)) where
  toFun := fun y => prodEquiv (c, y)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] lemma sourceFiberEmbedding_apply {t m : Nat}
    (c : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    sourceFiberEmbedding c y = prodEquiv (c, y) := rfl

lemma sourceMeasurement_fiber {t m : Nat} (c : Fin (2 ^ t)) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (t + m)) =>
          (measurement t m).readout basis = phaseOutcome t c) =
      Finset.univ.map (sourceFiberEmbedding c) := by
  ext basis
  rw [Finset.mem_filter, sourceMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [sourceFiberEmbedding_apply, ← hleft]
    exact (Equiv.apply_symm_apply (prodEquiv (m := t) (n := m)) basis)
  · intro hmem
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hmem
    change prodEquiv (c, y) = basis at hy
    rw [← hy, Equiv.symm_apply_apply]


end

end QuantumAlg.OrderFinding.Native

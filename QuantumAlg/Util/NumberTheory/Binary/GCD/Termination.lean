/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init

import all QuantumAlg.Util.NumberTheory.Binary.GCD.FixedRound
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size

/-!
# Fixed-round binary-GCD termination

This quantum-free module proves the decreasing-potential argument behind the
fixed `2n` Montgomery--Kaliski schedule.  It deliberately speaks only about
the integer source state; circuit realization and resource accounting remain
in `QuantumAlg.Primitives`.
-/

section

namespace QuantumAlg
namespace NumberTheory.BinaryGCD
namespace RoundState

/-! ## Binary-size potential -/

/-- Halving a positive natural strictly lowers its binary size. -/
theorem size_div_two_lt (value : Nat) (hvalue : 0 < value) :
    Nat.size (value / 2) < Nat.size value := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp at hvalue
  | bit bit tail hbit _ih =>
      have hne : Nat.bit bit tail ≠ 0 := Nat.bit_ne_zero_iff.mpr hbit
      rw [Nat.bit_div_two, Nat.size_bit hne]
      omega

/-- The binary-size potential of an active binary-GCD pair. -/
def roundPotential (st : RoundState) : Nat :=
  Nat.size st.u + Nat.size st.v

/-- The `uEven` update strictly lowers the binary-size potential. -/
theorem applyBranch_uEven_roundPotential_lt (st : RoundState)
    (hu : 0 < st.u) :
    roundPotential (applyBranch Branch.uEven st) < roundPotential st := by
  have hsize : Nat.size (st.u / 2) < Nat.size st.u := size_div_two_lt st.u hu
  simp only [roundPotential, applyBranch]
  omega

/-- The `vEven` update strictly lowers the binary-size potential. -/
theorem applyBranch_vEven_roundPotential_lt (st : RoundState)
    (hv : 0 < st.v) :
    roundPotential (applyBranch Branch.vEven st) < roundPotential st := by
  have hsize : Nat.size (st.v / 2) < Nat.size st.v := size_div_two_lt st.v hv
  simp only [roundPotential, applyBranch]
  omega

/-- The `uGreater` update strictly lowers the binary-size potential. -/
theorem applyBranch_uGreater_roundPotential_lt (st : RoundState)
    (hlt : st.v < st.u) :
    roundPotential (applyBranch Branch.uGreater st) < roundPotential st := by
  have hdiffPos : 0 < st.u - st.v := Nat.sub_pos_of_lt hlt
  have hhalf : Nat.size ((st.u - st.v) / 2) < Nat.size (st.u - st.v) :=
    size_div_two_lt (st.u - st.v) hdiffPos
  have hsub : Nat.size (st.u - st.v) ≤ Nat.size st.u :=
    Nat.size_le_size (Nat.sub_le _ _)
  have hsize : Nat.size ((st.u - st.v) / 2) < Nat.size st.u :=
    lt_of_lt_of_le hhalf hsub
  simp only [roundPotential, applyBranch]
  omega

/-- The `vLe` update strictly lowers the binary-size potential. -/
theorem applyBranch_vLe_roundPotential_lt (st : RoundState)
    (hv : 0 < st.v) :
    roundPotential (applyBranch Branch.vLe st) < roundPotential st := by
  have hdiv : (st.v - st.u) / 2 ≤ st.v / 2 :=
    Nat.div_le_div_right (c := 2) (Nat.sub_le _ _)
  have hdivSize : Nat.size ((st.v - st.u) / 2) ≤ Nat.size (st.v / 2) :=
    Nat.size_le_size hdiv
  have hhalf : Nat.size (st.v / 2) < Nat.size st.v := size_div_two_lt st.v hv
  have hsize : Nat.size ((st.v - st.u) / 2) < Nat.size st.v :=
    lt_of_le_of_lt hdivSize hhalf
  simp only [roundPotential, applyBranch]
  omega

/-- A nonterminal active round strictly lowers the binary-size potential. -/
theorem roundPotential_lt_of_active_nonzero (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0) (hu : 0 < st.u) :
    roundPotential (round st) < roundPotential st := by
  by_cases huEven : st.u % 2 = 0
  · rw [round_active_nonzero_uEven st hactive hv0 huEven]
    exact applyBranch_uEven_roundPotential_lt st hu
  by_cases hvEven : st.v % 2 = 0
  · rw [round_active_nonzero_vEven st hactive hv0 huEven hvEven]
    exact applyBranch_vEven_roundPotential_lt st (Nat.pos_of_ne_zero hv0)
  by_cases hlt : st.v < st.u
  · rw [round_active_nonzero_uGreater st hactive hv0 huEven hvEven hlt]
    exact applyBranch_uGreater_roundPotential_lt st hlt
  · rw [round_active_nonzero_vLe st hactive hv0 huEven hvEven hlt]
    exact applyBranch_vLe_roundPotential_lt st (Nat.pos_of_ne_zero hv0)

/-! ## Positivity and terminal-state persistence -/

/-- Every source round preserves positivity of the `u` word. -/
theorem round_u_pos_of_pos (st : RoundState) (huPos : 0 < st.u) :
    0 < (round st).u := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa using huPos
  · by_cases hv0 : st.v = 0
    · rw [round_active_terminated st hactive hv0]
      simpa using huPos
    · by_cases huEven : st.u % 2 = 0
      · rw [round_active_nonzero_uEven st hactive hv0 huEven]
        change 0 < st.u / 2
        have hhalf : 2 * (st.u / 2) = st.u :=
          Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.u huEven
        omega
      · by_cases hvEven : st.v % 2 = 0
        · rw [round_active_nonzero_vEven st hactive hv0 huEven hvEven]
          simpa [applyBranch] using huPos
        · by_cases hlt : st.v < st.u
          · have hsub : st.v ≤ st.u := Nat.le_of_lt hlt
            have hhalf : 2 * ((st.u - st.v) / 2) = st.u - st.v :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.u - st.v)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero
                  hsub huEven hvEven)
            rw [round_active_nonzero_uGreater st hactive hv0 huEven hvEven hlt]
            change 0 < (st.u - st.v) / 2
            have hdiffPos : 0 < st.u - st.v := Nat.sub_pos_of_lt hlt
            omega
          · rw [round_active_nonzero_vLe st hactive hv0 huEven hvEven hlt]
            simpa [applyBranch] using huPos

/-- Positivity of the `u` word persists through any fixed number of rounds. -/
theorem runRounds_u_pos_of_pos (rounds : Nat) (st : RoundState)
    (huPos : 0 < st.u) :
    0 < (runRounds rounds st).u := by
  induction rounds generalizing st with
  | zero =>
      simpa [runRounds] using huPos
  | succ rounds ih =>
      rw [runRounds_succ_eq_round_runRounds]
      exact round_u_pos_of_pos (runRounds rounds st) (ih st huPos)

/-- Once the source `v` word is zero, one further round leaves it zero. -/
theorem round_v_eq_zero_of_v_eq_zero (st : RoundState) (hv : st.v = 0) :
    (round st).v = 0 := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa using hv
  · rw [round_active_terminated st hactive hv]
    simpa using hv

/-- Once the source `v` word is zero, every remaining fixed round preserves it. -/
theorem runRounds_v_eq_zero_of_v_eq_zero (rounds : Nat) (st : RoundState)
    (hv : st.v = 0) :
    (runRounds rounds st).v = 0 := by
  induction rounds generalizing st with
  | zero =>
      simpa [runRounds] using hv
  | succ rounds ih =>
      rw [runRounds_succ_eq_round_runRounds]
      exact round_v_eq_zero_of_v_eq_zero (runRounds rounds st) (ih st hv)

/-- Splitting the fixed-round iterator at a prefix produces the corresponding
suffix iterator on the prefix state. -/
theorem runRounds_add (initialRounds suffix : Nat) (st : RoundState) :
    runRounds (initialRounds + suffix) st =
      runRounds suffix (runRounds initialRounds st) := by
  induction suffix generalizing st with
  | zero =>
      simp [runRounds]
  | succ suffix ih =>
      calc
        runRounds (initialRounds + (suffix + 1)) st =
            round (runRounds (initialRounds + suffix) st) := by
              rw [Nat.add_succ, runRounds_succ_eq_round_runRounds]
        _ = round (runRounds suffix (runRounds initialRounds st)) := by
              rw [ih st]
        _ = runRounds (suffix + 1) (runRounds initialRounds st) := by
              exact
                (runRounds_succ_eq_round_runRounds suffix
                  (runRounds initialRounds st)).symm

/-! ## Bounded termination -/

/-- If every earlier prefix still has nonzero `v`, then the active flag remains
set at the indicated prefix. -/
theorem runRounds_active_of_all_prefix_v_ne_zero (rounds : Nat) (st : RoundState)
    (hactive : st.active = true)
    (hzero : ∀ index < rounds, (runRounds index st).v ≠ 0) :
    (runRounds rounds st).active = true := by
  induction rounds with
  | zero =>
      simpa [runRounds] using hactive
  | succ rounds ih =>
      rw [runRounds_succ_eq_round_runRounds]
      apply round_active_nonzero_active
      · apply ih
        intro index hindex
        exact hzero index (Nat.lt_trans hindex (Nat.lt_succ_self rounds))
      · exact hzero rounds (Nat.lt_succ_self rounds)

/-- Before termination, each elapsed round can be charged against one unit of
the initial binary-size potential. -/
theorem roundPotential_add_rounds_le_of_all_prefix_v_ne_zero
    (rounds : Nat) (st : RoundState) (huPos : 0 < st.u)
    (hactive : st.active = true)
    (hzero : ∀ index < rounds, (runRounds index st).v ≠ 0) :
    roundPotential (runRounds rounds st) + rounds ≤ roundPotential st := by
  induction rounds with
  | zero =>
      simp [runRounds]
  | succ rounds ih =>
      have hprefixZero : ∀ index < rounds, (runRounds index st).v ≠ 0 := by
        intro index hindex
        exact hzero index (Nat.lt_trans hindex (Nat.lt_succ_self rounds))
      have hbound :
          roundPotential (runRounds rounds st) + rounds ≤ roundPotential st :=
        ih hprefixZero
      have huPrefix : 0 < (runRounds rounds st).u :=
        runRounds_u_pos_of_pos rounds st huPos
      have hactivePrefix : (runRounds rounds st).active = true :=
        runRounds_active_of_all_prefix_v_ne_zero rounds st hactive hprefixZero
      have hvPrefix : (runRounds rounds st).v ≠ 0 :=
        hzero rounds (Nat.lt_succ_self rounds)
      have hstep :
          roundPotential (round (runRounds rounds st)) <
            roundPotential (runRounds rounds st) :=
        roundPotential_lt_of_active_nonzero
          (runRounds rounds st) hactivePrefix hvPrefix huPrefix
      rw [runRounds_succ_eq_round_runRounds]
      omega

/-- An active binary-GCD state with positive `u` reaches `v = 0` within its
binary-size potential. -/
theorem exists_runRounds_v_eq_zero_of_active (st : RoundState)
    (huPos : 0 < st.u) (hactive : st.active = true) :
    ∃ rounds ≤ roundPotential st, (runRounds rounds st).v = 0 := by
  by_contra htermination
  have hnonzero : ∀ rounds ≤ roundPotential st, (runRounds rounds st).v ≠ 0 := by
    intro rounds hrounds hv
    apply htermination
    exact ⟨rounds, hrounds, hv⟩
  have hprefix :
      ∀ index < roundPotential st + 1, (runRounds index st).v ≠ 0 := by
    intro index hindex
    apply hnonzero index
    omega
  have hbound :
      roundPotential (runRounds (roundPotential st + 1) st) +
          (roundPotential st + 1) ≤ roundPotential st :=
    roundPotential_add_rounds_le_of_all_prefix_v_ne_zero
      (roundPotential st + 1) st huPos hactive hprefix
  omega

/-- A `2n` fixed schedule reaches the terminal `v = 0` state whenever the
initial binary-size potential fits in its round budget. -/
theorem fixedRoundState_v_eq_zero_of_size_budget (n p x : Nat)
    (hp : 0 < p) (hbudget : Nat.size p + Nat.size x ≤ 2 * n) :
    (fixedRoundState n p x).v = 0 := by
  have htermination :
      ∃ rounds ≤ roundPotential (initial p x),
        (runRounds rounds (initial p x)).v = 0 :=
    exists_runRounds_v_eq_zero_of_active (initial p x) (by simpa [initial] using hp) rfl
  rcases htermination with ⟨rounds, hrounds, hv⟩
  have hroundsSize : rounds ≤ Nat.size p + Nat.size x := by
    simpa [roundPotential, initial] using hrounds
  have hroundsBudget : rounds ≤ 2 * n := by
    exact hroundsSize.trans hbudget
  have hsum : rounds + (2 * n - rounds) = 2 * n :=
    Nat.add_sub_of_le hroundsBudget
  rw [fixedRoundState, fixedRoundCount, ← hsum, runRounds_add]
  exact runRounds_v_eq_zero_of_v_eq_zero (2 * n - rounds)
    (runRounds rounds (initial p x)) hv

/-- Any positive suffix after `v` has reached zero leaves the source in
inactive padding mode. -/
theorem runRounds_active_eq_false_of_pos_of_v_eq_zero
    (rounds : Nat) (st : RoundState) (hrounds : 0 < rounds)
    (hv : st.v = 0) :
    (runRounds rounds st).active = false := by
  cases rounds with
  | zero => omega
  | succ rounds =>
      rw [runRounds_succ_eq_round_runRounds]
      have hvPrefix : (runRounds rounds st).v = 0 :=
        runRounds_v_eq_zero_of_v_eq_zero rounds st hv
      cases hactive : (runRounds rounds st).active <;>
        simp [round, hactive, hvPrefix]

/-- A positive-`u` active state reaches `v = 0` strictly before exhausting
its binary-size potential.  The remaining unit is supplied by the positive
terminal `u` word. -/
theorem exists_runRounds_v_eq_zero_before_roundPotential
    (st : RoundState) (huPos : 0 < st.u) (hactive : st.active = true) :
    ∃ rounds < roundPotential st, (runRounds rounds st).v = 0 := by
  have hbounded := exists_runRounds_v_eq_zero_of_active st huPos hactive
  have hexists : ∃ rounds, (runRounds rounds st).v = 0 := by
    rcases hbounded with ⟨rounds, _hrounds, hv⟩
    exact ⟨rounds, hv⟩
  let rounds := Nat.find hexists
  have hv : (runRounds rounds st).v = 0 := by
    simpa only [rounds] using Nat.find_spec hexists
  have hprefix : ∀ index < rounds, (runRounds index st).v ≠ 0 := by
    intro index hindex hzero
    have hleast : rounds ≤ index := by
      dsimp only [rounds]
      exact Nat.find_min' hexists hzero
    omega
  have hcharge := roundPotential_add_rounds_le_of_all_prefix_v_ne_zero
    rounds st huPos hactive hprefix
  have huTerminal : 0 < (runRounds rounds st).u :=
    runRounds_u_pos_of_pos rounds st huPos
  have hterminalPotential : 0 < roundPotential (runRounds rounds st) := by
    unfold roundPotential
    have hsize : 0 < Nat.size (runRounds rounds st).u :=
      Nat.size_pos.2 huTerminal
    omega
  exact ⟨rounds, by omega, hv⟩

/-- The standard `2n` schedule contains at least one post-termination round,
so its terminal mode flag is clean. -/
theorem fixedRoundState_active_eq_false_of_size_budget
    (n p x : Nat) (hp : 0 < p)
    (hbudget : Nat.size p + Nat.size x ≤ 2 * n) :
    (fixedRoundState n p x).active = false := by
  rcases exists_runRounds_v_eq_zero_before_roundPotential
      (initial p x) (by simpa [initial] using hp) rfl with
    ⟨rounds, hrounds, hv⟩
  have hroundsBudget : rounds < 2 * n := by
    have hpotential : roundPotential (initial p x) ≤ 2 * n := by
      simpa [roundPotential, initial] using hbudget
    omega
  have hsuffixPos : 0 < 2 * n - rounds := by omega
  have hsum : rounds + (2 * n - rounds) = 2 * n :=
    Nat.add_sub_of_le (Nat.le_of_lt hroundsBudget)
  rw [fixedRoundState, fixedRoundCount, ← hsum, runRounds_add]
  exact runRounds_active_eq_false_of_pos_of_v_eq_zero
    (2 * n - rounds) (runRounds rounds (initial p x)) hsuffixPos hv

/-- Equivalently, the fixed schedule has entered the positive padding-count
range once the binary-size budget is available. -/
theorem fixedRoundState_paddingSteps_pos_of_size_budget
    (n p x : Nat) (hp : 0 < p)
    (hbudget : Nat.size p + Nat.size x ≤ 2 * n) :
    0 < (fixedRoundState n p x).paddingSteps := by
  have hmode := runRounds_activeCounterInvariant (fixedRoundCount n)
    (initial p x) (initial_activeCounterInvariant p x)
  change activeCounterInvariant (fixedRoundState n p x) at hmode
  rw [activeCounterInvariant,
    fixedRoundState_active_eq_false_of_size_budget n p x hp hbudget] at hmode
  have hne : (fixedRoundState n p x).paddingSteps ≠ 0 := by
    simpa using hmode
  exact Nat.pos_of_ne_zero hne

/-! ## Coprimality and the fixed endpoint -/

/-- The `uEven` branch preserves coprimality of the binary-GCD pair. -/
theorem applyBranch_uEven_coprime (st : RoundState) (huEven : st.u % 2 = 0)
    (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (applyBranch Branch.uEven st).u (applyBranch Branch.uEven st).v := by
  have hhalf : 2 * (st.u / 2) = st.u :=
    Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.u huEven
  have hdiv : st.u / 2 ∣ st.u := by
    refine ⟨2, ?_⟩
    simpa [Nat.mul_comm] using hhalf.symm
  change Nat.Coprime (st.u / 2) st.v
  exact Nat.Coprime.of_dvd_left hdiv hcoprime

/-- The `vEven` branch preserves coprimality of the binary-GCD pair. -/
theorem applyBranch_vEven_coprime (st : RoundState) (hvEven : st.v % 2 = 0)
    (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (applyBranch Branch.vEven st).u (applyBranch Branch.vEven st).v := by
  have hhalf : 2 * (st.v / 2) = st.v :=
    Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.v hvEven
  have hdiv : st.v / 2 ∣ st.v := by
    refine ⟨2, ?_⟩
    simpa [Nat.mul_comm] using hhalf.symm
  change Nat.Coprime st.u (st.v / 2)
  exact Nat.Coprime.of_dvd_right hdiv hcoprime

/-- The `uGreater` branch preserves coprimality of the binary-GCD pair. -/
theorem applyBranch_uGreater_coprime (st : RoundState)
    (huEven : st.u % 2 ≠ 0) (hvEven : st.v % 2 ≠ 0) (hlt : st.v < st.u)
    (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (applyBranch Branch.uGreater st).u
      (applyBranch Branch.uGreater st).v := by
  have hsub : st.v ≤ st.u := Nat.le_of_lt hlt
  have hhalf : 2 * ((st.u - st.v) / 2) = st.u - st.v :=
    Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.u - st.v)
      (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero
        hsub huEven hvEven)
  have hdiv : (st.u - st.v) / 2 ∣ st.u - st.v := by
    refine ⟨2, ?_⟩
    simpa [Nat.mul_comm] using hhalf.symm
  have hsubCoprime : Nat.Coprime (st.u - st.v) st.v :=
    (Nat.coprime_sub_self_left hsub).mpr hcoprime
  change Nat.Coprime ((st.u - st.v) / 2) st.v
  exact Nat.Coprime.of_dvd_left hdiv hsubCoprime

/-- The `vLe` branch preserves coprimality of the binary-GCD pair. -/
theorem applyBranch_vLe_coprime (st : RoundState)
    (huEven : st.u % 2 ≠ 0) (hvEven : st.v % 2 ≠ 0) (hlt : ¬ st.v < st.u)
    (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (applyBranch Branch.vLe st).u (applyBranch Branch.vLe st).v := by
  have hsub : st.u ≤ st.v := Nat.le_of_not_gt hlt
  have hhalf : 2 * ((st.v - st.u) / 2) = st.v - st.u :=
    Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.v - st.u)
      (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero
        hsub hvEven huEven)
  have hdiv : (st.v - st.u) / 2 ∣ st.v - st.u := by
    refine ⟨2, ?_⟩
    simpa [Nat.mul_comm] using hhalf.symm
  have hsubCoprime : Nat.Coprime st.u (st.v - st.u) :=
    (Nat.coprime_sub_self_right hsub).mpr hcoprime
  change Nat.Coprime st.u ((st.v - st.u) / 2)
  exact Nat.Coprime.of_dvd_right hdiv hsubCoprime

/-- One source round preserves coprimality of the binary-GCD pair. -/
theorem round_coprime (st : RoundState) (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (round st).u (round st).v := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa using hcoprime
  · by_cases hv0 : st.v = 0
    · rw [round_active_terminated st hactive hv0]
      simpa using hcoprime
    · by_cases huEven : st.u % 2 = 0
      · rw [round_active_nonzero_uEven st hactive hv0 huEven]
        exact applyBranch_uEven_coprime st huEven hcoprime
      · by_cases hvEven : st.v % 2 = 0
        · rw [round_active_nonzero_vEven st hactive hv0 huEven hvEven]
          exact applyBranch_vEven_coprime st hvEven hcoprime
        · by_cases hlt : st.v < st.u
          · rw [round_active_nonzero_uGreater st hactive hv0 huEven hvEven hlt]
            exact applyBranch_uGreater_coprime st huEven hvEven hlt hcoprime
          · rw [round_active_nonzero_vLe st hactive hv0 huEven hvEven hlt]
            exact applyBranch_vLe_coprime st huEven hvEven hlt hcoprime

/-- Coprimality persists through all fixed rounds. -/
theorem runRounds_coprime (rounds : Nat) (st : RoundState)
    (hcoprime : Nat.Coprime st.u st.v) :
    Nat.Coprime (runRounds rounds st).u (runRounds rounds st).v := by
  induction rounds generalizing st with
  | zero =>
      simpa [runRounds] using hcoprime
  | succ rounds ih =>
      exact ih (round st) (round_coprime st hcoprime)

/-- Under the binary-size round budget, a positive coprime input finishes with
`u = 1`. -/
theorem fixedRoundState_u_eq_one_of_coprime (n p x : Nat)
    (hp : 0 < p) (hbudget : Nat.size p + Nat.size x ≤ 2 * n)
    (hcoprime : Nat.Coprime p x) :
    (fixedRoundState n p x).u = 1 := by
  have hv : (fixedRoundState n p x).v = 0 :=
    fixedRoundState_v_eq_zero_of_size_budget n p x hp hbudget
  have hinitial : Nat.Coprime (initial p x).u (initial p x).v := by
    simpa [initial] using hcoprime
  have hfinish :
      Nat.Coprime (fixedRoundState n p x).u (fixedRoundState n p x).v := by
    simpa [fixedRoundState] using
      runRounds_coprime (fixedRoundCount n) (initial p x) hinitial
  rw [hv] at hfinish
  exact (fixedRoundState n p x).u.coprime_zero_right.mp hfinish

/-- Width-form wrapper for the fixed binary-GCD endpoint theorem. -/
theorem fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow (n p x : Nat)
    (hp : 0 < p) (hpWidth : p < 2 ^ n) (hxWidth : x < 2 ^ n)
    (hcoprime : Nat.Coprime p x) :
    (fixedRoundState n p x).u = 1 := by
  apply fixedRoundState_u_eq_one_of_coprime n p x hp ?_ hcoprime
  have hpSize : Nat.size p ≤ n := Nat.size_le.mpr hpWidth
  have hxSize : Nat.size x ≤ n := Nat.size_le.mpr hxWidth
  omega

/-! ## Coefficient growth and compact correction bounds -/

/-- Each coefficient is bounded by the power of two determined by the number
of active Kaliski updates completed so far.  Padding rounds leave this bound
unchanged. -/
def coefficientGrowthInvariant (st : RoundState) : Prop :=
  st.rCoeff ≤ 2 ^ st.kaliskiSteps ∧ st.sCoeff ≤ 2 ^ st.kaliskiSteps

theorem initial_coefficientGrowthInvariant (p x : Nat) :
    coefficientGrowthInvariant (initial p x) := by
  simp [coefficientGrowthInvariant, initial]

/-- One active branch preserves the coefficient-growth bound. -/
theorem applyBranch_coefficientGrowthInvariant (branch : Branch) (st : RoundState)
    (hinv : coefficientGrowthInvariant st) :
    coefficientGrowthInvariant (applyBranch branch st) := by
  rcases hinv with ⟨hr, hs⟩
  cases branch <;>
    simp only [coefficientGrowthInvariant, applyBranch, Nat.pow_succ] at * <;>
    omega

/-- One fixed source round preserves the coefficient-growth bound. -/
theorem round_coefficientGrowthInvariant (st : RoundState)
    (hinv : coefficientGrowthInvariant st) :
    coefficientGrowthInvariant (round st) := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa [coefficientGrowthInvariant] using hinv
  · by_cases hv : st.v = 0
    · rw [round_active_terminated st hactive hv]
      simpa [coefficientGrowthInvariant] using hinv
    · rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv]
      exact applyBranch_coefficientGrowthInvariant (selectBranch st) st hinv

/-- The coefficient-growth bound persists through an arbitrary fixed prefix. -/
theorem runRounds_coefficientGrowthInvariant (rounds : Nat) (st : RoundState)
    (hinv : coefficientGrowthInvariant st) :
    coefficientGrowthInvariant (runRounds rounds st) := by
  induction rounds generalizing st with
  | zero =>
      exact hinv
  | succ rounds ih =>
      exact ih (round st) (round_coefficientGrowthInvariant st hinv)

/-- At a terminal normalized binary-GCD state, the surviving `s` coefficient
is exactly the modulus. -/
theorem sCoeff_eq_modulus_of_terminal (p : Nat) (st : RoundState)
    (hinv : BezoutInvariant p st) (hv : st.v = 0) (hu : st.u = 1) :
    st.sCoeff = p := by
  simpa [BezoutInvariant, bezoutValue, hv, hu] using hinv

/-- Fixed-round specialization of `sCoeff_eq_modulus_of_terminal`. -/
theorem fixedRoundState_sCoeff_eq_modulus_of_terminal (n p x : Nat)
    (hv : (fixedRoundState n p x).v = 0)
    (hu : (fixedRoundState n p x).u = 1) :
    (fixedRoundState n p x).sCoeff = p :=
  sCoeff_eq_modulus_of_terminal p (fixedRoundState n p x)
    (fixedRoundState_bezoutInvariant n p x) hv hu

/-- A strict full-width modulus forces at least one active Kaliski update per
word bit before the fixed `2n` schedule can enter padding mode. -/
theorem fixedRoundState_paddingSteps_le_width_of_strict_full_width
    (n p x : Nat) (hp : 0 < p)
    (hpWidth : p < 2 ^ n) (hxWidth : x < 2 ^ n)
    (hcoprime : Nat.Coprime p x) (hfull : 2 ^ (n - 1) < p) :
    (fixedRoundState n p x).paddingSteps ≤ n := by
  have hv : (fixedRoundState n p x).v = 0 := by
    apply fixedRoundState_v_eq_zero_of_size_budget n p x hp
    have hpSize : Nat.size p ≤ n := Nat.size_le.mpr hpWidth
    have hxSize : Nat.size x ≤ n := Nat.size_le.mpr hxWidth
    omega
  have hu : (fixedRoundState n p x).u = 1 :=
    fixedRoundState_u_eq_one_of_coprime_of_lt_two_pow n p x hp hpWidth hxWidth hcoprime
  have hs : (fixedRoundState n p x).sCoeff = p :=
    fixedRoundState_sCoeff_eq_modulus_of_terminal n p x hv hu
  have hgrowth : coefficientGrowthInvariant (fixedRoundState n p x) := by
    simpa [fixedRoundState] using
      runRounds_coefficientGrowthInvariant (fixedRoundCount n) (initial p x)
        (initial_coefficientGrowthInvariant p x)
  have hpLe : p ≤ 2 ^ (fixedRoundState n p x).kaliskiSteps := by
    simpa [hs] using hgrowth.2
  have hk : n ≤ (fixedRoundState n p x).kaliskiSteps := by
    by_contra hnot
    have hkLt : (fixedRoundState n p x).kaliskiSteps < n := by
      omega
    have hkPow :
        2 ^ (fixedRoundState n p x).kaliskiSteps ≤ 2 ^ (n - 1) := by
      apply Nat.pow_le_pow_right (by omega)
      omega
    omega
  have htotal := fixedRoundState_totalRounds n p x
  unfold totalRounds at htotal
  omega

/-- For an odd full-width modulus, the weak lower bit-length bound is enough
to obtain the strict form needed by the compact correction counter. -/
theorem fixedRoundState_paddingSteps_le_width_of_full_width_odd
    (n p x : Nat) (hp : 0 < p)
    (hpWidth : p < 2 ^ n) (hx : 0 < x) (hxWidth : x < 2 ^ n)
    (hcoprime : Nat.Coprime p x) (hfull : 2 ^ (n - 1) ≤ p) (hodd : Odd p) :
    (fixedRoundState n p x).paddingSteps ≤ n := by
  cases n with
  | zero =>
      have htotal := fixedRoundState_totalRounds 0 p x
      unfold totalRounds at htotal
      omega
  | succ n =>
      cases n with
      | zero =>
          change (fixedRoundState 1 p x).paddingSteps ≤ 1
          have hk : 0 < (fixedRoundState 1 p x).kaliskiSteps :=
            fixedRoundState_kaliskiSteps_pos 1 p x (by omega) hx
          have htotal := fixedRoundState_totalRounds 1 p x
          unfold totalRounds at htotal
          omega
      | succ n =>
          apply fixedRoundState_paddingSteps_le_width_of_strict_full_width
            (n + 2) p x hp hpWidth hxWidth hcoprime
          have hbase : 2 ^ (n + 1) ≤ p := by
            simpa using hfull
          by_contra hnot
          have hpEq : p = 2 ^ (n + 1) := by
            apply Nat.le_antisymm
            · calc
                p ≤ 2 ^ (n + 1) := by
                  exact le_of_not_gt hnot
                _ = 2 ^ (n + 1) := rfl
            · exact hbase
          have heven : Even p := by
            refine ⟨2 ^ n, ?_⟩
            calc
              p = 2 ^ (n + 1) := hpEq
              _ = 2 ^ n + 2 ^ n := by
                rw [Nat.pow_succ]
                omega
          exact (Nat.not_even_iff_odd.mpr hodd) heven

end RoundState
end NumberTheory.BinaryGCD
end QuantumAlg

end

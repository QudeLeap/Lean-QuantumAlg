/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Nat.Binary.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Fixed-round binary-GCD semantics

This quantum-free module owns the mathematical definitions used by the
fixed-round binary-GCD realization.  Physical registers and gate schedules
remain in `QuantumAlg.Primitives`.
-/

section

namespace QuantumAlg
namespace NumberTheory.BinaryGCD

/-- Number of rounds in the width-indexed fixed binary-GCD schedule. -/
def fixedRoundCount (width : Nat) : Nat := 2 * width

@[simp] lemma fixedRoundCount_eq (width : Nat) :
    fixedRoundCount width = 2 * width := rfl

/-! ## Branch encoding -/

/-- The four active Kaliski branches encoded by the round circuit
[RNSL17, ECDLP.tex:405-408,471]. -/
inductive Branch where
  /-- The `u` register is even. -/
  | uEven
  /-- The `u` register is odd and the `v` register is even. -/
  | vEven
  /-- Both registers are odd and `u > v`. -/
  | uGreater
  /-- Both registers are odd and `u <= v`. -/
  | vLe
deriving DecidableEq, Repr

namespace Branch

/-- The auxiliary encoder bit `a` in the RNSL17 branch code
`10, 01, 11, 00` [RNSL17, ECDLP.tex:468-475]. -/
def auxBit : Branch -> Bool
  | uEven => true
  | vEven => false
  | uGreater => true
  | vLe => false

/-- The stored per-round branch-history bit `m_i`, i.e. the second bit `b` in
the RNSL17 branch code `10, 01, 11, 00` [RNSL17, ECDLP.tex:468-475]. -/
def historyBit : Branch -> Bool
  | uEven => false
  | vEven => true
  | uGreater => true
  | vLe => false

/-- The full two-bit branch code before the redundant auxiliary bit is
uncomputed. -/
def code (branch : Branch) : Bool × Bool :=
  (branch.auxBit, branch.historyBit)

@[simp] lemma code_uEven : code uEven = (true, false) := rfl

@[simp] lemma code_vEven : code vEven = (false, true) := rfl

@[simp] lemma code_uGreater : code uGreater = (true, true) := rfl

@[simp] lemma code_vLe : code vLe = (false, false) := rfl

/-- Branch selected from the circuit-facing condition signals: the low `u`
bit, the low `v` bit, and the staged comparison bit `v < u`. -/
def fromCircuitSignals (uOdd vOdd compare : Bool) : Branch :=
  if uOdd then
    if vOdd then
      if compare then uGreater else vLe
    else vEven
  else uEven


@[simp] lemma fromCircuitSignals_uEven (vOdd compare : Bool) :
    fromCircuitSignals false vOdd compare = uEven := by
  simp [fromCircuitSignals]

@[simp] lemma fromCircuitSignals_vEven (compare : Bool) :
    fromCircuitSignals true false compare = vEven := by
  simp [fromCircuitSignals]

@[simp] lemma fromCircuitSignals_uGreater :
    fromCircuitSignals true true true = uGreater := by
  simp [fromCircuitSignals]

@[simp] lemma fromCircuitSignals_vLe :
    fromCircuitSignals true true false = vLe := by
  simp [fromCircuitSignals]

/-- The auxiliary branch-code bit selected by the circuit-facing condition
signals. -/
lemma fromCircuitSignals_auxBit (uOdd vOdd compare : Bool) :
    (fromCircuitSignals uOdd vOdd compare).auxBit =
      (!uOdd || (vOdd && compare)) := by
  cases uOdd <;> cases vOdd <;> cases compare <;> rfl

/-- The branch-history code bit selected by the circuit-facing condition
signals. -/
lemma fromCircuitSignals_historyBit (uOdd vOdd compare : Bool) :
    (fromCircuitSignals uOdd vOdd compare).historyBit =
      (uOdd && (!vOdd || compare)) := by
  cases uOdd <;> cases vOdd <;> cases compare <;> rfl

/-- The full branch code selected by the circuit-facing condition signals. -/
lemma fromCircuitSignals_code (uOdd vOdd compare : Bool) :
    code (fromCircuitSignals uOdd vOdd compare) =
      (!uOdd || (vOdd && compare), uOdd && (!vOdd || compare)) := by
  rw [code, fromCircuitSignals_auxBit, fromCircuitSignals_historyBit]

/-- The selected auxiliary code bit in disjoint selector-term form. -/
lemma fromCircuitSignals_auxBit_disjoint (uOdd vOdd compare : Bool) :
    (fromCircuitSignals uOdd vOdd compare).auxBit =
      (!uOdd || (uOdd && vOdd && compare)) := by
  cases uOdd <;> cases vOdd <;> cases compare <;> rfl

/-- The selected branch-history code bit in disjoint selector-term form. -/
lemma fromCircuitSignals_historyBit_disjoint (uOdd vOdd compare : Bool) :
    (fromCircuitSignals uOdd vOdd compare).historyBit =
      ((uOdd && !vOdd) || (uOdd && vOdd && compare)) := by
  cases uOdd <;> cases vOdd <;> cases compare <;> rfl

/-- The selected two-bit branch code in disjoint selector-term form. -/
lemma fromCircuitSignals_code_disjoint (uOdd vOdd compare : Bool) :
    code (fromCircuitSignals uOdd vOdd compare) =
      (!uOdd || (uOdd && vOdd && compare),
       (uOdd && !vOdd) || (uOdd && vOdd && compare)) := by
  rw [code, fromCircuitSignals_auxBit_disjoint,
    fromCircuitSignals_historyBit_disjoint]

end Branch

/-! ## Fixed-round state -/

/-- Integer state of the Montgomery--Kaliski loop before Montgomery correction.
The `active` flag represents the RNSL17 Kaliski-mode flag: while it is true, a
round updates `u,v,r,s`; once the loop has terminated, fixed rounds increment a
padding counter instead [RNSL17, ECDLP.tex:406-475]. -/
structure RoundState where
  /-- Binary-GCD register `u`. -/
  u : Nat
  /-- Binary-GCD register `v`. -/
  v : Nat
  /-- Coefficient register `r`. -/
  rCoeff : Nat
  /-- Coefficient register `s`. -/
  sCoeff : Nat
  /-- Number of Kaliski updates already executed. -/
  kaliskiSteps : Nat
  /-- Number of fixed padding/counter rounds already executed after termination. -/
  paddingSteps : Nat
  /-- True while the Kaliski update path is still active. -/
  active : Bool
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprRoundState.repr

namespace RoundState

/-- Initial RNSL17 integer loop state for modulus `p` and input representative
`x`: `xmg p x 0 1 0` [RNSL17, ECDLP.tex:399-421]. -/
def initial (p x : Nat) : RoundState where
  u := p
  v := x
  rCoeff := 0
  sCoeff := 1
  kaliskiSteps := 0
  paddingSteps := 0
  active := true


/-- Total number of fixed rounds consumed so far. -/
def totalRounds (st : RoundState) : Nat :=
  st.kaliskiSteps + st.paddingSteps

@[simp] lemma totalRounds_initial (p x : Nat) :
    totalRounds (initial p x) = 0 := by
  rfl

/-- Branch selected by the active Kaliski loop.  The termination case `v = 0`
is handled outside this selector, matching the source pseudocode where
termination precedes the four update branches [RNSL17, ECDLP.tex:399-421]. -/
def selectBranch (st : RoundState) : Branch :=
  if st.u % 2 = 0 then
    Branch.uEven
  else if st.v % 2 = 0 then
    Branch.vEven
  else if st.v < st.u then
    Branch.uGreater
  else
    Branch.vLe

/-- Source-level branch selection agrees with the circuit-facing selector
signals: low `u`, low `v`, and the staged comparison predicate `v < u`. -/
lemma selectBranch_eq_fromCircuitSignals (st : RoundState) :
    selectBranch st =
      Branch.fromCircuitSignals (decide (st.u % 2 ≠ 0))
        (decide (st.v % 2 ≠ 0)) (decide (st.v < st.u)) := by
  by_cases hu : st.u % 2 = 0
  · simp [selectBranch, Branch.fromCircuitSignals, hu]
  · by_cases hv : st.v % 2 = 0
    · simp [selectBranch, Branch.fromCircuitSignals, hu, hv]
    · by_cases hlt : st.v < st.u
      · simp [selectBranch, Branch.fromCircuitSignals, hu, hv, hlt]
      · simp [selectBranch, Branch.fromCircuitSignals, hu, hv, hlt]


/-- If `u` is even, the active Kaliski selector chooses `uEven`. -/
lemma selectBranch_uEven_of_even (st : RoundState)
    (hu : st.u % 2 = 0) :
    selectBranch st = Branch.uEven := by
  simp [selectBranch, hu]

/-- If `u` is odd and `v` is even, the active Kaliski selector chooses
`vEven`. -/
lemma selectBranch_vEven_of_u_odd_v_even (st : RoundState)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 = 0) :
    selectBranch st = Branch.vEven := by
  simp [selectBranch, hu, hv]

/-- If both words are odd and `v < u`, the active Kaliski selector chooses
`uGreater`. -/
lemma selectBranch_uGreater_of_odd_odd_lt (st : RoundState)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : st.v < st.u) :
    selectBranch st = Branch.uGreater := by
  simp [selectBranch, hu, hv, hlt]

/-- If both words are odd and `v < u` is false, the active Kaliski selector
chooses `vLe`. -/
lemma selectBranch_vLe_of_odd_odd_not_lt (st : RoundState)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : ¬ st.v < st.u) :
    selectBranch st = Branch.vLe := by
  simp [selectBranch, hu, hv, hlt]

/-- Apply one active Montgomery--Kaliski update branch.  Shifts are represented
by multiplication/division by two, as in the RNSL17 round description
[RNSL17, ECDLP.tex:399-421,425-442]. -/
def applyBranch (branch : Branch) (st : RoundState) : RoundState :=
  match branch with
  | Branch.uEven =>
      { st with
        u := st.u / 2
        sCoeff := 2 * st.sCoeff
        kaliskiSteps := st.kaliskiSteps + 1 }
  | Branch.vEven =>
      { st with
        v := st.v / 2
        rCoeff := 2 * st.rCoeff
        kaliskiSteps := st.kaliskiSteps + 1 }
  | Branch.uGreater =>
      { st with
        u := (st.u - st.v) / 2
        rCoeff := st.rCoeff + st.sCoeff
        sCoeff := 2 * st.sCoeff
        kaliskiSteps := st.kaliskiSteps + 1 }
  | Branch.vLe =>
      { st with
        v := (st.v - st.u) / 2
        rCoeff := 2 * st.rCoeff
        sCoeff := st.rCoeff + st.sCoeff
        kaliskiSteps := st.kaliskiSteps + 1 }

/-- Source-level coefficient value `r*v + s*u` from the Kaliski loop invariant
[RNSL17, ECDLP.tex:473]. -/
def bezoutValue (st : RoundState) : Nat :=
  st.rCoeff * st.v + st.sCoeff * st.u

/-- Source-level Kaliski coefficient invariant `r*v + s*u = p`
[RNSL17, ECDLP.tex:473]. -/
def BezoutInvariant (p : Nat) (st : RoundState) : Prop :=
  bezoutValue st = p

lemma initial_bezoutInvariant (p x : Nat) :
    BezoutInvariant p (initial p x) := by
  simp [BezoutInvariant, bezoutValue, initial]

/-- Kaliski coefficient/input congruence for the `u` word, proved here for
the source recurrence [RNSL17, ECDLP.tex:405-409]: after `k` active updates,
`r*x = -2^k*u` in `ZMod p`. -/
def scaledUCongruence (p x : Nat) (st : RoundState) : Prop :=
  (st.rCoeff : ZMod p) * (x : ZMod p) =
    -((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p))

/-- Kaliski coefficient/input congruence for the `v` word: after `k` active
updates, `s*x = 2^k*v` in `ZMod p`. -/
def scaledVCongruence (p x : Nat) (st : RoundState) : Prop :=
  (st.sCoeff : ZMod p) * (x : ZMod p) =
    (2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p)

/-- Paired source-level congruence invariant relating both coefficients to
the input word throughout the Kaliski loop. -/
def scaledInputCongruence (p x : Nat) (st : RoundState) : Prop :=
  scaledUCongruence p x st ∧ scaledVCongruence p x st

lemma initial_scaledInputCongruence (p x : Nat) :
    scaledInputCongruence p x (initial p x) := by
  simp [scaledInputCongruence, scaledUCongruence, scaledVCongruence, initial]



/-- The `uEven` source branch preserves the coefficient invariant value when
the halving side condition is supplied explicitly. -/
lemma applyBranch_uEven_bezoutValue_of_halving
    (st : RoundState) (hhalf : 2 * (st.u / 2) = st.u) :
    bezoutValue (applyBranch Branch.uEven st) = bezoutValue st := by
  change
    st.rCoeff * st.v + (2 * st.sCoeff) * (st.u / 2) =
      st.rCoeff * st.v + st.sCoeff * st.u
  nlinarith

/-- The `vEven` source branch preserves the coefficient invariant value when
the halving side condition is supplied explicitly. -/
lemma applyBranch_vEven_bezoutValue_of_halving
    (st : RoundState) (hhalf : 2 * (st.v / 2) = st.v) :
    bezoutValue (applyBranch Branch.vEven st) = bezoutValue st := by
  change
    (2 * st.rCoeff) * (st.v / 2) + st.sCoeff * st.u =
      st.rCoeff * st.v + st.sCoeff * st.u
  nlinarith

/-- The `uGreater` source branch preserves the coefficient invariant value when
the subtraction and halving side conditions are supplied explicitly. -/
lemma applyBranch_uGreater_bezoutValue_of_sub_halving
    (st : RoundState)
    (hsub : st.v <= st.u)
    (hhalf : 2 * ((st.u - st.v) / 2) = st.u - st.v) :
    bezoutValue (applyBranch Branch.uGreater st) = bezoutValue st := by
  change
    (st.rCoeff + st.sCoeff) * st.v +
        (2 * st.sCoeff) * ((st.u - st.v) / 2) =
      st.rCoeff * st.v + st.sCoeff * st.u
  have hcancel : st.u - st.v + st.v = st.u := Nat.sub_add_cancel hsub
  nlinarith

/-- The `vLe` source branch preserves the coefficient invariant value when the
subtraction and halving side conditions are supplied explicitly. -/
lemma applyBranch_vLe_bezoutValue_of_sub_halving
    (st : RoundState)
    (hsub : st.u <= st.v)
    (hhalf : 2 * ((st.v - st.u) / 2) = st.v - st.u) :
    bezoutValue (applyBranch Branch.vLe st) = bezoutValue st := by
  change
    (2 * st.rCoeff) * ((st.v - st.u) / 2) +
        (st.rCoeff + st.sCoeff) * st.u =
      st.rCoeff * st.v + st.sCoeff * st.u
  have hcancel : st.v - st.u + st.u = st.v := Nat.sub_add_cancel hsub
  nlinarith

lemma applyBranch_uEven_scaledInputCongruence_of_halving
    (p x : Nat) (st : RoundState)
    (hhalf : 2 * (st.u / 2) = st.u)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (applyBranch Branch.uEven st) := by
  rcases hinv with ⟨hu, hv⟩
  constructor
  · have hhalfZ :
        (st.u : ZMod p) = (2 : ZMod p) * ((st.u / 2 : Nat) : ZMod p) := by
      simpa [Nat.cast_mul] using
        congrArg (fun value : Nat => (value : ZMod p)) hhalf.symm
    change
      (st.rCoeff : ZMod p) * (x : ZMod p) =
        -((2 : ZMod p) ^ (st.kaliskiSteps + 1) *
          ((st.u / 2 : Nat) : ZMod p))
    calc
      (st.rCoeff : ZMod p) * (x : ZMod p)
          = -((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p)) := hu
      _ = -((2 : ZMod p) ^ (st.kaliskiSteps + 1) *
            ((st.u / 2 : Nat) : ZMod p)) := by
        rw [hhalfZ]
        ring
  · change
      (((2 * st.sCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        (2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.v : ZMod p)
    calc
      (((2 * st.sCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((2 : ZMod p) * st.sCoeff) * (x : ZMod p) := by
        simp [Nat.cast_mul]
      _ = (2 : ZMod p) * ((st.sCoeff : ZMod p) * x) := by
        ring
      _ = (2 : ZMod p) *
            ((2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p)) := by
        rw [hv]
      _ = (2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.v : ZMod p) := by
        ring

lemma applyBranch_vEven_scaledInputCongruence_of_halving
    (p x : Nat) (st : RoundState)
    (hhalf : 2 * (st.v / 2) = st.v)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (applyBranch Branch.vEven st) := by
  rcases hinv with ⟨hu, hv⟩
  constructor
  · change
      (((2 * st.rCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        -((2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.u : ZMod p))
    calc
      (((2 * st.rCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((2 : ZMod p) * st.rCoeff) * (x : ZMod p) := by
        simp [Nat.cast_mul]
      _ = (2 : ZMod p) * ((st.rCoeff : ZMod p) * x) := by
        ring
      _ = (2 : ZMod p) *
            (-((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p))) := by
        rw [hu]
      _ = -((2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.u : ZMod p)) := by
        ring
  · have hhalfZ :
        (st.v : ZMod p) = (2 : ZMod p) * ((st.v / 2 : Nat) : ZMod p) := by
      simpa [Nat.cast_mul] using
        congrArg (fun value : Nat => (value : ZMod p)) hhalf.symm
    change
      (st.sCoeff : ZMod p) * (x : ZMod p) =
        (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
          ((st.v / 2 : Nat) : ZMod p)
    calc
      (st.sCoeff : ZMod p) * (x : ZMod p)
          = (2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p) := hv
      _ = (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
            ((st.v / 2 : Nat) : ZMod p) := by
        rw [hhalfZ]
        ring

lemma applyBranch_uGreater_scaledInputCongruence_of_sub_halving
    (p x : Nat) (st : RoundState)
    (hsub : st.v <= st.u)
    (hhalf : 2 * ((st.u - st.v) / 2) = st.u - st.v)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (applyBranch Branch.uGreater st) := by
  rcases hinv with ⟨hu, hv⟩
  constructor
  · have hsubZ :
        ((st.u - st.v : Nat) : ZMod p) =
          (st.u : ZMod p) - (st.v : ZMod p) := by
      have hcancel : st.u - st.v + st.v = st.u := Nat.sub_add_cancel hsub
      apply add_right_cancel (b := (st.v : ZMod p))
      rw [sub_add_cancel]
      simpa [Nat.cast_add] using
        congrArg (fun value : Nat => (value : ZMod p)) hcancel
    have hhalfZ :
        ((st.u - st.v : Nat) : ZMod p) =
          (2 : ZMod p) * (((st.u - st.v) / 2 : Nat) : ZMod p) := by
      simpa [Nat.cast_mul] using
        congrArg (fun value : Nat => (value : ZMod p)) hhalf.symm
    change
      (((st.rCoeff + st.sCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        -((2 : ZMod p) ^ (st.kaliskiSteps + 1) *
          (((st.u - st.v) / 2 : Nat) : ZMod p))
    calc
      (((st.rCoeff + st.sCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((st.rCoeff : ZMod p) + st.sCoeff) * (x : ZMod p) := by
        simp [Nat.cast_add]
      _ = (st.rCoeff : ZMod p) * x + (st.sCoeff : ZMod p) * x := by
        ring
      _ = -((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p)) +
            (2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p) := by
        rw [hu, hv]
      _ = -((2 : ZMod p) ^ (st.kaliskiSteps + 1) *
            (((st.u - st.v) / 2 : Nat) : ZMod p)) := by
        have hpowHalf :
            (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
                (((st.u - st.v) / 2 : Nat) : ZMod p) =
              (2 : ZMod p) ^ st.kaliskiSteps *
                ((st.u - st.v : Nat) : ZMod p) := by
          rw [pow_succ, hhalfZ]
          ring
        rw [hpowHalf, hsubZ]
        ring
  · change
      (((2 * st.sCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        (2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.v : ZMod p)
    calc
      (((2 * st.sCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((2 : ZMod p) * st.sCoeff) * (x : ZMod p) := by
        simp [Nat.cast_mul]
      _ = (2 : ZMod p) * ((st.sCoeff : ZMod p) * x) := by
        ring
      _ = (2 : ZMod p) *
            ((2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p)) := by
        rw [hv]
      _ = (2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.v : ZMod p) := by
        ring

lemma applyBranch_vLe_scaledInputCongruence_of_sub_halving
    (p x : Nat) (st : RoundState)
    (hsub : st.u <= st.v)
    (hhalf : 2 * ((st.v - st.u) / 2) = st.v - st.u)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (applyBranch Branch.vLe st) := by
  rcases hinv with ⟨hu, hv⟩
  constructor
  · change
      (((2 * st.rCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        -((2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.u : ZMod p))
    calc
      (((2 * st.rCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((2 : ZMod p) * st.rCoeff) * (x : ZMod p) := by
        simp [Nat.cast_mul]
      _ = (2 : ZMod p) * ((st.rCoeff : ZMod p) * x) := by
        ring
      _ = (2 : ZMod p) *
            (-((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p))) := by
        rw [hu]
      _ = -((2 : ZMod p) ^ (st.kaliskiSteps + 1) * (st.u : ZMod p)) := by
        ring
  · have hsubZ :
        ((st.v - st.u : Nat) : ZMod p) =
          (st.v : ZMod p) - (st.u : ZMod p) := by
      have hcancel : st.v - st.u + st.u = st.v := Nat.sub_add_cancel hsub
      apply add_right_cancel (b := (st.u : ZMod p))
      rw [sub_add_cancel]
      simpa [Nat.cast_add] using
        congrArg (fun value : Nat => (value : ZMod p)) hcancel
    have hhalfZ :
        ((st.v - st.u : Nat) : ZMod p) =
          (2 : ZMod p) * (((st.v - st.u) / 2 : Nat) : ZMod p) := by
      simpa [Nat.cast_mul] using
        congrArg (fun value : Nat => (value : ZMod p)) hhalf.symm
    change
      (((st.rCoeff + st.sCoeff : Nat) : ZMod p) * (x : ZMod p)) =
        (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
          (((st.v - st.u) / 2 : Nat) : ZMod p)
    calc
      (((st.rCoeff + st.sCoeff : Nat) : ZMod p) * (x : ZMod p))
          = ((st.rCoeff : ZMod p) + st.sCoeff) * (x : ZMod p) := by
        simp [Nat.cast_add]
      _ = (st.rCoeff : ZMod p) * x + (st.sCoeff : ZMod p) * x := by
        ring
      _ = -((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p)) +
            (2 : ZMod p) ^ st.kaliskiSteps * (st.v : ZMod p) := by
        rw [hu, hv]
      _ = (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
            (((st.v - st.u) / 2 : Nat) : ZMod p) := by
        have hpowHalf :
            (2 : ZMod p) ^ (st.kaliskiSteps + 1) *
                (((st.v - st.u) / 2 : Nat) : ZMod p) =
              (2 : ZMod p) ^ st.kaliskiSteps *
                ((st.v - st.u : Nat) : ZMod p) := by
          rw [pow_succ, hhalfZ]
          ring
        rw [hpowHalf, hsubZ]
        ring

/-- The stored `m_i` bit for the next fixed round.  Counter-mode rounds store a
distinguished zero bit; active rounds store the second bit of the RNSL17 branch
code [RNSL17, ECDLP.tex:468-475]. -/
def historyBit (st : RoundState) : Bool :=
  if st.active then
    if st.v = 0 then
      false
    else
      (selectBranch st).historyBit
  else
    false

/-- On a non-terminated active round, the `uEven` branch records history bit
zero. -/
lemma historyBit_active_nonzero_uEven (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 = 0) :
    historyBit st = false := by
  rw [historyBit]
  simp [hactive, hv0, selectBranch_uEven_of_even st hu, Branch.historyBit]

/-- On a non-terminated active round, the `vEven` branch records history bit
one. -/
lemma historyBit_active_nonzero_vEven (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 = 0) :
    historyBit st = true := by
  rw [historyBit]
  simp [hactive, hv0, selectBranch_vEven_of_u_odd_v_even st hu hv,
    Branch.historyBit]

/-- On a non-terminated active round, the `uGreater` branch records history
bit one. -/
lemma historyBit_active_nonzero_uGreater (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : st.v < st.u) :
    historyBit st = true := by
  rw [historyBit]
  simp [hactive, hv0, selectBranch_uGreater_of_odd_odd_lt st hu hv hlt,
    Branch.historyBit]

/-- On a non-terminated active round, the `vLe` branch records history bit
zero. -/
lemma historyBit_active_nonzero_vLe (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : ¬ st.v < st.u) :
    historyBit st = false := by
  rw [historyBit]
  simp [hactive, hv0, selectBranch_vLe_of_odd_odd_not_lt st hu hv hlt,
    Branch.historyBit]

/-- A terminating active round records history bit zero. -/
lemma historyBit_active_terminated (st : RoundState)
    (hactive : st.active = true) (hv : st.v = 0) :
    historyBit st = false := by
  simp [historyBit, hactive, hv]

/-- In padding/counter mode, the fixed-round history bit is zero. -/
lemma historyBit_inactive (st : RoundState)
    (hactive : st.active = false) :
    historyBit st = false := by
  simp [historyBit, hactive]

/-- One fixed Montgomery--Kaliski round.  Each round advances exactly one of
the two processes described in RNSL17: either an active Kaliski update, or the
post-termination padding counter [RNSL17, ECDLP.tex:425-475]. -/
def round (st : RoundState) : RoundState :=
  if st.active then
    if st.v = 0 then
      { st with active := false, paddingSteps := st.paddingSteps + 1 }
    else
      applyBranch (selectBranch st) st
  else
    { st with paddingSteps := st.paddingSteps + 1 }

/-- A non-terminated active fixed round is exactly the selected active branch
update. -/
lemma round_active_nonzero_eq_applyBranch_selectBranch (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0) :
    round st = applyBranch (selectBranch st) st := by
  simp [round, hactive, hv0]

/-- Source-round dispatch for the active non-terminated `uEven` case. -/
lemma round_active_nonzero_uEven (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 = 0) :
    round st = applyBranch Branch.uEven st := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  rw [selectBranch_uEven_of_even st hu]

/-- Source-round dispatch for the active non-terminated `vEven` case. -/
lemma round_active_nonzero_vEven (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 = 0) :
    round st = applyBranch Branch.vEven st := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  rw [selectBranch_vEven_of_u_odd_v_even st hu hv]

/-- Source-round dispatch for the active non-terminated `uGreater` case. -/
lemma round_active_nonzero_uGreater (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : st.v < st.u) :
    round st = applyBranch Branch.uGreater st := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  rw [selectBranch_uGreater_of_odd_odd_lt st hu hv hlt]

/-- Source-round dispatch for the active non-terminated `vLe` case. -/
lemma round_active_nonzero_vLe (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0)
    (hu : st.u % 2 ≠ 0) (hv : st.v % 2 ≠ 0) (hlt : ¬ st.v < st.u) :
    round st = applyBranch Branch.vLe st := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  rw [selectBranch_vLe_of_odd_odd_not_lt st hu hv hlt]

/-- Source-round dispatch for the active termination case. -/
lemma round_active_terminated (st : RoundState)
    (hactive : st.active = true) (hv : st.v = 0) :
    round st = { st with active := false, paddingSteps := st.paddingSteps + 1 } := by
  simp [round, hactive, hv]

/-- Source-round dispatch for inactive padding/counter mode. -/
lemma round_inactive (st : RoundState)
    (hactive : st.active = false) :
    round st = { st with paddingSteps := st.paddingSteps + 1 } := by
  simp [round, hactive]

lemma round_bezoutValue (st : RoundState) :
    bezoutValue (round st) = bezoutValue st := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simp [bezoutValue]
  · by_cases hv0 : st.v = 0
    · rw [round_active_terminated st hactive hv0]
      simp [bezoutValue]
    · by_cases hu : st.u % 2 = 0
      · rw [round_active_nonzero_uEven st hactive hv0 hu]
        exact applyBranch_uEven_bezoutValue_of_halving st
          (Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.u hu)
      · by_cases hv : st.v % 2 = 0
        · rw [round_active_nonzero_vEven st hactive hv0 hu hv]
          exact applyBranch_vEven_bezoutValue_of_halving st
            (Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.v hv)
        · by_cases hlt : st.v < st.u
          · have hsub : st.v <= st.u := Nat.le_of_lt hlt
            have hhalf :
                2 * ((st.u - st.v) / 2) = st.u - st.v :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.u - st.v)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hsub hu hv)
            rw [round_active_nonzero_uGreater st hactive hv0 hu hv hlt]
            exact applyBranch_uGreater_bezoutValue_of_sub_halving st hsub hhalf
          · have hsub : st.u <= st.v := Nat.le_of_not_gt hlt
            have hhalf :
                2 * ((st.v - st.u) / 2) = st.v - st.u :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.v - st.u)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hsub hv hu)
            rw [round_active_nonzero_vLe st hactive hv0 hu hv hlt]
            exact applyBranch_vLe_bezoutValue_of_sub_halving st hsub hhalf

lemma round_bezoutInvariant (p : Nat) (st : RoundState)
    (hinv : BezoutInvariant p st) :
    BezoutInvariant p (round st) := by
  rw [BezoutInvariant] at *
  rw [round_bezoutValue]
  exact hinv

lemma round_scaledInputCongruence (p x : Nat) (st : RoundState)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (round st) := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa [scaledInputCongruence, scaledUCongruence, scaledVCongruence] using hinv
  · by_cases hv0 : st.v = 0
    · rw [round_active_terminated st hactive hv0]
      simpa [scaledInputCongruence, scaledUCongruence, scaledVCongruence] using hinv
    · by_cases hu : st.u % 2 = 0
      · rw [round_active_nonzero_uEven st hactive hv0 hu]
        exact applyBranch_uEven_scaledInputCongruence_of_halving p x st
          (Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.u hu) hinv
      · by_cases hv : st.v % 2 = 0
        · rw [round_active_nonzero_vEven st hactive hv0 hu hv]
          exact applyBranch_vEven_scaledInputCongruence_of_halving p x st
            (Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.v hv) hinv
        · by_cases hlt : st.v < st.u
          · have hsub : st.v <= st.u := Nat.le_of_lt hlt
            have hhalf :
                2 * ((st.u - st.v) / 2) = st.u - st.v :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.u - st.v)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hsub hu hv)
            rw [round_active_nonzero_uGreater st hactive hv0 hu hv hlt]
            exact applyBranch_uGreater_scaledInputCongruence_of_sub_halving
              p x st hsub hhalf hinv
          · have hsub : st.u <= st.v := Nat.le_of_not_gt hlt
            have hhalf :
                2 * ((st.v - st.u) / 2) = st.v - st.u :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.v - st.u)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hsub hv hu)
            rw [round_active_nonzero_vLe st hactive hv0 hu hv hlt]
            exact applyBranch_vLe_scaledInputCongruence_of_sub_halving
              p x st hsub hhalf hinv

/-- An active branch update consumes one Kaliski update. -/
lemma applyBranch_kaliskiSteps (branch : Branch) (st : RoundState) :
    (applyBranch branch st).kaliskiSteps = st.kaliskiSteps + 1 := by
  cases branch <;> rfl

/-- An active branch update does not consume a padding/counter round. -/
lemma applyBranch_paddingSteps (branch : Branch) (st : RoundState) :
    (applyBranch branch st).paddingSteps = st.paddingSteps := by
  cases branch <;> rfl

/-- An active branch update preserves the source active flag. -/
lemma applyBranch_active (branch : Branch) (st : RoundState) :
    (applyBranch branch st).active = st.active := by
  cases branch <;> rfl

/-- A non-terminated active source round consumes one Kaliski update. -/
lemma round_active_nonzero_kaliskiSteps (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0) :
    (round st).kaliskiSteps = st.kaliskiSteps + 1 := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  exact applyBranch_kaliskiSteps (selectBranch st) st

/-- A non-terminated active source round leaves the padding/counter count
unchanged. -/
lemma round_active_nonzero_paddingSteps (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0) :
    (round st).paddingSteps = st.paddingSteps := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  exact applyBranch_paddingSteps (selectBranch st) st

/-- A non-terminated active source round stays in active mode. -/
lemma round_active_nonzero_active (st : RoundState)
    (hactive : st.active = true) (hv0 : st.v ≠ 0) :
    (round st).active = true := by
  rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv0]
  rw [applyBranch_active]
  exact hactive

/-- A terminating active source round does not consume another Kaliski update.
-/
lemma round_active_terminated_kaliskiSteps (st : RoundState)
    (hactive : st.active = true) (hv : st.v = 0) :
    (round st).kaliskiSteps = st.kaliskiSteps := by
  simpa using congrArg RoundState.kaliskiSteps
    (round_active_terminated st hactive hv)

/-- A terminating active source round consumes one padding/counter round. -/
lemma round_active_terminated_paddingSteps (st : RoundState)
    (hactive : st.active = true) (hv : st.v = 0) :
    (round st).paddingSteps = st.paddingSteps + 1 := by
  simpa using congrArg RoundState.paddingSteps
    (round_active_terminated st hactive hv)

/-- A terminating active source round turns off active mode. -/
lemma round_active_terminated_active (st : RoundState)
    (hactive : st.active = true) (hv : st.v = 0) :
    (round st).active = false := by
  simpa using congrArg RoundState.active
    (round_active_terminated st hactive hv)

/-- An inactive source round does not consume a Kaliski update. -/
lemma round_inactive_kaliskiSteps (st : RoundState)
    (hactive : st.active = false) :
    (round st).kaliskiSteps = st.kaliskiSteps := by
  simpa using congrArg RoundState.kaliskiSteps
    (round_inactive st hactive)

/-- An inactive source round consumes one padding/counter round. -/
lemma round_inactive_paddingSteps (st : RoundState)
    (hactive : st.active = false) :
    (round st).paddingSteps = st.paddingSteps + 1 := by
  simpa using congrArg RoundState.paddingSteps
    (round_inactive st hactive)

/-- An inactive source round remains in inactive padding/counter mode. -/
lemma round_inactive_active (st : RoundState)
    (hactive : st.active = false) :
    (round st).active = false := by
  rw [round_inactive st hactive]
  exact hactive

lemma applyBranch_totalRounds (branch : Branch) (st : RoundState) :
    totalRounds (applyBranch branch st) = totalRounds st + 1 := by
  cases branch <;>
    simp [applyBranch, totalRounds, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma round_totalRounds (st : RoundState) :
    totalRounds (round st) = totalRounds st + 1 := by
  cases hactive : st.active
  · simp [round, hactive, totalRounds, Nat.add_assoc]
  · by_cases hv : st.v = 0
    · simp [round, hactive, hv, totalRounds, Nat.add_assoc]
    · simp [round, hactive, hv, applyBranch_totalRounds]

/-- Source-level mode/counter invariant: the Kaliski mode flag is set exactly
when no padding/counter round has yet been consumed. -/
def activeCounterInvariant (st : RoundState) : Prop :=
  st.active = decide (st.paddingSteps = 0)

lemma initial_activeCounterInvariant (p x : Nat) :
    activeCounterInvariant (initial p x) := by
  simp [activeCounterInvariant, initial]

/-- One fixed source round preserves the mode/counter invariant. -/
lemma round_activeCounterInvariant (st : RoundState)
    (hinv : activeCounterInvariant st) :
    activeCounterInvariant (round st) := by
  rw [activeCounterInvariant] at hinv ⊢
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simp [hactive]
  · by_cases hv : st.v = 0
    · rw [round_active_terminated st hactive hv]
      simp
    · rw [round_active_nonzero_eq_applyBranch_selectBranch st hactive hv]
      rw [applyBranch_active, applyBranch_paddingSteps]
      simp [hactive] at hinv
      simp [hactive, hinv]

/-- Run a fixed number of Montgomery--Kaliski rounds. -/
def runRounds : Nat -> RoundState -> RoundState
  | 0, st => st
  | m + 1, st => runRounds m (round st)

lemma runRounds_bezoutValue (m : Nat) (st : RoundState) :
    bezoutValue (runRounds m st) = bezoutValue st := by
  induction m generalizing st with
  | zero =>
      rfl
  | succ m ih =>
      calc
        bezoutValue (runRounds (m + 1) st)
            = bezoutValue (runRounds m (round st)) := rfl
        _ = bezoutValue (round st) := ih (round st)
        _ = bezoutValue st := round_bezoutValue st

lemma runRounds_bezoutInvariant (m p : Nat) (st : RoundState)
    (hinv : BezoutInvariant p st) :
    BezoutInvariant p (runRounds m st) := by
  rw [BezoutInvariant] at *
  rw [runRounds_bezoutValue]
  exact hinv

lemma runRounds_scaledInputCongruence (m p x : Nat) (st : RoundState)
    (hinv : scaledInputCongruence p x st) :
    scaledInputCongruence p x (runRounds m st) := by
  induction m generalizing st with
  | zero =>
      exact hinv
  | succ m ih =>
      exact ih (round st) (round_scaledInputCongruence p x st hinv)

lemma runRounds_totalRounds (m : Nat) (st : RoundState) :
    totalRounds (runRounds m st) = totalRounds st + m := by
  induction m generalizing st with
  | zero =>
      rfl
  | succ m ih =>
      calc
        totalRounds (runRounds (m + 1) st)
            = totalRounds (runRounds m (round st)) := rfl
        _ = totalRounds (round st) + m := ih (round st)
        _ = totalRounds st + (m + 1) := by
          rw [round_totalRounds]
          omega

/-- Fixed source iteration preserves the mode/counter invariant. -/
lemma runRounds_activeCounterInvariant (rounds : Nat) (st : RoundState)
    (hinv : activeCounterInvariant st) :
    activeCounterInvariant (runRounds rounds st) := by
  induction rounds generalizing st with
  | zero =>
      exact hinv
  | succ rounds ih =>
      exact ih (round st) (round_activeCounterInvariant st hinv)

/-- Starting from the source initial state, active Kaliski mode is equivalent
to a zero padding/counter value after any fixed-round prefix. -/
lemma runRounds_initial_active_iff_paddingSteps_eq_zero
    (rounds p x : Nat) :
    (runRounds rounds (initial p x)).active = true ↔
      (runRounds rounds (initial p x)).paddingSteps = 0 := by
  have hinv := runRounds_activeCounterInvariant rounds (initial p x)
    (initial_activeCounterInvariant p x)
  rw [activeCounterInvariant] at hinv
  rw [hinv]
  simp

/-- One fixed round never decreases the number of active Kaliski updates. -/
lemma kaliskiSteps_le_round (st : RoundState) :
    st.kaliskiSteps <= (round st).kaliskiSteps := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
  · by_cases hv : st.v = 0
    · rw [round_active_terminated st hactive hv]
    · rw [round_active_nonzero_kaliskiSteps st hactive hv]
      omega

/-- Running any fixed suffix never decreases the number of active Kaliski
updates already executed. -/
lemma kaliskiSteps_le_runRounds (m : Nat) (st : RoundState) :
    st.kaliskiSteps <= (runRounds m st).kaliskiSteps := by
  induction m generalizing st with
  | zero =>
      exact Nat.le_refl _
  | succ m ih =>
      exact (kaliskiSteps_le_round st).trans (ih (round st))

/-- A positive source prefix with positive input has executed at least one
Kaliski update: its first round cannot be a padding/counter round. -/
lemma runRounds_kaliskiSteps_pos_of_pos
    (rounds p x : Nat) (hrounds : 0 < rounds) (hx : 0 < x) :
    0 < (runRounds rounds (initial p x)).kaliskiSteps := by
  have hfirst :
      (round (initial p x)).kaliskiSteps = 1 := by
    simpa [initial] using
      round_active_nonzero_kaliskiSteps (initial p x) rfl (Nat.ne_of_gt hx)
  rw [show rounds = (rounds - 1) + 1 by omega]
  change 0 <
    (runRounds (rounds - 1) (round (initial p x))).kaliskiSteps
  have hmono :=
    kaliskiSteps_le_runRounds (rounds - 1) (round (initial p x))
  omega

/-- For a positive modulus width and positive input, every strict source
prefix has a padding/counter successor that fits in the logarithmic counter.
This is the source-level no-wrap bound for the compact MK handoff. -/
lemma runRounds_paddingSteps_succ_lt_pow_clog
    (n p x rounds : Nat) (hn : 0 < n) (hx : 0 < x)
    (hrounds : rounds < 2 * n) :
    (runRounds rounds (initial p x)).paddingSteps + 1 <
      2 ^ Nat.clog 2 (2 * n) := by
  have hcapacity : 2 * n ≤ 2 ^ Nat.clog 2 (2 * n) :=
    Nat.le_pow_clog (by omega : 1 < (2 : Nat)) (2 * n)
  by_cases hzero : rounds = 0
  · subst rounds
    change 1 < 2 ^ Nat.clog 2 (2 * n)
    have htwo : 1 < 2 * n := by omega
    exact htwo.trans_le hcapacity
  · have hroundsPos : 0 < rounds := Nat.pos_of_ne_zero hzero
    have hkaliski :
        0 < (runRounds rounds (initial p x)).kaliskiSteps :=
      runRounds_kaliskiSteps_pos_of_pos rounds p x hroundsPos hx
    have htotal :
        (runRounds rounds (initial p x)).kaliskiSteps +
            (runRounds rounds (initial p x)).paddingSteps = rounds := by
      simpa [totalRounds, initial] using
        runRounds_totalRounds rounds (initial p x)
    omega

/-- Successor form of the fixed-round source iteration.  This direction
matches the folded circuit-prefix induction: a one-step extension rounds the
current prefix state. -/
lemma runRounds_succ_eq_round_runRounds (m : Nat) (st : RoundState) :
    runRounds (m + 1) st = round (runRounds m st) := by
  induction m generalizing st with
  | zero =>
      rfl
  | succ m ih =>
      change runRounds (m + 1) (round st) =
        round (runRounds (m + 1) st)
      rw [ih (round st)]
      rfl

/-- Branch-history bits generated by a fixed number of rounds. -/
def historyBits : Nat -> RoundState -> List Bool
  | 0, _ => []
  | m + 1, st => historyBit st :: historyBits m (round st)

@[simp] lemma historyBits_length (m : Nat) (st : RoundState) :
    (historyBits m st).length = m := by
  induction m generalizing st with
  | zero =>
      rfl
  | succ m ih =>
      simp [historyBits, ih]

/-- Read the branch-history slot for the `i`-th round of an `m`-round source
trace.  This form keeps the schedule index explicit for a future concrete
fixed-round fold entrypoint. -/
def historyBitsAt : (m : Nat) -> RoundState -> Fin m -> Bool
  | _ + 1, st, ⟨0, _⟩ => historyBit st
  | m + 1, st, ⟨i + 1, _⟩ =>
      historyBitsAt m (round st) ⟨i, by omega⟩

/-- The `i`-th branch-history slot is the source history bit of the prefix state
after `i` rounds. -/
lemma historyBitsAt_eq_historyBit_runRounds :
    ∀ (m : Nat) (st : RoundState) (i : Fin m),
      historyBitsAt m st i = historyBit (runRounds i.val st)
  | 0, _, i => by exact Fin.elim0 i
  | _ + 1, st, ⟨0, _⟩ => by rfl
  | m + 1, st, ⟨i + 1, _⟩ => by
      simpa [historyBitsAt, runRounds] using
        historyBitsAt_eq_historyBit_runRounds
          m (round st) ⟨i, by omega⟩

/-- The indexed branch-history readout agrees with the materialized history
list. -/
lemma historyBitsAt_eq_get :
    ∀ (m : Nat) (st : RoundState) (i : Fin m),
      historyBitsAt m st i =
        (historyBits m st).get ⟨i.val, by simp [i.isLt]⟩
  | 0, _, i => by exact Fin.elim0 i
  | _ + 1, st, ⟨0, _⟩ => by rfl
  | m + 1, st, ⟨i + 1, _⟩ => by
      simpa [historyBitsAt, historyBits] using
        historyBitsAt_eq_get m (round st) ⟨i, by omega⟩

/-- The materialized source history list is exactly the finite table of
indexed source history readouts. -/
lemma historyBits_eq_ofFn_historyBitsAt :
    ∀ (m : Nat) (st : RoundState),
      historyBits m st =
        List.ofFn (fun roundIndex : Fin m => historyBitsAt m st roundIndex)
  | 0, _ => by
      simp [historyBits]
  | m + 1, st => by
      rw [List.ofFn_succ]
      change
        historyBit st :: historyBits m (round st) =
          historyBit st ::
            List.ofFn
              (fun i : Fin m => historyBitsAt (m + 1) st i.succ)
      rw [historyBits_eq_ofFn_historyBitsAt m (round st)]
      exact
        congrArg (List.cons (historyBit st))
          (congrArg List.ofFn (funext fun roundIndex => rfl))

private def rCoeffReachabilityInvariant (p : Nat) (st : RoundState) : Prop :=
  BezoutInvariant p st ∧
    0 < st.u ∧
    0 < st.sCoeff ∧
    (st.v = 0 → st.rCoeff < 2 * p)

private lemma rCoeff_lt_modulus_of_reachabilityInvariant
    (p : Nat) (st : RoundState)
    (hinv : rCoeffReachabilityInvariant p st) (hv : st.v ≠ 0) :
    st.rCoeff < p := by
  rcases hinv with ⟨hbezout, hu, hs, _hterminated⟩
  rw [BezoutInvariant, bezoutValue] at hbezout
  have hvPos : 0 < st.v := Nat.pos_of_ne_zero hv
  have hrLeMul : st.rCoeff ≤ st.rCoeff * st.v := by
    calc
      st.rCoeff = st.rCoeff * 1 := by rw [Nat.mul_one]
      _ ≤ st.rCoeff * st.v :=
        Nat.mul_le_mul_left st.rCoeff (Nat.succ_le_of_lt hvPos)
  have hsuPos : 0 < st.sCoeff * st.u := Nat.mul_pos hs hu
  omega

private lemma initial_rCoeffReachabilityInvariant
    (p x : Nat) (hp : 0 < p) :
    rCoeffReachabilityInvariant p (initial p x) := by
  rw [rCoeffReachabilityInvariant]
  refine ⟨initial_bezoutInvariant p x, hp, by simp [initial], ?_⟩
  intro _hv
  change 0 < 2 * p
  omega

private lemma round_rCoeffReachabilityInvariant
    (p : Nat) (st : RoundState)
    (hinv : rCoeffReachabilityInvariant p st) :
    rCoeffReachabilityInvariant p (round st) := by
  cases hactive : st.active
  · rw [round_inactive st hactive]
    simpa [rCoeffReachabilityInvariant, BezoutInvariant, bezoutValue] using hinv
  · by_cases hv0 : st.v = 0
    · rw [round_active_terminated st hactive hv0]
      simpa [rCoeffReachabilityInvariant, BezoutInvariant, bezoutValue] using hinv
    · rcases hinv with ⟨hbezout, huPos, hsPos, hterminated⟩
      have hinv' : rCoeffReachabilityInvariant p st :=
        ⟨hbezout, huPos, hsPos, hterminated⟩
      have hrLt : st.rCoeff < p :=
        rCoeff_lt_modulus_of_reachabilityInvariant p st hinv' hv0
      have hbezoutRound : BezoutInvariant p (round st) :=
        round_bezoutInvariant p st hbezout
      by_cases hu : st.u % 2 = 0
      · have hhalf : 2 * (st.u / 2) = st.u :=
          Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero st.u hu
        rw [round_active_nonzero_uEven st hactive hv0 hu] at hbezoutRound ⊢
        rw [rCoeffReachabilityInvariant]
        refine ⟨hbezoutRound, ?_, ?_, ?_⟩
        · change 0 < st.u / 2
          omega
        · change 0 < 2 * st.sCoeff
          omega
        · intro hv
          change st.v = 0 at hv
          exact (hv0 hv).elim
      · by_cases hv : st.v % 2 = 0
        · rw [round_active_nonzero_vEven st hactive hv0 hu hv] at hbezoutRound ⊢
          rw [rCoeffReachabilityInvariant]
          refine ⟨hbezoutRound, huPos, hsPos, ?_⟩
          intro _hv
          change 2 * st.rCoeff < 2 * p
          omega
        · by_cases hlt : st.v < st.u
          · have hsub : st.v ≤ st.u := Nat.le_of_lt hlt
            have hhalf : 2 * ((st.u - st.v) / 2) = st.u - st.v :=
              Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero (st.u - st.v)
                (Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hsub hu hv)
            rw [round_active_nonzero_uGreater st hactive hv0 hu hv hlt] at hbezoutRound ⊢
            rw [rCoeffReachabilityInvariant]
            refine ⟨hbezoutRound, ?_, ?_, ?_⟩
            · change 0 < (st.u - st.v) / 2
              omega
            · change 0 < 2 * st.sCoeff
              omega
            · intro hvZero
              change st.v = 0 at hvZero
              exact (hv0 hvZero).elim
          · rw [round_active_nonzero_vLe st hactive hv0 hu hv hlt] at hbezoutRound ⊢
            rw [rCoeffReachabilityInvariant]
            refine ⟨hbezoutRound, huPos, ?_, ?_⟩
            · change 0 < st.rCoeff + st.sCoeff
              omega
            · intro _hvZero
              change 2 * st.rCoeff < 2 * p
              omega

private lemma runRounds_rCoeffReachabilityInvariant
    (rounds p : Nat) (st : RoundState)
    (hinv : rCoeffReachabilityInvariant p st) :
    rCoeffReachabilityInvariant p (runRounds rounds st) := by
  induction rounds generalizing st with
  | zero =>
      exact hinv
  | succ rounds ih =>
      exact ih (round st) (round_rCoeffReachabilityInvariant p st hinv)

/-- Final integer state after the source-selected `2n` fixed rounds. -/
def fixedRoundState (n p x : Nat) : RoundState :=
  runRounds (fixedRoundCount n) (initial p x)

/-- The reachable fixed-round Kaliski coefficient occupies less than twice the
modulus, including the terminal round where `v` first becomes zero. -/
lemma fixedRoundState_rCoeff_lt_two_mul_modulus
    (n p x : Nat) (hp : 0 < p) :
    (fixedRoundState n p x).rCoeff < 2 * p := by
  have hinv :
      rCoeffReachabilityInvariant p (fixedRoundState n p x) :=
    runRounds_rCoeffReachabilityInvariant
      (fixedRoundCount n) p (initial p x)
      (initial_rCoeffReachabilityInvariant p x hp)
  by_cases hv : (fixedRoundState n p x).v = 0
  · exact hinv.2.2.2 hv
  · have hrLt : (fixedRoundState n p x).rCoeff < p :=
      rCoeff_lt_modulus_of_reachabilityInvariant
        p (fixedRoundState n p x) hinv hv
    omega

lemma fixedRoundState_bezoutInvariant (n p x : Nat) :
    BezoutInvariant p (fixedRoundState n p x) :=
  runRounds_bezoutInvariant (fixedRoundCount n) p
    (initial p x) (initial_bezoutInvariant p x)

lemma fixedRoundState_scaledInputCongruence (n p x : Nat) :
    scaledInputCongruence p x (fixedRoundState n p x) :=
  runRounds_scaledInputCongruence (fixedRoundCount n) p x
    (initial p x) (initial_scaledInputCongruence p x)

lemma bezoutInvariant_zmod_eq_zero (p : Nat) (st : RoundState)
    (hinv : BezoutInvariant p st) :
    (st.rCoeff : ZMod p) * (st.v : ZMod p) +
        (st.sCoeff : ZMod p) * (st.u : ZMod p) = 0 := by
  have hcast :
      ((bezoutValue st : Nat) : ZMod p) = (p : ZMod p) :=
    congrArg (fun value : Nat => (value : ZMod p)) hinv
  simpa [bezoutValue, Nat.cast_add, Nat.cast_mul] using hcast

lemma fixedRoundState_bezoutInvariant_zmod_eq_zero (n p x : Nat) :
    ((fixedRoundState n p x).rCoeff : ZMod p) *
          ((fixedRoundState n p x).v : ZMod p) +
        ((fixedRoundState n p x).sCoeff : ZMod p) *
          ((fixedRoundState n p x).u : ZMod p) = 0 :=
  bezoutInvariant_zmod_eq_zero p (fixedRoundState n p x)
    (fixedRoundState_bezoutInvariant n p x)

/-- The `m_i` branch-history register family produced by the source-selected
`2n` fixed rounds. -/
def fixedRoundHistory (n p x : Nat) : List Bool :=
  historyBits (fixedRoundCount n) (initial p x)

lemma fixedRoundState_totalRounds (n p x : Nat) :
    totalRounds (fixedRoundState n p x) = 2 * n := by
  calc
    totalRounds (fixedRoundState n p x)
        = totalRounds (initial p x) + fixedRoundCount n := by
          simp [fixedRoundState, runRounds_totalRounds]
    _ = 2 * n := by
      simp

/-- A positive input consumes at least one active Kaliski update in every
positive-width fixed schedule. -/
lemma fixedRoundState_kaliskiSteps_pos
    (n p x : Nat) (hn : 0 < n) (hx : 0 < x) :
    0 < (fixedRoundState n p x).kaliskiSteps := by
  have hcount : 0 < fixedRoundCount n := by
    simp [fixedRoundCount]
    omega
  have hfirst :
      (round (initial p x)).kaliskiSteps = 1 := by
    simpa [initial] using
      round_active_nonzero_kaliskiSteps (initial p x) rfl (Nat.ne_of_gt hx)
  rw [fixedRoundState, show fixedRoundCount n =
      (fixedRoundCount n - 1) + 1 by omega]
  change 0 <
    (runRounds (fixedRoundCount n - 1) (round (initial p x))).kaliskiSteps
  have hmono :=
    kaliskiSteps_le_runRounds (fixedRoundCount n - 1) (round (initial p x))
  omega

/-- For a positive input, the `2n-k` correction count is strictly below the
full `2n` schedule length.  This is the exact no-wrap fact needed by the
logarithmic padding counter. -/
lemma fixedRoundState_paddingSteps_lt_two_mul
    (n p x : Nat) (hn : 0 < n) (hx : 0 < x) :
    (fixedRoundState n p x).paddingSteps < 2 * n := by
  have htotal := fixedRoundState_totalRounds n p x
  have hk := fixedRoundState_kaliskiSteps_pos n p x hn hx
  unfold totalRounds at htotal
  omega

lemma fixedRoundHistory_length (n p x : Nat) :
    (fixedRoundHistory n p x).length = 2 * n := by
  simp [fixedRoundHistory]


/-- Source branch-history bit selected by a fixed-round schedule index. -/
def fixedRoundHistoryAt (n p x : Nat)
    (roundIndex : Fin (fixedRoundCount n)) : Bool :=
  historyBitsAt (fixedRoundCount n) (initial p x) roundIndex

/-- Fixed-round indexed history readout agrees with the source prefix state
after the same number of rounds. -/
lemma fixedRoundHistoryAt_eq_historyBit_prefix (n p x : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    fixedRoundHistoryAt n p x roundIndex =
      historyBit (runRounds roundIndex.val (initial p x)) := by
  simpa [fixedRoundHistoryAt] using
    historyBitsAt_eq_historyBit_runRounds
      (fixedRoundCount n) (initial p x) roundIndex

/-- Fixed-round indexed history readout agrees with the materialized `m_i`
history list. -/
lemma fixedRoundHistoryAt_eq_get (n p x : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    fixedRoundHistoryAt n p x roundIndex =
      (fixedRoundHistory n p x).get
        ⟨roundIndex.val, by
          rw [fixedRoundHistory_length]
          exact roundIndex.isLt⟩ := by
  simpa [fixedRoundHistoryAt, fixedRoundHistory] using
    historyBitsAt_eq_get
      (fixedRoundCount n) (initial p x) roundIndex

/-- Counter value used to correct the copied almost-inverse.  In the fixed
`2n` schedule this is the number of padding/counter rounds, i.e. the `2n-k`
doubling count from the parallel pseudo-inverse correction route [HJN+20,
modular-arithmetic.tex:141-144]. -/
def correctionRounds (st : RoundState) : Nat :=
  st.paddingSteps

lemma correctionRounds_eq_paddingSteps (st : RoundState) :
    correctionRounds st = st.paddingSteps :=
  rfl

/-- For a completed `2n` fixed-round state, the correction counter is the source
`2n-k` value. -/
lemma correctionRounds_eq_two_mul_sub_kaliskiSteps_of_totalRounds
    (n : Nat) (st : RoundState) (hrounds : totalRounds st = 2 * n) :
    correctionRounds st = 2 * n - st.kaliskiSteps := by
  simp [correctionRounds, totalRounds] at *
  omega

lemma fixedRoundState_correctionRounds_eq_two_mul_sub_kaliskiSteps
    (n p x : Nat) :
    correctionRounds (fixedRoundState n p x) =
      2 * n - (fixedRoundState n p x).kaliskiSteps :=
  correctionRounds_eq_two_mul_sub_kaliskiSteps_of_totalRounds n
    (fixedRoundState n p x) (fixedRoundState_totalRounds n p x)

/-- Candidate residue slot read from `r`.  For an arbitrary source state this is
only the raw coefficient residue; when the state is the fixed-round endpoint,
the later arithmetic invariant identifies it with the almost-inverse from the
source route [RNSL17, ECDLP.tex:399-412; HJN+20,
modular-arithmetic.tex:141-144]. -/
def pseudoInverseResidue (p : Nat) (st : RoundState) : ZMod p :=
  st.rCoeff

/-- Multiplicative factor contributed by `rounds` modular doublings. -/
def correctionFactor (p rounds : Nat) : ZMod p :=
  (2 : ZMod p) ^ rounds

@[simp] lemma correctionFactor_zero (p : Nat) :
    correctionFactor p 0 = 1 := by
  simp [correctionFactor]

lemma correctionFactor_succ (p rounds : Nat) :
    correctionFactor p (rounds + 1) =
      (2 : ZMod p) * correctionFactor p rounds := by
  simp [correctionFactor, pow_succ, mul_comm]

/-- Corrected residue expression after applying the fixed-round correction
doublings to the copied residue slot.  The full number-theoretic bridge to the
staged `inverseResidue` endpoint is proved by the next arithmetic layer; this
definition fixes the trace-side expression. -/
def correctedInverseResidue (p : Nat) (st : RoundState) : ZMod p :=
  correctionFactor p (correctionRounds st) * pseudoInverseResidue p st

lemma correctedInverseResidue_eq_pow_mul (p : Nat) (st : RoundState) :
    correctedInverseResidue p st =
      (2 : ZMod p) ^ correctionRounds st * (st.rCoeff : ZMod p) :=
  rfl

/-- Sign-adjusted corrected residue.  The Kaliski coefficient invariant carries
one source-level minus sign, so this is the residue whose product with the
input has the positive Montgomery scale [RNSL17, ECDLP.tex:399-412]. -/
def signedCorrectedInverseResidue (p : Nat) (st : RoundState) : ZMod p :=
  -correctedInverseResidue p st

lemma signedCorrectedInverseResidue_eq_neg (p : Nat) (st : RoundState) :
    signedCorrectedInverseResidue p st = -correctedInverseResidue p st :=
  rfl

/-- The scaled Kaliski coefficient congruence identifies the corrected residue
times the input with the fixed Montgomery scaling factor when the fixed trace
has terminated at `u = 1` [RNSL17, ECDLP.tex:399-412,442-475; HJN+20,
modular-arithmetic.tex:141-144]. -/
lemma correctedInverseResidue_mul_input_eq_neg_pow_of_scaled
    (p x n : Nat) (st : RoundState)
    (hinv : scaledInputCongruence p x st)
    (hrounds : correctionRounds st + st.kaliskiSteps = 2 * n)
    (hfinish : st.u = 1) :
    correctedInverseResidue p st * (x : ZMod p) =
      -((2 : ZMod p) ^ (2 * n)) := by
  rcases hinv with ⟨hu, _hv⟩
  calc
    correctedInverseResidue p st * (x : ZMod p)
        = ((2 : ZMod p) ^ correctionRounds st * (st.rCoeff : ZMod p)) *
            (x : ZMod p) := by
      rfl
    _ = (2 : ZMod p) ^ correctionRounds st *
          ((st.rCoeff : ZMod p) * (x : ZMod p)) := by
      ring
    _ = (2 : ZMod p) ^ correctionRounds st *
          (-((2 : ZMod p) ^ st.kaliskiSteps * (st.u : ZMod p))) := by
      rw [hu]
    _ = -((2 : ZMod p) ^ (correctionRounds st + st.kaliskiSteps) *
          (st.u : ZMod p)) := by
      rw [pow_add]
      ring
    _ = -((2 : ZMod p) ^ (2 * n) * (st.u : ZMod p)) := by
      rw [hrounds]
    _ = -((2 : ZMod p) ^ (2 * n)) := by
      rw [hfinish]
      ring

/-- After making the source sign explicit, the corrected residue has the
positive Montgomery scale `2^(2n)` at a terminating fixed-round endpoint. -/
lemma signedCorrectedInverseResidue_mul_input_eq_pow_of_scaled
    (p x n : Nat) (st : RoundState)
    (hinv : scaledInputCongruence p x st)
    (hrounds : correctionRounds st + st.kaliskiSteps = 2 * n)
    (hfinish : st.u = 1) :
    signedCorrectedInverseResidue p st * (x : ZMod p) =
      (2 : ZMod p) ^ (2 * n) := by
  calc
    signedCorrectedInverseResidue p st * (x : ZMod p) =
        -(correctedInverseResidue p st * (x : ZMod p)) := by
      rw [signedCorrectedInverseResidue]
      ring
    _ = -(-((2 : ZMod p) ^ (2 * n))) := by
      rw [correctedInverseResidue_mul_input_eq_neg_pow_of_scaled
        p x n st hinv hrounds hfinish]
    _ = (2 : ZMod p) ^ (2 * n) := by
      ring

end RoundState

end NumberTheory.BinaryGCD
end QuantumAlg

end

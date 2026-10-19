/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.FinPow
import all QuantumAlg.Algorithms.AmplitudeEstimation.PhaseWorkspace
import all QuantumAlg.Algorithms.QPE.Construction

/-!
# Minimal actual layout for elementary amplitude estimation

The original phase wires remain first and the source wires remain last. An
extra work position is inserted between them only for the total-definition
case with one phase wire and at least three source wires. Every admitted
precision/confidence input has at least two original phase wires, so this
extra position is absent throughout the original scientific domain.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- Extra physical work is needed only when the total definition has one phase wire. -/
@[expose] public def helperWidth (t n : Nat) : Nat :=
  if t = 1 ∧ 3 ≤ n then 1 else 0

/-- The original phase prefix followed by any explicitly allocated work position. -/
@[implicit_reducible, expose] public def phaseWidth (t n : Nat) : Nat := t + helperWidth t n

/-- Every phase, selected work and original source system is part of the actual register. -/
@[implicit_reducible, expose] public def totalQubits (t n : Nat) : Nat := phaseWidth t n + n

lemma helperWidth_eq_zero_of_two_le {t n : Nat} (wide : 2 ≤ t) : helperWidth t n = 0 := by
  unfold helperWidth
  rw [if_neg (by omega)]

lemma helperWidth_eq_zero_of_small {t n : Nat} (small : n ≤ 2) : helperWidth t n = 0 := by
  unfold helperWidth
  rw [if_neg (by omega)]

/-- The original admitted parameter domain never allocates an additional system. -/
lemma selected_helperWidth_eq_zero {eps η : Real} (n : Nat)
    (heps : 0 < eps) (heps_le : eps ≤ 1) (heta : 0 < η) (heta_le : η ≤ 1) :
    helperWidth (selectedPhaseQubits eps η) n = 0 :=
  helperWidth_eq_zero_of_two_le (selectedPhaseQubits_atLeastTwo heps heps_le heta heta_le)

/-- The power stage controls precisely its original physical phase position. -/
def controlWire {t : Nat} (n : Nat) (stage : Fin t) : Fin (phaseWidth t n) :=
  Fin.castAdd (helperWidth t n) (PhaseWorkspace.controlWire stage)

lemma controlWire_val {t : Nat} (n : Nat) (stage : Fin t) :
    (controlWire n stage).val = stage.rev.val := rfl

/-- Even the exceptional one-phase total-definition branch has one distinct work position. -/
lemma phaseWidth_atLeastTwo {t : Nat} (n : Nat) (stage : Fin t) (large : 3 ≤ n) :
    2 ≤ phaseWidth t n := by
  have positive := stage.isLt
  unfold phaseWidth helperWidth
  split <;> omega

/-- Select an actual phase-or-work position distinct from the original stage control. -/
def workWire {t : Nat} (n : Nat) (stage : Fin t) (large : 3 ≤ n) : Fin (phaseWidth t n) :=
  if (controlWire n stage).val = 0 then
    ⟨1, by have wide := phaseWidth_atLeastTwo n stage large; omega⟩
  else ⟨0, by have wide := phaseWidth_atLeastTwo n stage large; omega⟩

lemma controlWire_ne_workWire {t : Nat} (n : Nat) (stage : Fin t) (large : 3 ≤ n) :
    controlWire n stage ≠ workWire n stage large := by
  intro same
  have values := congrArg (fun wire : Fin (phaseWidth t n) => wire.val) same
  by_cases first : (controlWire n stage).val = 0
  · simp only [workWire, first, if_true] at values
    omega
  · simp only [workWire, first, if_false] at values

/-- The extended power-stage label names the same physical control, not a new phase bit. -/
def extendedStage {t : Nat} (n : Nat) (stage : Fin t) : Fin (phaseWidth t n) :=
  ⟨stage.val + helperWidth t n, by change _ < t + helperWidth t n; omega⟩

lemma extendedStage_prefix {t : Nat} (n : Nat) (stage : Fin t) :
    (extendedStage n stage).rev.val = stage.rev.val := by
  dsimp only [extendedStage, Fin.rev, phaseWidth]
  omega

/-- Reassociate the actual coordinates as original phase/source values and the selected work.
This changes only the basis description and preserves each of those values explicitly. -/
def originalAndWorkEquiv (t n : Nat) :
    Fin (2 ^ totalQubits t n) ≃ Fin (2 ^ (t + n)) × Fin (2 ^ helperWidth t n) :=
  (prodEquiv (m := phaseWidth t n) (n := n)).symm |>.trans
    (Equiv.prodCongr (prodEquiv (m := t) (n := helperWidth t n)).symm (Equiv.refl _)) |>.trans
    (Equiv.prodAssoc (Fin (2 ^ t)) (Fin (2 ^ helperWidth t n)) (Fin (2 ^ n))) |>.trans
    (Equiv.prodCongr (Equiv.refl _)
      (Equiv.prodComm (Fin (2 ^ helperWidth t n)) (Fin (2 ^ n)))) |>.trans
    (Equiv.prodAssoc (Fin (2 ^ t)) (Fin (2 ^ n)) (Fin (2 ^ helperWidth t n))).symm |>.trans
    (Equiv.prodCongr (prodEquiv (m := t) (n := n)) (Equiv.refl _))

lemma originalAndWorkEquiv_apply (t n : Nat) (phase : Fin (2 ^ t))
    (work : Fin (2 ^ helperWidth t n)) (source : Fin (2 ^ n)) :
    originalAndWorkEquiv t n (prodEquiv (prodEquiv (phase, work), source)) =
      (prodEquiv (phase, source), work) := by
  simp [originalAndWorkEquiv]

end

end QuantumAlg.AmplitudeEstimation.Elementary

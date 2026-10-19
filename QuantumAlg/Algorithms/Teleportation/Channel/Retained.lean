/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Teleportation.Channel
import all QuantumAlg.Core.Measure.Kraus

/-!
# Retaining Alice's measured quantum systems

The computational-basis projection keeps Alice's two measured systems in
its actual measured basis state. Bob's correction commutes through this
basis insertion, and the corrected unknown input is transferred with the
source's exact branch scalar [dW19, qcnotes.tex:792,802,804]. The rectangular
matrix identities hold for every input column, including arbitrary joint
inputs with an external reference [dW19, qcnotes.tex:809].
-/

namespace QuantumAlg.QuantumTeleportation.RetainedAlice

noncomputable section

open MeasurementInstrument

private lemma controlled_conjTranspose {B T : Type} [DecidableEq B]
    (operators : B → Matrix T T ℂ) :
    (controlled operators).conjTranspose =
      controlled (fun label => (operators label).conjTranspose) := by
  ext ⟨left, row⟩ ⟨right, column⟩
  by_cases same : left = right
  · subst right
    simp [controlled, Matrix.conjTranspose_apply]
  · simp [controlled, Matrix.conjTranspose_apply, same, Ne.symm same]

/-- Correction on Bob can be pulled through reinsertion of Alice's retained basis systems. -/
lemma controlled_insert {B T : Type} [Fintype B] [Fintype T]
    [DecidableEq B] [DecidableEq T] (label : B) (operator : Matrix T T ℂ) :
    controlled (fun _ : B => operator) * (selectHead (T := T) label).conjTranspose =
      (selectHead (T := T) label).conjTranspose * operator := by
  have exactBranch := congrArg Matrix.conjTranspose
    (selectHead_controlled label (fun _ : B => operator.conjTranspose))
  simpa only [Matrix.conjTranspose_mul, controlled_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using exactBranch

/-- Full branch output equals the corrected tail with Alice's actual measured ket retained. -/
lemma retain_measured_head {B T I : Type} [Fintype B] [Fintype T]
    [DecidableEq B] [DecidableEq T] (label : B) (correction : Matrix T T ℂ)
    (before : Matrix (B × T) I ℂ) :
    controlled (fun _ : B => correction) *
        ((selectHead (T := T) label).conjTranspose * selectHead label) * before =
      (selectHead (T := T) label).conjTranspose *
        (correction * (selectHead (T := T) label * before : Matrix T I ℂ) :
          Matrix T I ℂ) := by
  calc
    _ = (controlled (fun _ : B => correction) *
        (selectHead (T := T) label).conjTranspose) *
          (selectHead (T := T) label * before : Matrix T I ℂ) := by
      simp only [Matrix.mul_assoc]
    _ = ((selectHead (T := T) label).conjTranspose * correction) *
        (selectHead (T := T) label * before : Matrix T I ℂ) := by
      rw [controlled_insert]
    _ = _ := Matrix.mul_assoc _ _ _

/-- Alice's measured systems are retained even when the corrected unknown state is arbitrary. -/
def keptKraus (first second : Bool) : Matrix (Fin 4 × Fin 2) (Fin 2) ℂ :=
  (selectHead (T := Fin 2) (outcomeValue first second)).conjTranspose *
    correctedKraus first second

lemma keptKraus_eq (first second : Bool) :
    keptKraus first second = (2 : ℂ)⁻¹ •
      (selectHead (T := Fin 2) (outcomeValue first second)).conjTranspose := by
  rw [keptKraus, teleportation_correctedKraus_eq_half_identity, Matrix.mul_smul,
    Matrix.mul_one]

end

end QuantumAlg.QuantumTeleportation.RetainedAlice

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Basic
import all QuantumAlg.Algorithms.QPE.Construction
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An existing phase wire for the elementary source reflection

The original precision and confidence domain selects at least two phase
wires. Every stage can therefore borrow one different phase wire, with no
additional system or initialization promise. The selection below uses only
the original physical phase positions and remains distinct from every source
position. Exact restoration is supplied by the elementary reflection circuit.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

/-- The original legal parameters always provide two actual phase wires. -/
lemma selectedPhaseQubits_atLeastTwo {eps η : Real}
    (heps : 0 < eps) (heps_le : eps ≤ 1)
    (heta : 0 < η) (heta_le : η ≤ 1) :
    2 ≤ selectedPhaseQubits eps η := by
  have scale := selectedPhaseQubits_scale heps heta
  have inverse : (1 : Real) ≤ η⁻¹ := by
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1) heta).2 heta_le
  have twiceRadius : 2 * precisionRadius eps < 1 := by
    rw [precisionRadius, ← mul_div_assoc]
    apply (div_lt_one Real.pi_pos).2
    nlinarith [Real.pi_gt_three]
  by_contra small
  have casesWidth : selectedPhaseQubits eps η = 0 ∨ selectedPhaseQubits eps η = 1 := by
    omega
  rcases casesWidth with zero | one
  · rw [zero, pow_zero, one_mul] at scale
    linarith
  · rw [one, pow_one] at scale
    linarith

namespace PhaseWorkspace

/-- The existing physical control selected by the original binary-power stage. -/
def controlWire {t : Nat} (stage : Fin t) : Fin t :=
  stage.rev

/-- Choose one different existing phase wire; no new wire is allocated. -/
def workWire {t : Nat} (stage : Fin t) (wide : 2 ≤ t) : Fin t :=
  if (controlWire stage).val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- The borrowed wire is distinct from this stage's actual control. -/
lemma workWire_ne_controlWire {t : Nat} (stage : Fin t) (wide : 2 ≤ t) :
    workWire stage wide ≠ controlWire stage := by
  intro same
  have value := congrArg Fin.val same
  by_cases first : (controlWire stage).val = 0
  · simp only [workWire, first, if_true] at value
    omega
  · simp only [workWire, first, if_false] at value
    exact first value.symm

/-- Embed the same phase position into the complete phase-first register. -/
def fullWorkWire {t n : Nat} (stage : Fin t) (wide : 2 ≤ t) : Fin (t + n) :=
  Fin.castAdd n (workWire stage wide)

/-- The borrowed phase wire cannot coincide with any of the actual source wires. -/
lemma fullWorkWire_ne_source {t n : Nat} (stage : Fin t) (wide : 2 ≤ t)
    (source : Fin n) :
    fullWorkWire stage wide ≠ source.natAdd t := by
  intro same
  have value := congrArg Fin.val same
  change (workWire stage wide).val = t + source.val at value
  have inside := (workWire stage wide).isLt
  omega

/-- The same selected wire is already inside the original phase/source register. -/
lemma fullWorkWire_identity {t n : Nat} (stage : Fin t) (wide : 2 ≤ t) :
    (fullWorkWire (n := n) stage wide).val = (workWire stage wide).val := rfl

end PhaseWorkspace

end

end QuantumAlg.AmplitudeEstimation

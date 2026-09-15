/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Execution.Probability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ENNReal.Inv

/-!
# Exact probability law of actual finite uniform sampling

Every actual random outcome has one equal fraction of its original quantum
block's trace. The probability distribution is consequently the original
state's trace distribution followed by an independent finite uniform draw.
The statement is derived from the existing state operation and does not
supply a separate distribution witness to any execution.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance (count : ℕ+) : Nonempty (Fin count) := ⟨⟨0, count.pos⟩⟩

/-- Exact trace weight of one actual finite random choice. -/
theorem uniformChoice_block_mass {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (count : ℕ+) (entry : C) (outcome : Fin count) :
    ((uniformChoice state count).block (entry, outcome)).mass =
      (count : ℝ)⁻¹ * (state.block entry).mass :=
  divideMass_mass (state.block entry) count

private theorem uniform_pair_apply {C : Type} [Finite C] (distribution : PMF C)
    (count : ℕ+) (entry : C) (outcome : Fin count) :
    (distribution.bind (fun original => (PMF.uniformOfFintype (Fin count)).map
      (fun sample => (original, sample)))) (entry, outcome) =
        distribution entry * (count : ENNReal)⁻¹ := by
  classical
  let : Fintype C := Fintype.ofFinite C
  rw [PMF.bind_apply]
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [Finset.sum_eq_single entry]
  · simp
  · intro other _ different
    simp [different.symm]
  · simp

/-- The actual independent uniform operation preserves normalized execution mass. -/
theorem uniformChoice_normalized {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (normalized : state.IsNormalized) (count : ℕ+) :
    (uniformChoice state count).IsNormalized := by
  change (uniformChoice state count).mass = 1
  change state.mass = 1 at normalized
  exact (uniformChoice_mass state count).trans normalized

/-- The actual independent finite random instruction has the unchanged uniform PMF law. -/
theorem uniformChoice_toPMF {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (normalized : state.IsNormalized) (count : ℕ+) :
    (uniformChoice state count).toPMF (uniformChoice_normalized state normalized count) =
      (state.toPMF normalized).bind (fun original =>
        (PMF.uniformOfFintype (Fin count)).map (fun sample => (original, sample))) := by
  apply PMF.ext
  intro result
  obtain ⟨entry, outcome⟩ := result
  rw [ExecutionState.toPMF_apply, uniformChoice_block_mass, uniform_pair_apply,
    ExecutionState.toPMF_apply, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast count.pos), ENNReal.ofReal_natCast]
  exact mul_comm _ _

end
end QuantumAlg.Execution

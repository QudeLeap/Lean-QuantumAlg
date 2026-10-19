/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Random.Index
public import QuantumAlg.Core.Execution.Random.Kernel
public import QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Components.Classical.Model.BitWord.Random.Index
import all QuantumAlg.Core.Execution.Random
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Uniform finite labels for the actual native sampling kernel

A bijective relabeling of the generated bit string recovers the source's finite
uniform distribution. The identity retains every original weighted quantum
block and permits arbitrary subsequent classical maps, including collisions.
-/

namespace QuantumAlg.BitWord.Random

noncomputable section

open scoped Classical in
/-- The native bit kernel and finite uniform source induce exactly the same mapped state. -/
lemma randomKernel_map_indexed {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (width : Nat)
    (update : C × CShape.Value (.bits width) → D) :
    (Execution.kernelChoice state (fun _ => uniformBits width)).mapClassical update =
      (Execution.uniformChoice state ⟨2 ^ width, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => update (entry.1, (sampleEquiv width).symm entry.2)) := by
  classical
  apply ExecutionState.ext
  intro result
  apply DensityOperator.ext
  rw [ExecutionState.mapClassical_block_matrix, ExecutionState.mapClassical_block_matrix]
  apply Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl C) (sampleEquiv width))
  rintro ⟨entry, outcome⟩
  change (if update (entry, outcome) = result then _ else _) =
    (if update (entry, (sampleEquiv width).symm (sampleEquiv width outcome)) = result then
      ((Execution.uniformChoice state ⟨2 ^ width, Nat.two_pow_pos _⟩).block
        (entry, sampleEquiv width outcome)).matrix else _)
  simp only [Equiv.symm_apply_apply,
    Execution.kernelChoice_block_matrix,
    randomUniformBits_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rfl

end

end QuantumAlg.BitWord.Random

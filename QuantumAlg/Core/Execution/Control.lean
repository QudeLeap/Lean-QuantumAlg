/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# Interpreting finite classical conditionals

A conditional partitions the current blocks by the actual classical read,
runs the corresponding instruction body on each selected part, and combines
the results. The interpreter supplies the body interpretations and their proved
mass equalities. This helper introduces no circuit constructor or independent
resource witness.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {C D Value : Type} [Fintype C] [Fintype D] [Fintype Value]
  [DecidableEq Value] {R S : Register}

/-- Execute each body only on blocks selected by its actual classical read value. -/
def runSelected (state : ExecutionState C R) (read : C → Value)
    (body : Value → ExecutionState C R → ExecutionState D S)
    (mass : ∀ value input, (body value input).mass = input.mass) : ExecutionState D S :=
  ExecutionState.finiteSum (fun value => body value (state.selectClassical read value)) (by
    simp only [mass, ExecutionState.sum_selectClassical_mass]
    exact state.mass_le_one)

/-- The entire conditional preserves the incoming execution mass. -/
lemma runSelected_mass (state : ExecutionState C R) (read : C → Value)
    (body : Value → ExecutionState C R → ExecutionState D S)
    (mass : ∀ value input, (body value input).mass = input.mass) :
    (runSelected state read body mass).mass = state.mass := by
  simp only [runSelected, ExecutionState.finiteSum_mass, mass,
    ExecutionState.sum_selectClassical_mass]

/-- Every final block is exactly the sum of the executed selected parts. -/
lemma runSelected_block_matrix (state : ExecutionState C R) (read : C → Value)
    (body : Value → ExecutionState C R → ExecutionState D S)
    (mass : ∀ value input, (body value input).mass = input.mass) (output : D) :
    ((runSelected state read body mass).block output).matrix =
      ∑ value, ((body value (state.selectClassical read value)).block output).matrix := rfl

end

end QuantumAlg.Execution

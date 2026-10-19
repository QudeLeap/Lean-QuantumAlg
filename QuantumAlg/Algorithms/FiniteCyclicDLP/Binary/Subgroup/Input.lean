/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Subgroup
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber

/-!
# The unchanged proof-side logarithm after subgroup restriction

The finite Fourier analysis uses the same residue logarithm in the generated
subgroup and in the caller's ambient group [Sho95, source.tex:1704-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The same bounded logarithm is a witness for the internally represented instance. -/
public def subgroupInput {P : KnownOrderProblem G} (input : Canonical.Probability.SecretInput P) :
    Canonical.Probability.SecretInput (subgroupProblem P) where
  secret := input.secret
  target_eq_generator_pow := Subtype.ext input.target_eq_generator_pow

/-- No secret value is computed or changed by this proof-side restriction. -/
@[simp] public lemma subgroupInput_secret {P : KnownOrderProblem G} (input :
  Canonical.Probability.SecretInput P) :
    (subgroupInput input).secret = input.secret := by
  rfl

end

end QuantumAlg.FiniteCyclicDLP.Binary

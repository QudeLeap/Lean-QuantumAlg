/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.StateEmbedding
import all Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Reference extension of arbitrary rectangular Kraus intertwiners -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeBranch

noncomputable section

open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Reference extension also applies to nonunitary, unnormalized Kraus branches. -/
private lemma reference_intertwines {R S : Register} (embedding : S.Index ↪ R.Index)
    (native : HilbertOperator R) (source : HilbertOperator S)
    (derived : native * BasisEmbedding.matrix embedding = BasisEmbedding.matrix embedding * source)
    (Reference : Register) :
    let nativeRef : Matrix (R.prod Reference).Index (R.prod Reference).Index ℂ :=
      native ⊗ₖ (1 : HilbertOperator Reference)
    let sourceRef : Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ :=
      source ⊗ₖ (1 : HilbertOperator Reference)
    let j : Matrix (R.prod Reference).Index (S.prod Reference).Index ℂ :=
      BasisEmbedding.matrix (BasisEmbedding.withReference embedding Reference)
    nativeRef * j = j * sourceRef := by
  dsimp only
  rw [BasisEmbedding.reference_matrix (R := R) (S := S) embedding Reference,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, derived]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeBranch

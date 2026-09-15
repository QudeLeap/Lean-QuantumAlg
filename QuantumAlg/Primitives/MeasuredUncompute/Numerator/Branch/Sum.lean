/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Fibers

/-!
# Exact summation of all actual measured numerator results

There are exactly 2^n complete final stores and the literal Hadamard
amplitude has squared magnitude 1/2^n. Thus the same corrected joint matrix
in every real stored branch recovers that complete matrix after summation.
The calculation includes n=0 and retains the external reference
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorBranchSum

noncomputable section

open Execution NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual store count normalizes precisely the actual native Hadamard squared amplitude. -/
theorem coefficient_normalized (width : Nat) :
    (Fintype.card (Store (context width)) : ℂ) *
      (WalshHadamard.invSqrtCard width * star (WalshHadamard.invSqrtCard width)) = 1 := by
  rw [NumeratorStoredFibers.store_card, WalshHadamard.star_invSqrtCard,
    WalshHadamard.invSqrtCard_mul_self]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.two_pow_pos width).ne')

/-- Corrected formulas for every actual stored branch imply the complete joint matrix equality. -/
theorem full_matrix {width : Nat} {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History)
    (target : HilbertOperator (Register.prod (context width).register Reference))
    (blocks : ∀ stored : Store (context width),
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
        (WalshHadamard.invSqrtCard width * star (WalshHadamard.invSqrtCard width)) • target) :
    state.quantumMarginal.matrix = target :=
  matrix_of_uniform_store_blocks state target _ (coefficient_normalized width) blocks

end

end QuantumAlg.MeasuredUncompute.NumeratorBranchSum

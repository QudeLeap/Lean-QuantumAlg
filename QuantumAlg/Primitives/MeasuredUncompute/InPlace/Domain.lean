/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Preparation
import all QuantumAlg.Core.Execution.Input

/-!
# Original two-word domain of in-place modular arithmetic

The first supplied word is a nonzero residue and the second is any residue,
including zero. This is the source domain for both in-place division and
multiplication [LYL+26, sec_point_add/sec_point_add.tex:45-105,119-122].
The predicate restricts only local density support. It permits arbitrary
coherences and every external-reference extension, without supplying any
arithmetic execution behavior or initialized auxiliary system.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceDomain

noncomputable section

open Execution MAU.Inversion.SharedEEA.InversePreparation

/-- Both actual supplied words are residues, with only the first required to be nonzero. -/
def admissible (modulus : Nat) (basis : (before modulus.size).register.Index) : Prop :=
  0 < (inputBasisEquiv modulus.size basis).1.val ∧
    (inputBasisEquiv modulus.size basis).1.val < modulus ∧
    (inputBasisEquiv modulus.size basis).2.val < modulus

/-- The original arithmetic domain is a local support condition on an arbitrary mixed input. -/
def valid (modulus : Nat)
    (state : ExecutionState (Store (before modulus.size)) (before modulus.size).register) : Prop :=
  ∀ basis, ¬admissible modulus basis → state.quantumMarginal.matrix basis basis = 0

end

end QuantumAlg.MeasuredUncompute.InPlaceDomain

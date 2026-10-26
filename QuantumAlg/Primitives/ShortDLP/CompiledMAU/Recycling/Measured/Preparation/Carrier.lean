/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Seed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement.Zero

/-!
# The true complete-frame seed is the same canonical unit-one carrier

Every control, auxiliary, helper and flag coordinate is compared in the
original physical placement. The identity representative is one modulo the
actual positive modulus, including modulus one [G25, main.tex:271-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat) (modulus : BitVec width) [NeZero modulus.toNat]

/-- The physically loaded frame is exactly the zero-control embedding of the original unit one. -/
lemma preparedSeed_zeroEmbedding :
    preparedSeed base noQuantum m ell width modulus.toNat =
      Placement.zeroEmbedding base noQuantum m ell width modulus 1 := by
  change Placement.basis base noQuantum m ell width
      ((Physical.qubits width).basisEquiv.symm
        (Physical.cleanLabel width false (BitVec.ofNat width (1 % modulus.toNat)))) =
    Placement.basis base noQuantum m ell width
      ((Physical.qubits width).basisEquiv.symm
        (Physical.cleanLabel width (finTwoEquiv 0) (Carrier.unitWord modulus 1)))
  simp only [Carrier.unitWord, Units.val_one, ZMod.val_one_eq_one_mod]
  rfl

/-- The complete reference embedding keeps both reference coordinates at that same true seed. -/
lemma preparedSeed_zeroJointEmbedding (Reference : Register) (reference : Reference.Index) :
    zeroJointEmbedding base noQuantum m ell width modulus Reference (1, reference) =
      (preparedSeed base noQuantum m ell width modulus.toNat, reference) := by
  apply Prod.ext
  · exact (preparedSeed_zeroEmbedding base noQuantum m ell width modulus).symm
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

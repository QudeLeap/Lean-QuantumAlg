/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Control

/-!
# Exact zero-control subspace retained between actual measured stages

The comparison represents every unit/reference density block in the actual
zero-control, zero-auxiliary, clean-helper frame. It is a mathematical
isometry and introduces no executable packing or input certificate
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

private lemma embedding_matrix_trans {R S T : Register}
    (first : T.Index ↪ S.Index) (second : S.Index ↪ R.Index) :
    BasisEmbedding.matrix (first.trans second) =
      BasisEmbedding.matrix second * BasisEmbedding.matrix first := by
  classical
  ext row column
  simp [BasisEmbedding.matrix, Matrix.mul_apply]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Complete actual zero-control embedding beside the same untouched external reference. -/
def zeroJointEmbedding (Reference : Register) :
    ((Recycling.Carrier.units modulus.toNat).prod Reference).Index ↪
      ((Context base noQuantum m ell width).register.prod Reference).Index :=
  BasisEmbedding.withReference
    (Placement.zeroEmbedding base noQuantum m ell width modulus) Reference

/-- The actual between-stage embedding is precisely zero-control injection into the full carrier. -/
lemma zeroJointEmbedding_matrix (Reference : Register) :
    BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
      BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
        BasisEmbedding.matrix
          (BasisEmbedding.withReference
            (Recycling.ControlKraus.zeroInjection (S := Recycling.Carrier.units modulus.toNat))
            Reference) := by
  have embeddings : zeroJointEmbedding base noQuantum m ell width modulus Reference =
      (BasisEmbedding.withReference
        (Recycling.ControlKraus.zeroInjection (S := Recycling.Carrier.units modulus.toNat))
        Reference).trans
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) := by
    apply Function.Embedding.ext
    intro label
    rfl
  rw [embeddings]
  exact embedding_matrix_trans _ _

/-- Encode all original Store correlations with an arbitrary mixed unit/reference state. -/
def encodeUnitState {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) × History)
      ((Recycling.Carrier.units modulus.toNat).prod Reference)) :
    State (Context base noQuantum m ell width) Reference History where
  block entry := BasisEmbedding.density
    (zeroJointEmbedding base noQuantum m ell width modulus Reference) (state.block entry)
  total_le_one := by
    simpa only [BasisEmbedding.basisEmbedding_density_mass] using state.total_le_one

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

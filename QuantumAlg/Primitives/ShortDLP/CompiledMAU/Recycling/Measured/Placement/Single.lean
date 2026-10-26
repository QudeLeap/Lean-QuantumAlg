/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Single
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Placement

/-!
# Exact caller-context H and phase action on the measured arithmetic carrier

The complete ordered physical-wire certificate transports the native
operator, rather than only its register dimension. Both matrix equalities
hold on all source-unit columns and all actual physical rows
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Placement

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- The actual placed native H retains the complete unit carrier and its coherent sign. -/
lemma hadamard_intertwines (environment : OracleModel.empty.Interpretation) :
    ((single base noQuantum m ell width Gate.HOp).matrix environment :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (embedding base noQuantum m ell width modulus) =
    BasisEmbedding.matrix (embedding base noQuantum m ell width modulus) *
      (UnitaryOperator.prodTensor Gate.HOp
        (1 : UnitaryOperator (Recycling.Carrier.units modulus.toNat)) :
          HilbertOperator (Recycling.Carrier.full modulus.toNat)) := by
  rw [measuredSingle_matrix]
  exact Recycling.Placement.reindex_intertwines _ _ _ _
    (Measured.Carrier.physical_hadamard_intertwines modulus environment)

/-- The actual placed stored-feedback phase preserves its exact full unit-carrier matrix. -/
lemma phase_intertwines (angle : Real) (environment : OracleModel.empty.Interpretation) :
    ((single base noQuantum m ell width (phaseGateOp angle)).matrix environment :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (embedding base noQuantum m ell width modulus) =
    BasisEmbedding.matrix (embedding base noQuantum m ell width modulus) *
      (UnitaryOperator.prodTensor (phaseGateOp angle)
        (1 : UnitaryOperator (Recycling.Carrier.units modulus.toNat)) :
          HilbertOperator (Recycling.Carrier.full modulus.toNat)) := by
  rw [measuredSingle_matrix]
  exact Recycling.Placement.reindex_intertwines _ _ _ _
    (Measured.Carrier.physical_phase_intertwines modulus angle environment)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Placement

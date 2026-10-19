/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Subgroup
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle

/-!
# The represented subgroup retains the original ambient oracle meaning

The ambient group is allowed to be larger than the generator's cyclic
subgroup. Its native oracle restricts to the same represented source action.
The physical inclusion below proves this restriction on arbitrary coherent
and mixed states, with arbitrary external references; no ambient-generation
assumption is added [Sho95, source.tex:1704-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Include the full represented source basis into the original native ambient basis. -/
public def ambientEmbedding (P : KnownOrderProblem G) :
    (OrderOracle.layout (subgroupProblem P)).Basis ↪ (OrderOracle.layout P).Basis where
  toFun state := (OrderOracle.basisEquiv P).symm
    (ambientBasis P (OrderOracle.basisEquiv (subgroupProblem P) state))
  inj' := (OrderOracle.basisEquiv P).symm.injective.comp
    ((ambientBasis_injective P).comp (OrderOracle.basisEquiv (subgroupProblem P)).injective)

/-- The original zero initialization has exactly the represented subgroup meaning. -/
public lemma ambientEmbedding_zero (P : KnownOrderProblem G) :
    ambientEmbedding P (OrderOracle.layout (subgroupProblem P)).zeroLabel =
      (OrderOracle.layout P).zeroLabel := by
  apply (OrderOracle.basisEquiv P).injective
  simp only [ambientEmbedding, Function.Embedding.coeFn_mk, Equiv.apply_symm_apply,
    OrderOracle.basisEquiv_zero, ambientBasis, Subgroup.coe_one]
  exact Prod.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl)) rfl

/-- Inclusion commutes with the complete physical source action on every represented basis. -/
public lemma ambientEmbedding_action (P : KnownOrderProblem G)
    (state : (OrderOracle.layout (subgroupProblem P)).Basis) :
    OrderOracle.physicalAction P (ambientEmbedding P state) =
      ambientEmbedding P (OrderOracle.physicalAction (subgroupProblem P) state) := by
  apply (OrderOracle.basisEquiv P).injective
  simp only [ambientEmbedding, Function.Embedding.coeFn_mk, OrderOracle.physicalAction,
    Equiv.trans_apply, Equiv.apply_symm_apply, OrderOracle.actionEquiv,
    Equiv.coe_fn_mk, ambientBasis_action]

/-- The original ambient and represented source operators have the same full-subspace action. -/
public lemma ambient_oracle_intertwines (P : KnownOrderProblem G) :
    (OrderOracle.operator P : HilbertOperator (OrderOracle.layout P).register) *
      BasisEmbedding.matrix (R := (OrderOracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (ambientEmbedding P) =
    BasisEmbedding.matrix (R := (OrderOracle.layout P).register)
      (S := (OrderOracle.layout (subgroupProblem P)).register) (ambientEmbedding P) *
      (OrderOracle.operator (subgroupProblem P) :
        HilbertOperator (OrderOracle.layout (subgroupProblem P)).register) :=
  BasisEmbedding.permutation_intertwines (R := (OrderOracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (ambientEmbedding P)
    (OrderOracle.physicalAction (subgroupProblem P)) (OrderOracle.physicalAction P)
    (ambientEmbedding_action P)

/-- The subgroup restriction preserves arbitrary mixed inputs and their external references. -/
public lemma ambient_oracle_density_reference (P : KnownOrderProblem G)
    (Reference : Register)
    (state : DensityOperator
      (Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)) :
    DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (OrderOracle.operator P) (1 : UnitaryOperator Reference))
      (BasisEmbedding.density (R := Register.prod (OrderOracle.layout P).register Reference)
        (S := Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)
        (BasisEmbedding.withReference (R := (OrderOracle.layout P).register)
          (S := (OrderOracle.layout (subgroupProblem P)).register)
          (ambientEmbedding P) Reference) state) =
    BasisEmbedding.density (R := Register.prod (OrderOracle.layout P).register Reference)
      (S := Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)
      (BasisEmbedding.withReference (R := (OrderOracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (ambientEmbedding P) Reference)
      (DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (OrderOracle.operator (subgroupProblem P))
          (1 : UnitaryOperator Reference)) state) :=
  BasisEmbedding.density_applyUnitary_reference (R := (OrderOracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (ambientEmbedding P)
    (OrderOracle.operator (subgroupProblem P)) (OrderOracle.operator P)
    (ambient_oracle_intertwines P) Reference state

end

end QuantumAlg.FiniteCyclicDLP.Binary

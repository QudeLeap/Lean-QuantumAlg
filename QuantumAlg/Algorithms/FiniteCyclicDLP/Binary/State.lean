/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Oracle
public import QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Oracle
import all QuantumAlg.Components.Encoded.StateEmbedding

/-!
# Complete state and external-reference bridge for the binary DLP oracle

The implemented physical permutation intertwines the original subgroup oracle
on the entire encoded subspace. The statement is coherent, mixed-state and
reference-aware; neither zero workspace nor a separable reference is assumed.
Only the physical representation changes [Sho95, source.tex:1756-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The actual binary and source oracle matrices intertwine on the full encoded subspace. -/
public lemma oracle_intertwines (P : KnownOrderProblem G) :
    (Oracle.operator P : HilbertOperator (Oracle.layout P).register) *
        BasisEmbedding.matrix (R := (Oracle.layout P).register)
          (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P) =
      BasisEmbedding.matrix (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P) *
        (OrderOracle.operator (subgroupProblem P) :
          HilbertOperator (OrderOracle.layout (subgroupProblem P)).register) :=
  BasisEmbedding.permutation_intertwines (R := (Oracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
    (OrderOracle.physicalAction (subgroupProblem P)) (Oracle.physicalAction P)
    (Oracle.physicalAction_source P)

/-- Every mixed input on the encoded subspace has exactly the source oracle evolution. -/
public lemma oracle_density (P : KnownOrderProblem G)
    (state : DensityOperator (OrderOracle.layout (subgroupProblem P)).register) :
    DensityOperator.applyUnitary (Oracle.operator P)
        (BasisEmbedding.density (R := (Oracle.layout P).register)
          (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
          state) =
      BasisEmbedding.density (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
        (DensityOperator.applyUnitary (OrderOracle.operator (subgroupProblem P)) state) :=
  BasisEmbedding.density_applyUnitary (R := (Oracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
    (OrderOracle.operator (subgroupProblem P)) (Oracle.operator P) (oracle_intertwines P) state

/-- Arbitrary reference entanglement and every subnormalized branch survive the representation. -/
public lemma oracle_density_reference (P : KnownOrderProblem G) (Reference : Register)
    (state : DensityOperator
      (Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (Oracle.operator P) (1 : UnitaryOperator Reference))
        (BasisEmbedding.density (R := Register.prod (Oracle.layout P).register Reference)
          (S := Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)
          (BasisEmbedding.withReference (R := (Oracle.layout P).register)
            (S := (OrderOracle.layout (subgroupProblem P)).register)
            (Oracle.sourceEmbedding P) Reference) state) =
      BasisEmbedding.density (R := Register.prod (Oracle.layout P).register Reference)
        (S := Register.prod (OrderOracle.layout (subgroupProblem P)).register Reference)
        (BasisEmbedding.withReference (R := (Oracle.layout P).register)
          (S := (OrderOracle.layout (subgroupProblem P)).register)
          (Oracle.sourceEmbedding P) Reference)
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (OrderOracle.operator (subgroupProblem P))
            (1 : UnitaryOperator Reference)) state) :=
  BasisEmbedding.density_applyUnitary_reference (R := (Oracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
    (OrderOracle.operator (subgroupProblem P)) (Oracle.operator P)
    (oracle_intertwines P) Reference state

end

end QuantumAlg.FiniteCyclicDLP.Binary

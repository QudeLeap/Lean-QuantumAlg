/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Fourier
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.State
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Fourier
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Oracle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Base.Gate.Effect.Extension

/-!
# Born bridge from the binary circuit to the original subgroup experiment

The binary circuit's prepared state, sole query and inverse Fourier transforms
are compared as actual vectors, including phase. The encoded source vectors
have zero amplitudes on unused labels. Mapping their Born distribution through
the actual exponent readout therefore gives the original source experiment
[Sho95, source.tex:1713-1841].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Encoding changes only the group basis label, preserving both exponents exactly. -/
public lemma sourceEmbedding_fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : Carrier P) :
    Oracle.sourceEmbedding P
      (OrderBornBridge.fullBasis (subgroupProblem P) left right tail) =
        Fourier.fullBasis P left right (encodeGroup P tail) := by
  simp [Oracle.sourceEmbedding, Oracle.logicalEmbedding, OrderBornBridge.fullBasis,
    Fourier.fullBasis]
  rfl

private lemma encodeGroup_eq_zero (P : KnownOrderProblem G) (tail : Carrier P) :
    encodeGroup P tail = 0 ↔ tail = 1 := by
  rw [← encodeGroup_one P]
  exact (encodeGroup_injective P).eq_iff

/-- Both native preparation words produce the same amplitudes under the fixed encoding. -/
public lemma preparedVec_source (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (basis : (OrderOracle.layout (subgroupProblem P)).Basis) :
    Fourier.preparedVec P expansion (Oracle.sourceEmbedding P basis) =
      OrderBornBridge.preparedVec (subgroupProblem P) expansion basis := by
  obtain ⟨⟨⟨left, right⟩, tail⟩, rfl⟩ :=
    (OrderOracle.basisEquiv (subgroupProblem P)).symm.surjective basis
  have sourceFormula :
      OrderBornBridge.preparedVec (subgroupProblem P) expansion
        (OrderBornBridge.fullBasis (subgroupProblem P) left right tail) =
      @ite ℂ (tail = 1) (Classical.propDecidable _)
        (if right.val < P.order then
          if left.val < P.order then
            OrderPreparation.invSqrtOrder P.order * OrderPreparation.invSqrtOrder P.order
          else 0
        else 0) 0 :=
    OrderBornBridge.preparedVec_apply (subgroupProblem P) expansion left right tail
  have same :
      @ite ℂ (encodeGroup P tail = 0) (Classical.propDecidable _)
          (if right.val < P.order then
            if left.val < P.order then
              OrderPreparation.invSqrtOrder P.order * OrderPreparation.invSqrtOrder P.order
            else 0
          else 0) 0 =
        @ite ℂ (tail = 1) (Classical.propDecidable _)
          (if right.val < P.order then
            if left.val < P.order then
              OrderPreparation.invSqrtOrder P.order * OrderPreparation.invSqrtOrder P.order
            else 0
          else 0) 0 := by
    exact congrArg (fun condition : Prop =>
      @ite ℂ condition (Classical.propDecidable condition)
        (if right.val < P.order then
          if left.val < P.order then
            OrderPreparation.invSqrtOrder P.order * OrderPreparation.invSqrtOrder P.order
          else 0
        else 0) 0) (propext (encodeGroup_eq_zero P tail))
  exact (congrArg (fun index : (Oracle.layout P).Basis =>
    Fourier.preparedVec P expansion index) (sourceEmbedding_fullBasis P left right tail)).trans
      ((Fourier.binaryFourier_preparedVec_apply P expansion left right (encodeGroup P tail)).trans
        (same.trans sourceFormula.symm))

/-- The actual native preparations have no amplitude on any unused binary group label. -/
public lemma preparedVec_unused (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (basis : (Oracle.layout P).Basis)
    (unused : basis ∉ Set.range (Oracle.sourceEmbedding P)) :
    Fourier.preparedVec P expansion basis = 0 := by
  obtain ⟨⟨⟨left, right⟩, tail⟩, rfl⟩ := (Oracle.basisEquiv P).symm.surjective basis
  have nonzero : tail ≠ 0 := by
    intro zero
    apply unused
    refine ⟨OrderBornBridge.fullBasis (subgroupProblem P) left right 1, ?_⟩
    rw [sourceEmbedding_fullBasis, encodeGroup_one]
    exact congrArg (Fourier.fullBasis P left right) zero.symm
  exact (Fourier.binaryFourier_preparedVec_apply P expansion left right tail).trans (if_neg nonzero)

/-- Preparation compatibility is a full-vector identity, not only agreement of measured weights. -/
public lemma preparedVec_extension (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    Fourier.preparedVec P expansion =
      Effect.extensionVector (Oracle.sourceEmbedding P)
        (OrderBornBridge.preparedVec (subgroupProblem P) expansion) := by
  classical
  ext basis
  by_cases valid : basis ∈ Set.range (Oracle.sourceEmbedding P)
  · obtain ⟨source, rfl⟩ := valid
    rw [preparedVec_source,
      Effect.extensionVector_image _ (Oracle.sourceEmbedding P).injective]
  · rw [preparedVec_unused P expansion basis valid, Effect.extensionVector_apply]
    have different : ∀ source, Oracle.sourceEmbedding P source ≠ basis :=
      fun source same => valid ⟨source, same⟩
    simp [different]

/-- The same granted query preserves the coherent encoded preparation relation. -/
public lemma postOracleVec_extension (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    Fourier.postOracleVec P expansion =
      Effect.extensionVector (Oracle.sourceEmbedding P)
        (OrderBornBridge.postOracleVec (subgroupProblem P) expansion) := by
  have binaryQuery := congrArg
    (fun operator : UnitaryOperator (Oracle.layout P).register =>
      operator.applyVec (Fourier.preparedVec P expansion))
    (Oracle.binaryOracle_circuit_matrix AlgorithmGate.model P)
  have sourceQuery := congrArg
    (fun operator : UnitaryOperator (OrderOracle.layout (subgroupProblem P)).register =>
      operator.applyVec (OrderBornBridge.preparedVec (subgroupProblem P) expansion))
    (OrderOracle.circuit_matrix AlgorithmGate.model (subgroupProblem P))
  exact binaryQuery.trans
    ((congrArg (Oracle.operator P).applyVec (preparedVec_extension P expansion)).trans
      ((BasisEmbedding.applyVec_extension (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
        (OrderOracle.operator (subgroupProblem P)) (Oracle.operator P) (oracle_intertwines P)
        (OrderBornBridge.preparedVec (subgroupProblem P) expansion)).trans
          (congrArg (Effect.extensionVector (R := (Oracle.layout P).register)
            (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P))
              sourceQuery.symm)))

/-- The generated binary inverse QFTs agree with the source on every valid row and column. -/
public lemma inverseQFTs_source_entry (P : KnownOrderProblem G)
    (row column : (OrderOracle.layout (subgroupProblem P)).Basis) :
    ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P))
      (Oracle.sourceEmbedding P row) (Oracle.sourceEmbedding P column) =
        ((OrderCircuit.inverseQFTs (subgroupProblem P)).matrix (OrderOracle.interpretation
          (subgroupProblem P))) row column := by
  obtain ⟨⟨⟨left, right⟩, tail⟩, rfl⟩ :=
    (OrderOracle.basisEquiv (subgroupProblem P)).symm.surjective row
  obtain ⟨⟨⟨inputLeft, inputRight⟩, inputTail⟩, rfl⟩ :=
    (OrderOracle.basisEquiv (subgroupProblem P)).symm.surjective column
  have sourceFormula :
      ((OrderCircuit.inverseQFTs (subgroupProblem P)).matrix (OrderOracle.interpretation
        (subgroupProblem P)))
          (OrderBornBridge.fullBasis (subgroupProblem P) left right tail)
          (OrderBornBridge.fullBasis (subgroupProblem P) inputLeft inputRight inputTail) =
        @ite ℂ (tail = inputTail) (Classical.propDecidable _)
          ((star (QFTOperator (OrderPreparation.width P))) left inputLeft *
            (star (QFTOperator (OrderPreparation.width P))) right inputRight) 0 :=
    OrderBornBridge.inverseQFTs_matrix_fullBasis (subgroupProblem P)
      left right inputLeft inputRight tail inputTail
  have same :
      @ite ℂ (encodeGroup P tail = encodeGroup P inputTail) (Classical.propDecidable _)
          ((star (QFTOperator (OrderPreparation.width P))) left inputLeft *
            (star (QFTOperator (OrderPreparation.width P))) right inputRight) 0 =
        @ite ℂ (tail = inputTail) (Classical.propDecidable _)
          ((star (QFTOperator (OrderPreparation.width P))) left inputLeft *
            (star (QFTOperator (OrderPreparation.width P))) right inputRight) 0 := by
    exact congrArg (fun condition : Prop =>
      @ite ℂ condition (Classical.propDecidable condition)
        ((star (QFTOperator (OrderPreparation.width P))) left inputLeft *
          (star (QFTOperator (OrderPreparation.width P))) right inputRight) 0)
      (propext (encodeGroup_injective P).eq_iff)
  exact (congrArg₂ (fun row column : (Oracle.layout P).Basis =>
    ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P)) row column)
    (sourceEmbedding_fullBasis P left right tail)
    (sourceEmbedding_fullBasis P inputLeft inputRight inputTail)).trans
      ((Fourier.binaryFourier_inverseQFTs_matrix_fullBasis P
        left right inputLeft inputRight (encodeGroup P tail) (encodeGroup P inputTail)).trans
          (same.trans sourceFormula.symm))

/-- Fourier gates on the exponents cannot move valid group amplitude to an unused label. -/
public lemma inverseQFTs_unused_entry (P : KnownOrderProblem G)
    (row : (Oracle.layout P).Basis)
    (column : (OrderOracle.layout (subgroupProblem P)).Basis)
    (unused : row ∉ Set.range (Oracle.sourceEmbedding P)) :
    ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P)) row (Oracle.sourceEmbedding P column)
      = 0 := by
  obtain ⟨⟨⟨left, right⟩, tail⟩, rfl⟩ := (Oracle.basisEquiv P).symm.surjective row
  obtain ⟨⟨⟨inputLeft, inputRight⟩, inputTail⟩, rfl⟩ :=
    (OrderOracle.basisEquiv (subgroupProblem P)).symm.surjective column
  have different : tail ≠ encodeGroup P inputTail := by
    intro same
    exact unused ⟨OrderBornBridge.fullBasis (subgroupProblem P) left right inputTail,
      (sourceEmbedding_fullBasis P left right inputTail).trans
        (congrArg (Fourier.fullBasis P left right) same.symm)⟩
  exact (congrArg (fun index : (Oracle.layout P).Basis =>
    ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P)) (Fourier.fullBasis P left right tail)
      index)
    (sourceEmbedding_fullBasis P inputLeft inputRight inputTail)).trans
      ((Fourier.binaryFourier_inverseQFTs_matrix_fullBasis P
        left right inputLeft inputRight tail (encodeGroup P inputTail)).trans (if_neg different))

/-- The actual two-QFT operator intertwines the entire encoded subspace. -/
public lemma inverseQFTs_intertwines (P : KnownOrderProblem G) :
    (((Circuit.inverseQFTs P).matrix (Oracle.interpretation P)) : HilbertOperator (Oracle.layout
      P).register) *
      BasisEmbedding.matrix (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P) =
    BasisEmbedding.matrix (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P) *
      (((OrderCircuit.inverseQFTs (subgroupProblem P)).matrix (OrderOracle.interpretation
        (subgroupProblem P))) :
        HilbertOperator (OrderOracle.layout (subgroupProblem P)).register) := by
  classical
  apply BasisEmbedding.intertwines_of_columns (R := (Oracle.layout P).register)
    (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
    ((OrderCircuit.inverseQFTs (subgroupProblem P)).matrix (OrderOracle.interpretation
      (subgroupProblem P))) ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P))
  intro row column
  by_cases valid : row ∈ Set.range (Oracle.sourceEmbedding P)
  · obtain ⟨source, rfl⟩ := valid
    refine (inverseQFTs_source_entry P source column).trans ?_
    simp only [(Oracle.sourceEmbedding P).injective.eq_iff,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine (inverseQFTs_unused_entry P row column valid).trans ?_
    have different : ∀ source, Oracle.sourceEmbedding P source ≠ row :=
      fun source same => valid ⟨source, same⟩
    simp [different]

/-- Complete phase-exact output state of the binary native word. -/
public lemma evolvedState_extension (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    Fourier.evolvedState P expansion =
      BasisEmbedding.vector (R := (Oracle.layout P).register)
        (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
        (OrderBornBridge.evolvedState (subgroupProblem P) expansion) := by
  have finalVector :
      ((Circuit.circuit P expansion).applyVec (Oracle.interpretation P)) (Fourier.inputVec P) =
        Effect.extensionVector (Oracle.sourceEmbedding P)
          (((OrderCircuit.circuit (subgroupProblem P) expansion).applyVec
            (OrderOracle.interpretation (subgroupProblem P)))
            (OrderBornBridge.inputVec (subgroupProblem P))) :=
    (Fourier.binaryFourier_circuit_applyVec_zero P expansion).trans
      ((congrArg ((Circuit.inverseQFTs P).applyVec (Oracle.interpretation P))
        (postOracleVec_extension P expansion)).trans
        ((BasisEmbedding.applyVec_extension (R := (Oracle.layout P).register)
          (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
          ((OrderCircuit.inverseQFTs (subgroupProblem P)).matrix (OrderOracle.interpretation
            (subgroupProblem P))) ((Circuit.inverseQFTs P).matrix (Oracle.interpretation P))
          (inverseQFTs_intertwines P)
          (OrderBornBridge.postOracleVec (subgroupProblem P) expansion)).trans
            (congrArg (Effect.extensionVector (R := (Oracle.layout P).register)
              (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P))
              (OrderBornBridge.circuit_applyVec_zero (subgroupProblem P) expansion).symm)))
  apply NormalizedVector.ext
  intro basis
  exact congrArg (fun state : HilbertVector (Oracle.layout P).register => state basis) finalVector

end

end QuantumAlg.FiniteCyclicDLP.Binary

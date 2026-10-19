/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Cascade.Correctness
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Correctness
import all QuantumAlg.Core.Execution.Context.Embedding.Permutation

/-!
# Full-density correctness of the actual initialized converted cascade

Actual initialization supplies the fixed arithmetic work and selector and
retains the original finite cells. The converted cascade then acts on those
same complete entries. Its support premise is checked on the prescribed
initialized density after the inverse coordinate operator, without referring
to execution or requiring the caller to supply allocated workspace.

The resulting equality retains the complete quantum register and arbitrary
reference correlations. Discharging this mathematical support predicate from
the original Montgomery-encoded affine input is a separate obligation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MeasuredUncompute

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma placedConvertedCascade_marginal {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((placedConvertedCascade E points order coefficient allowAllocation).execute environment
      Reference
      (ContextPermutation.state (Allocation.body_entries p.size count) original)).quantumMarginal =
      ((convertedCascade E points order coefficient false).execute environment Reference
        original).quantumMarginal.reindex
          (ContextPermutation.referenceBasis (Allocation.body_entries p.size count) Reference) := by
  have actual := Circuit.permutation_embed_execute
    (environment := environment) (allowAllocation := allowAllocation)
    (Allocation.body_entries p.size count) (convertedCascade E points order coefficient false)
    Reference original
  have marginal := congrArg
    (fun result : State (Allocation.after p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (placedConvertedCascade E points order coefficient allowAllocation).Path)) =>
        result.quantumMarginal) actual
  exact marginal.trans (Allocation.permuted_marginal _ _)

/-- The complete converted target uses the same entries produced by actual initialization. -/
def placedConvertedTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (Reference : Register) :
    UnitaryOperator (Register.prod (Allocation.after p.size count).register Reference) :=
  UnitaryOperator.reindex
    (ContextPermutation.referenceBasis (Allocation.body_entries p.size count) Reference)
    (convertedCascadeTarget (environment := environment) E points order coefficient Reference)

/-- Actual converted execution has the full joint target on the converted mathematical domain. -/
lemma placedConvertedCascade_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (Allocation.after p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : cascadeSupport E points Reference order
      (DensityOperator.applyUnitary
        (pairOperator (environment := environment) p.size count (InPlaceTarget.modulusWord p)
          coefficient⁻¹ Reference)
        (original.quantumMarginal.reindex
          (ContextPermutation.referenceBasis (Allocation.body_entries p.size count)
            Reference).symm))) (allowAllocation : Bool := true) :
    ((placedConvertedCascade E points order coefficient allowAllocation).execute environment
      Reference
      original).quantumMarginal =
      DensityOperator.applyUnitary (placedConvertedTarget (environment := environment) E points
        order coefficient Reference)
        original.quantumMarginal := by
  let coordinates := ContextPermutation.referenceBasis (Allocation.body_entries p.size count)
    Reference
  obtain ⟨reversed, roundtrip⟩ :=
    ContextPermutation.state_surjective (Allocation.body_entries p.size count) original
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    have mapped := Allocation.permuted_marginal (Allocation.body_entries p.size count) reversed
    rw [roundtrip] at mapped
    have back := congrArg (fun density => density.reindex coordinates.symm) mapped.symm
    rw [DensityOperator.reindex_trans, Equiv.self_trans_symm,
      DensityOperator.reindex_refl] at back
    exact back
  have originalSupport : cascadeSupport E points Reference order
      (DensityOperator.applyUnitary
        (pairOperator (environment := environment) p.size count (InPlaceTarget.modulusWord p)
          coefficient⁻¹ Reference)
        reversed.quantumMarginal) := by
    rw [reversedMarginal]
    exact support
  have actual := placedConvertedCascade_marginal (environment := environment)
    (allowAllocation := allowAllocation)
    E points order coefficient reversed
  rw [roundtrip, convertedCascade_density E points order coefficient reversed originalSupport false,
    reversedMarginal, DensityOperator.applyUnitary_reindex, DensityOperator.reindex_trans] at actual
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  rw [inverse, DensityOperator.reindex_refl] at actual
  exact actual

/-- The prescribed result combines the original preparation factors and the complete target. -/
def convertedResultDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (input : DensityOperator (Register.prod (Allocation.before p.size count).register Reference)) :
    DensityOperator (Register.prod (Allocation.after p.size count).register Reference) :=
  DensityOperator.applyUnitary (placedConvertedTarget (environment := environment) E points order
    coefficient Reference)
    (Allocation.initializedDensity p count Reference input)

/-- The cascade domain is checked on independently initialized and inverse-converted density. -/
def convertedInitializedSupport {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (input : DensityOperator (Register.prod (Allocation.before p.size count).register Reference)) :
    Prop :=
  cascadeSupport E points Reference order
    (DensityOperator.applyUnitary
      (pairOperator (environment := environment) p.size count (InPlaceTarget.modulusWord p)
        coefficient⁻¹ Reference)
      ((Allocation.initializedDensity p count Reference input).reindex
        (ContextPermutation.referenceBasis (Allocation.body_entries p.size count) Reference).symm))

/-- The actual allocating converted circuit realizes its full-reference prescribed density. -/
lemma convertedCircuit_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) {Reference : Register} {H : Type} [Fintype H]
    (original : State (Allocation.before p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : convertedInitializedSupport (environment := environment) E points order coefficient
      Reference
      original.quantumMarginal) :
    ((convertedCircuit E points order coefficient).execute environment
      Reference original).quantumMarginal =
      convertedResultDensity (environment := environment) E points order coefficient Reference
        original.quantumMarginal := by
  have initializedSupport : cascadeSupport E points Reference order
      (DensityOperator.applyUnitary
        (pairOperator (environment := environment) p.size count (InPlaceTarget.modulusWord p)
          coefficient⁻¹ Reference)
        (((Allocation.initializeWork p count).execute environment
          Reference original).quantumMarginal.reindex
          (ContextPermutation.referenceBasis (Allocation.body_entries p.size count)
            Reference).symm)) := by
    rw [Allocation.initialize_density]
    exact support
  rw [convertedCircuit, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    placedConvertedCascade_density E points order coefficient _ initializedSupport,
    Allocation.initialize_density]
  rfl

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

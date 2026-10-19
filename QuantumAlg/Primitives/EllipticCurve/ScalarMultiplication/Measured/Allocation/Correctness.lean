/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Support
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Correctness
import all QuantumAlg.Core.Execution.Context.Embedding.Permutation

/-!
# Complete initialized scalar action on its mathematical trajectory domain

The same actual circuit prepares its work, retains its finite result cells,
and executes the prescribed measured point steps. Its independent target
contains the two fixed preparation factors and the mathematical point product.
Trajectory support is checked on that independent initialized density. For a
single selected step, support follows directly from the original supplied input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma permuted_marginal {source destination : RuntimeCtx .quantum}
    (same : source.entries.Perm destination.entries) {Reference : Register} {H : Type}
    [Fintype H] (original : State source Reference H) :
    (ContextPermutation.state same original).quantumMarginal =
      original.quantumMarginal.reindex (ContextPermutation.referenceBasis same Reference) := by
  rw [ContextPermutation.state, MeasuredPointAddition.reindex_marginal,
    ExecutionState.mapClassical_quantumMarginal]

private lemma placedCascade_marginal {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((placedCascade E points order allowAllocation).execute environment Reference
      (ContextPermutation.state (body_entries p.size count) original)).quantumMarginal =
        ((cascade E points order false).execute environment
          Reference original).quantumMarginal.reindex
          (ContextPermutation.referenceBasis (body_entries p.size count) Reference) := by
  have actual := Circuit.permutation_embed_execute
    (environment := environment) (allowAllocation := allowAllocation)
    (body_entries p.size count) (cascade E points order false) Reference original
  have marginal := congrArg
    (fun result : State (after p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (placedCascade E points order allowAllocation).Path)) =>
        result.quantumMarginal) actual
  exact marginal.trans (permuted_marginal _ _)

/-- The independent point product uses precisely the entries produced by actual initialization. -/
def placedTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (Reference : Register) :
    UnitaryOperator (Register.prod (after p.size count).register Reference) :=
  UnitaryOperator.reindex (ContextPermutation.referenceBasis (body_entries p.size count) Reference)
    (cascadeTarget E points Reference order)

/-- Actual post-allocation execution realizes the independent complete point product. -/
lemma placedCascade_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (after p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : cascadeSupport E points Reference order
      (original.quantumMarginal.reindex
        (ContextPermutation.referenceBasis (body_entries p.size count) Reference).symm))
    (allowAllocation : Bool := true) :
    ((placedCascade E points order allowAllocation).execute environment
      Reference original).quantumMarginal =
      DensityOperator.applyUnitary (placedTarget E points order Reference)
        original.quantumMarginal := by
  let coordinates := ContextPermutation.referenceBasis (body_entries p.size count) Reference
  obtain ⟨reversed, roundtrip⟩ :=
    ContextPermutation.state_surjective (body_entries p.size count) original
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    have mapped := permuted_marginal (body_entries p.size count) reversed
    rw [roundtrip] at mapped
    have back := congrArg (fun density => density.reindex coordinates.symm) mapped.symm
    rw [DensityOperator.reindex_trans, Equiv.self_trans_symm,
      DensityOperator.reindex_refl] at back
    exact back
  have originalSupport : cascadeSupport E points Reference order reversed.quantumMarginal := by
    rw [reversedMarginal]
    exact support
  have actual := placedCascade_marginal (environment := environment)
    (allowAllocation := allowAllocation) E points order reversed
  rw [roundtrip, cascade_density E points order reversed originalSupport false, reversedMarginal,
    DensityOperator.applyUnitary_reindex, DensityOperator.reindex_trans] at actual
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  rw [inverse, DensityOperator.reindex_refl] at actual
  exact actual

/-- The independently prescribed result includes the fixed factors and every point action. -/
def resultDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (Reference : Register)
    (input : DensityOperator (Register.prod (before p.size count).register Reference)) :
    DensityOperator (Register.prod (after p.size count).register Reference) :=
  DensityOperator.applyUnitary (placedTarget E points order Reference)
    (initializedDensity p count Reference input)

/-- The complete actual initialized cascade has the independent full-reference result. -/
lemma circuit_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : cascadeSupport E points Reference order
      ((initializedDensity p count Reference original.quantumMarginal).reindex
        (ContextPermutation.referenceBasis (body_entries p.size count) Reference).symm)) :
    ((circuit E points order).execute environment Reference original).quantumMarginal =
      resultDensity E points order Reference original.quantumMarginal := by
  have initializedSupport : cascadeSupport E points Reference order
      (((initializeWork p count).execute environment Reference original).quantumMarginal.reindex
        (ContextPermutation.referenceBasis (body_entries p.size count) Reference).symm) := by
    rw [initialize_density]
    exact support
  rw [circuit, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    placedCascade_density E points order _ initializedSupport, initialize_density]
  rfl

/-- One selected initialized call needs only its original supplied-coordinate domain. -/
lemma circuit_singleton_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (active : Fin count)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (before p.size count).register Reference).Index,
      ¬inputStepAdmissible E (points active) active input.1 →
        original.quantumMarginal.matrix input input = 0) :
    ((circuit E points [active]).execute environment Reference original).quantumMarginal =
      resultDensity E points [active] Reference original.quantumMarginal := by
  apply circuit_density
  refine ⟨?_, trivial⟩
  intro input outside
  rw [DensityOperator.reindex_entry]
  apply initializedDensity_support p count Reference original.quantumMarginal
    (inputStepAdmissible E (points active) active) (stepAdmissible E (points active) active)
    (initializedReadyBasis_admissible E (points active) active) support
  change ¬stepAdmissible E (points active) active
    ((ContextPermutation.basis (body_entries p.size count)).symm
      (ContextPermutation.basis (body_entries p.size count) input.1))
  rw [Equiv.symm_apply_apply]
  exact outside

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

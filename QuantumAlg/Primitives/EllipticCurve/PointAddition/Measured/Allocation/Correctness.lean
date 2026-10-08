/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Support
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Density
import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State
import all QuantumAlg.Core.Execution.MarginalLaws

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Runtime
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness

/-!
# Complete correctness of allocating measured affine point addition

One actual circuit prepares its own work, retains the original measurement
cells and executes the measured point-addition body. Its full quantum-reference
state equals the independently prescribed fixed preparation followed by the
original mathematical point action. Only supplied affine/control inputs carry
the original exclusions; internal prepared support follows from execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution MeasuredUncompute

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem permuted_marginal {source destination : RuntimeCtx .quantum}
    (same : source.entries.Perm destination.entries) {Reference : Register} {H : Type}
    [Fintype H] (original : State source Reference H) :
    (ContextPermutation.state same original).quantumMarginal =
      original.quantumMarginal.reindex (ContextPermutation.referenceBasis same Reference) := by
  rw [ContextPermutation.state, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

private theorem placed_body_marginal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((placedBody E Q).execute Reference
      (ContextPermutation.state (body_entries p.size) original)).quantumMarginal =
      ((body E Q).execute Reference original).quantumMarginal.reindex
        (ContextPermutation.referenceBasis (body_entries p.size) Reference) := by
  have actual := ContextPermutation.localCircuit_execute (body E Q) (body_isLocal E Q)
    (after p.size) (body_entries p.size) Reference original
  have marginal := congrArg
    (fun result : State (after p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × (H × (placedBody E Q).Path)) =>
      result.quantumMarginal) actual
  exact marginal.trans ((State.mapHistory_quantumMarginal _ _).trans (permuted_marginal _ _))

/-- The original independent mathematical point action on the actually allocated physical bank. -/
def placedTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) :
    UnitaryOperator (Register.prod (after p.size).register Reference) :=
  UnitaryOperator.reindex (ContextPermutation.referenceBasis (body_entries p.size) Reference)
    (target E Q Reference)

private theorem transport_action_of_source_support
    {source destination : RuntimeCtx .quantum}
    (same : source.entries.Perm destination.entries) (Reference : Register)
    {H : Type} [Fintype H] (domain : source.register.Index → Prop)
    (operator : UnitaryOperator (Register.prod source.register Reference))
    (sourceAction : State source Reference H →
      DensityOperator (Register.prod source.register Reference))
    (destinationAction : State destination Reference H →
      DensityOperator (Register.prod destination.register Reference))
    (natural : ∀ original, destinationAction (ContextPermutation.state same original) =
      (sourceAction original).reindex (ContextPermutation.referenceBasis same Reference))
    (correct : ∀ original, (∀ input : (Register.prod source.register Reference).Index,
      ¬domain input.1 → original.quantumMarginal.matrix input input = 0) →
        sourceAction original = DensityOperator.applyUnitary operator original.quantumMarginal)
    (original : State destination Reference H)
    (support : ∀ input : (Register.prod destination.register Reference).Index,
      ¬domain ((ContextPermutation.basis same).symm input.1) →
        original.quantumMarginal.matrix input input = 0) :
    destinationAction original = DensityOperator.applyUnitary
      (UnitaryOperator.reindex (ContextPermutation.referenceBasis same Reference) operator)
      original.quantumMarginal := by
  obtain ⟨preimage, rfl⟩ := ContextPermutation.state_surjective same original
  have originalSupport : ∀ input : (Register.prod source.register Reference).Index,
      ¬domain input.1 → preimage.quantumMarginal.matrix input input = 0 := by
    intro input outside
    have targetOutside : ¬domain ((ContextPermutation.basis same).symm
        (ContextPermutation.referenceBasis same Reference input).1) := by
      change ¬domain ((ContextPermutation.basis same).symm
        (ContextPermutation.basis same input.1))
      simpa only [Equiv.symm_apply_apply] using outside
    have observed := support (ContextPermutation.referenceBasis same Reference input) targetOutside
    rw [permuted_marginal, DensityOperator.reindex_entry] at observed
    simpa only [Equiv.symm_apply_apply] using observed
  have native := correct preimage originalSupport
  calc
    _ = (sourceAction preimage).reindex (ContextPermutation.referenceBasis same Reference) :=
      natural preimage
    _ = (DensityOperator.applyUnitary operator preimage.quantumMarginal).reindex
        (ContextPermutation.referenceBasis same Reference) :=
      congrArg (fun density : DensityOperator (Register.prod source.register Reference) =>
        density.reindex (ContextPermutation.referenceBasis same Reference)) native
    _ = DensityOperator.applyUnitary
        (UnitaryOperator.reindex (ContextPermutation.referenceBasis same Reference) operator)
        (preimage.quantumMarginal.reindex (ContextPermutation.referenceBasis same Reference)) :=
      DensityOperator.applyUnitary_reindex _ _ _
    _ = _ := congrArg (DensityOperator.applyUnitary
      (UnitaryOperator.reindex (ContextPermutation.referenceBasis same Reference) operator))
        (permuted_marginal same preimage).symm

/-- Actual placed execution has the complete point action on its internally established domain. -/
theorem placedBody_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (after p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (after p.size).register Reference).Index,
      ¬admissible E Q ((ContextPermutation.basis (body_entries p.size)).symm input.1) →
        original.quantumMarginal.matrix input input = 0) :
    ((placedBody E Q).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (placedTarget E Q Reference) original.quantumMarginal :=
  transport_action_of_source_support (body_entries p.size) Reference (admissible E Q)
    (target E Q Reference) (fun state => ((body E Q).execute Reference state).quantumMarginal)
    (fun state => ((placedBody E Q).execute Reference state).quantumMarginal)
    (fun state => placed_body_marginal E Q state)
    (fun state allowed => body_density E Q state allowed) original support

/-- Independent full-reference result retains prescribed work and the mathematical point action. -/
def resultDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (input : DensityOperator (Register.prod (before p.size).register Reference)) :
    DensityOperator (Register.prod (after p.size).register Reference) :=
  DensityOperator.applyUnitary (placedTarget E Q Reference) (initializedDensity p Reference input)

private theorem sequence_marginal {first middle last : RuntimeCtx .quantum}
    (prefixCode : Circuit (.quantum AlgorithmGate.model .empty) first middle)
    (bodyCode : Circuit (.quantum AlgorithmGate.model .empty) middle last)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State first Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    ((prefixCode.seq bodyCode).execute Reference original).quantumMarginal =
      (bodyCode.execute Reference (prefixCode.execute Reference original)).quantumMarginal := by
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]

/-- The complete actual circuit proves the original point contract without a caller work premise. -/
theorem circuit_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (before p.size).register Reference).Index,
      ¬inputAdmissible E Q input.1 → original.quantumMarginal.matrix input input = 0) :
    ((circuit E Q).execute Reference original).quantumMarginal =
      resultDensity E Q Reference original.quantumMarginal :=
  (sequence_marginal (initializeWork p) (placedBody E Q) original).trans
    ((placedBody_density E Q ((initializeWork p).execute Reference original)
      (initialize_support E Q original support)).trans
        (congrArg (DensityOperator.applyUnitary (placedTarget E Q Reference))
          (initialize_density p original)))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

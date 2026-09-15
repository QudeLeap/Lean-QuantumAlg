/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Support
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Density

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
    (original : State (context p.size) Reference H) :
    ((placedBody E Q).execute Reference
      (ContextPermutation.state (body_entries p.size) original)).quantumMarginal =
      ((body E Q).execute Reference original).quantumMarginal.reindex
        (ContextPermutation.referenceBasis (body_entries p.size) Reference) := by
  have actual := ContextPermutation.localCircuit_execute (body E Q) (body_isLocal E Q)
    (after p.size) (body_entries p.size) Reference original
  have marginal := congrArg
    (fun result : State (after p.size) Reference (H × (placedBody E Q).Path) =>
      result.quantumMarginal) actual
  exact marginal.trans ((State.mapHistory_quantumMarginal _ _).trans (permuted_marginal _ _))

/-- The original independent mathematical point action on the actually allocated physical bank. -/
def placedTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) :
    UnitaryOperator (Register.prod (after p.size).register Reference) :=
  UnitaryOperator.reindex (ContextPermutation.referenceBasis (body_entries p.size) Reference)
    (target E Q Reference)

/-- Actual placed execution has the complete point action on its internally established domain. -/
theorem placedBody_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (after p.size) Reference H)
    (support : ∀ input : (Register.prod (after p.size).register Reference).Index,
      ¬admissible E Q ((ContextPermutation.basis (body_entries p.size)).symm input.1) →
        original.quantumMarginal.matrix input input = 0) :
    ((placedBody E Q).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (placedTarget E Q Reference) original.quantumMarginal := by
  let coordinates := ContextPermutation.referenceBasis (body_entries p.size) Reference
  let labels := ContextPermutation.recordEquiv (body_entries p.size) H
  let reversed : State (context p.size) Reference H :=
    (original.mapClassical labels.symm).reindex coordinates.symm
  have roundtrip : ContextPermutation.state (body_entries p.size) reversed = original :=
    ExecutionState.coordinate_transport_inverse original labels.symm coordinates.symm
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    dsimp only [reversed]
    rw [reindex_marginal, ExecutionState.mapClassical_quantumMarginal]
  have originalSupport :
      ∀ input : (Register.prod (context p.size).register Reference).Index,
        ¬admissible E Q input.1 → reversed.quantumMarginal.matrix input input = 0 := by
    intro input outside
    rw [reversedMarginal, DensityOperator.reindex_entry]
    apply support (coordinates input)
    change ¬admissible E Q
      ((ContextPermutation.basis (body_entries p.size)).symm
        (ContextPermutation.basis (body_entries p.size) input.1))
    rw [Equiv.symm_apply_apply]
    exact outside
  have actual := placed_body_marginal E Q reversed
  rw [roundtrip, body_density E Q reversed originalSupport, reversedMarginal,
    DensityOperator.applyUnitary_reindex, DensityOperator.reindex_trans] at actual
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  rw [inverse, DensityOperator.reindex_refl] at actual
  exact actual

/-- Independent full-reference result retains prescribed work and the mathematical point action. -/
def resultDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (input : DensityOperator (Register.prod (before p.size).register Reference)) :
    DensityOperator (Register.prod (after p.size).register Reference) :=
  DensityOperator.applyUnitary (placedTarget E Q Reference) (initializedDensity p Reference input)

private theorem sequence_marginal {first middle last : RuntimeCtx .quantum}
    (prefixCode : Circuit first middle) (bodyCode : Circuit middle last)
    {Reference : Register} {H : Type} [Fintype H] (original : State first Reference H) :
    ((prefixCode.seq bodyCode).execute Reference original).quantumMarginal =
      (bodyCode.execute Reference (prefixCode.execute Reference original)).quantumMarginal := by
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]

/-- The complete actual circuit proves the original point contract without a caller work premise. -/
theorem circuit_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size) Reference H)
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

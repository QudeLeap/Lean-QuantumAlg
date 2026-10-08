/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Framing.Correctness

/-!
# Complete indexed point action in the common measured workspace

The indexed step acts on its original prepared affine domain in the actual
common context. Its independent point target retains all other exponent
systems, arithmetic systems and external references in the full joint state.
No independence premise is placed on those resident systems or finite stores.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem permuted_marginal {source target : RuntimeCtx .quantum}
    (same : source.entries.Perm target.entries) {Reference : Register} {H : Type} [Fintype H]
    (original : State source Reference H) :
    (ContextPermutation.state same original).quantumMarginal =
      original.quantumMarginal.reindex (ContextPermutation.referenceBasis same Reference) := by
  rw [ContextPermutation.state, MeasuredPointAddition.reindex_marginal,
    ExecutionState.mapClassical_quantumMarginal]

/-- The original prepared point domain is read at the selected exponent in the common context. -/
def stepAdmissible {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (input : (readyContext p.size count).register.Index) : Prop :=
  MeasuredPointAddition.Placement.Framing.admissible E Q (storageMap p.size active)
    (physicalMap p.size active) (ambientContext p.size active) (ambient_disjoint p.size active)
    ((ContextPermutation.basis (framed_entries p.size active)).symm input)

/-- The independent full point action keeps the common resident and external reference systems. -/
def stepTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register) :
    UnitaryOperator (Register.prod (readyContext p.size count).register Reference) :=
  UnitaryOperator.reindex
    (ContextPermutation.referenceBasis (framed_entries p.size active) Reference)
    (MeasuredPointAddition.Placement.Framing.target E Q (storageMap p.size active)
      (physicalMap p.size active) (ambientContext p.size active)
      (ambient_disjoint p.size active) Reference)

private theorem step_marginal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State ((MeasuredPointAddition.Placement.context p.size
      (storageMap p.size active) (physicalMap p.size active)).disjointUnion
        (ambientContext p.size active) (ambient_disjoint p.size active)) Reference
          (ClassicalOracleModel.empty.HiddenState × H)) :
    ((step E Q active).execute Reference
      (ContextPermutation.state (framed_entries p.size active) original)).quantumMarginal =
        ((residentBody E Q active).execute Reference original).quantumMarginal.reindex
          (ContextPermutation.referenceBasis (framed_entries p.size active) Reference) := by
  have actual := step_execute E Q active original
  have marginal := congrArg
    (fun result : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × (H × (step E Q active).Path)) =>
        result.quantumMarginal) actual
  exact marginal.trans ((State.mapHistory_quantumMarginal _ _).trans
    (permuted_marginal (framed_entries p.size active) _))

/-- The actual indexed step realizes the full point target on exactly its original domain. -/
theorem step_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (readyContext p.size count).register Reference).Index,
      ¬stepAdmissible E Q active input.1 → original.quantumMarginal.matrix input input = 0) :
    ((step E Q active).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (stepTarget E Q active Reference) original.quantumMarginal := by
  let coordinates := ContextPermutation.referenceBasis (framed_entries p.size active) Reference
  obtain ⟨reversed, roundtrip⟩ :=
    ContextPermutation.state_surjective (framed_entries p.size active) original
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    have mapped := permuted_marginal (framed_entries p.size active) reversed
    rw [roundtrip] at mapped
    have back := congrArg (fun density => density.reindex coordinates.symm) mapped.symm
    rw [DensityOperator.reindex_trans, Equiv.self_trans_symm,
      DensityOperator.reindex_refl] at back
    exact back
  have originalSupport : ∀ input,
      ¬MeasuredPointAddition.Placement.Framing.admissible E Q (storageMap p.size active)
        (physicalMap p.size active) (ambientContext p.size active)
        (ambient_disjoint p.size active) input.1 →
          reversed.quantumMarginal.matrix input input = 0 := by
    intro input outside
    rw [reversedMarginal, DensityOperator.reindex_entry]
    apply support (coordinates input)
    change ¬MeasuredPointAddition.Placement.Framing.admissible E Q (storageMap p.size active)
      (physicalMap p.size active) (ambientContext p.size active) (ambient_disjoint p.size active)
      ((ContextPermutation.basis (framed_entries p.size active)).symm
        (ContextPermutation.basis (framed_entries p.size active) input.1))
    rw [Equiv.symm_apply_apply]
    exact outside
  have actual := step_marginal E Q active reversed
  rw [roundtrip] at actual
  have pointAction := MeasuredPointAddition.Placement.Framing.body_density E Q
    (storageMap p.size active) (physicalMap p.size active) (ambientContext p.size active)
    (ambient_disjoint p.size active) reversed originalSupport
  change ((residentBody E Q active).execute Reference reversed).quantumMarginal = _ at pointAction
  rw [pointAction, reversedMarginal, DensityOperator.applyUnitary_reindex,
    DensityOperator.reindex_trans] at actual
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  rw [inverse, DensityOperator.reindex_refl] at actual
  exact actual

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Core.Execution.Context.Embedding.Relabeling

/-!
# Complete measured point action on mapped physical systems

The same measured point-addition body acts on injectively placed physical
systems and finite result cells. The original prepared affine/control domain
is read at the inverse physical coordinates. The independent mathematical
target has precisely the corresponding basis map, with arbitrary reference,
coherence, mixed input and classical history retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma relabeled_marginal {source : RuntimeCtx .quantum}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H] (original : State source Reference H) :
    (ContextRelabeling.state keys physical original).quantumMarginal =
      original.quantumMarginal.reindex
        (ContextRelabeling.referenceBasis (source := source) keys physical Reference) := by
  rw [ContextRelabeling.state, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

/-- Full measured execution follows the corresponding complete store and physical coordinates. -/
lemma body_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) (allowAllocation : Bool := true) :
    (body E Q keys physical allowAllocation).execute environment Reference
      (ContextRelabeling.state keys physical original) =
      ContextRelabeling.state keys physical
        ((MeasuredPointAddition.body E Q false).execute environment Reference original) :=
  Circuit.relabeling_embed_execute (environment := environment) keys physical
    (MeasuredPointAddition.body E Q false)
    Reference original

private lemma body_marginal {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((body E Q keys physical allowAllocation).execute environment Reference
      (ContextRelabeling.state keys physical original)).quantumMarginal =
        ((MeasuredPointAddition.body E Q false).execute environment Reference
          original).quantumMarginal.reindex
          (ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
            keys physical Reference) := by
  have actual := body_execute (environment := environment) E Q keys physical original
    allowAllocation
  have marginal := congrArg
    (fun result : State (context p.size keys physical) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (H × (body E Q keys physical allowAllocation).Path)) =>
        result.quantumMarginal) actual
  exact marginal.trans (relabeled_marginal keys physical _)

/-- Independent mathematical point action in the exact mapped physical-reference coordinates. -/
def target {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (Reference : Register) :
    UnitaryOperator (Register.prod (context p.size keys physical).register Reference) :=
  UnitaryOperator.reindex
    (ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
      keys physical Reference) (MeasuredPointAddition.target E Q Reference)

/-- Actual placed execution has the original complete point action on exactly its mapped domain. -/
lemma body_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size keys physical) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (context p.size keys physical).register Reference).Index,
      ¬MeasuredPointAddition.admissible E Q
        ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
          input.1) → original.quantumMarginal.matrix input input = 0)
    (allowAllocation : Bool := true) :
    ((body E Q keys physical allowAllocation).execute environment Reference
      original).quantumMarginal =
      DensityOperator.applyUnitary (target E Q keys physical Reference)
        original.quantumMarginal := by
  let coordinates :=
    ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
      keys physical Reference
  obtain ⟨reversed, roundtrip⟩ := ContextRelabeling.state_surjective keys physical original
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    have mapped := relabeled_marginal keys physical reversed
    rw [roundtrip] at mapped
    have back := congrArg (fun density => density.reindex coordinates.symm) mapped.symm
    rw [DensityOperator.reindex_trans, Equiv.self_trans_symm,
      DensityOperator.reindex_refl] at back
    exact back
  have originalSupport :
      ∀ input : (Register.prod (MeasuredPointAddition.context p.size).register Reference).Index,
        ¬MeasuredPointAddition.admissible E Q input.1 →
          reversed.quantumMarginal.matrix input input = 0 := by
    intro input outside
    rw [reversedMarginal, DensityOperator.reindex_entry]
    apply support (coordinates input)
    change ¬MeasuredPointAddition.admissible E Q
      ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
        (ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical input.1))
    rw [Equiv.symm_apply_apply]
    exact outside
  have transported :=
    (body_marginal (environment := environment)
      (allowAllocation := allowAllocation) E Q keys physical reversed).trans
    (congrArg (fun density => density.reindex coordinates)
      (MeasuredPointAddition.body_density E Q reversed originalSupport false))
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  calc
    ((body E Q keys physical allowAllocation).execute environment Reference
      original).quantumMarginal =
        (DensityOperator.applyUnitary (MeasuredPointAddition.target E Q Reference)
          reversed.quantumMarginal).reindex coordinates := by
      simpa only [roundtrip] using transported
    _ = DensityOperator.applyUnitary (target E Q keys physical Reference)
          original.quantumMarginal := by
      rw [reversedMarginal, DensityOperator.applyUnitary_reindex,
        DensityOperator.reindex_trans, inverse, DensityOperator.reindex_refl]
      rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement

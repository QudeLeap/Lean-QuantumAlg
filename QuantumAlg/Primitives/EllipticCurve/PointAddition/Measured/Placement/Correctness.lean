/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Core.Execution.Context.Relabeling.Local.State

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

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem relabeled_marginal {source : RuntimeCtx .quantum}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H] (original : State source Reference H) :
    (ContextRelabeling.state keys physical original).quantumMarginal =
      original.quantumMarginal.reindex
        (ContextRelabeling.referenceBasis (source := source) keys physical Reference) := by
  rw [ContextRelabeling.state, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

/-- Full measured execution follows the corresponding complete store and physical coordinates. -/
theorem body_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (MeasuredPointAddition.context p.size) Reference H) :
    (body E Q keys physical).execute Reference (ContextRelabeling.state keys physical original) =
      (ContextRelabeling.state keys physical
        ((MeasuredPointAddition.body E Q).execute Reference original)).mapHistory
          (fun record => (record.1, pathEquiv E Q keys physical record.2)) :=
  ContextRelabeling.localCircuit_execute _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical Reference original

private theorem body_marginal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (MeasuredPointAddition.context p.size) Reference H) :
    ((body E Q keys physical).execute Reference
      (ContextRelabeling.state keys physical original)).quantumMarginal =
        ((MeasuredPointAddition.body E Q).execute Reference original).quantumMarginal.reindex
          (ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
            keys physical Reference) := by
  have actual := body_execute E Q keys physical original
  have marginal := congrArg
    (fun result : State (context p.size keys physical) Reference
      (H × (body E Q keys physical).Path) => result.quantumMarginal) actual
  exact marginal.trans ((State.mapHistory_quantumMarginal _ _).trans
    (relabeled_marginal keys physical _))

/-- Independent mathematical point action in the exact mapped physical-reference coordinates. -/
def target {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (Reference : Register) :
    UnitaryOperator (Register.prod (context p.size keys physical).register Reference) :=
  UnitaryOperator.reindex
    (ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
      keys physical Reference) (MeasuredPointAddition.target E Q Reference)

/-- Actual placed execution has the original complete point action on exactly its mapped domain. -/
theorem body_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size keys physical) Reference H)
    (support : ∀ input : (Register.prod (context p.size keys physical).register Reference).Index,
      ¬MeasuredPointAddition.admissible E Q
        ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
          input.1) → original.quantumMarginal.matrix input input = 0) :
    ((body E Q keys physical).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (target E Q keys physical Reference)
        original.quantumMarginal := by
  let coordinates :=
    ContextRelabeling.referenceBasis (source := MeasuredPointAddition.context p.size)
      keys physical Reference
  let labels := ContextRelabeling.recordEquiv (source := MeasuredPointAddition.context p.size)
    keys physical H
  let reversed : State (MeasuredPointAddition.context p.size) Reference H :=
    (original.mapClassical labels.symm).reindex coordinates.symm
  have roundtrip : ContextRelabeling.state keys physical reversed = original :=
    ExecutionState.coordinate_transport_inverse original labels.symm coordinates.symm
  have reversedMarginal : reversed.quantumMarginal =
      original.quantumMarginal.reindex coordinates.symm := by
    dsimp only [reversed]
    rw [reindex_marginal, ExecutionState.mapClassical_quantumMarginal]
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
  have actual := body_marginal E Q keys physical reversed
  rw [roundtrip, MeasuredPointAddition.body_density E Q reversed originalSupport, reversedMarginal,
    DensityOperator.applyUnitary_reindex, DensityOperator.reindex_trans] at actual
  have inverse : coordinates.symm.trans coordinates = Equiv.refl _ :=
    Equiv.symm_trans_self coordinates
  rw [inverse, DensityOperator.reindex_refl] at actual
  exact actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement

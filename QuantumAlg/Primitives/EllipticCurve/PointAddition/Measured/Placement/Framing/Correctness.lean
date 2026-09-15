/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Framing
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Correctness

/-!
# Full point action with a physically resident correlated frame

The point target and its original prepared domain follow the actual mapped
physical systems inside the complete context union. The extra frame remains
resident and may be arbitrarily correlated with the point input or external
reference. Its full state is retained by the independent mathematical target,
while actual storage and native resource facts belong to the same framed code.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
namespace Framing

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem split_marginal (left right : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint left right) {Reference : Register} {H : Type}
    [Fintype H] (original : State (left.disjointUnion right separate) Reference H) :
    (ContextUnion.splitState left right separate original).quantumMarginal =
      original.quantumMarginal.reindex
        (ContextUnion.referenceBasis left right separate Reference) := by
  rw [ContextUnion.splitState, reindex_marginal, ExecutionState.mapClassical_quantumMarginal]

/-- The original point domain is read from its mapped systems inside the complete resident union. -/
def admissible {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (input : (context p.size keys physical frame separate).register.Index) : Prop :=
  MeasuredPointAddition.admissible E Q
    ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
      ((ContextUnion.unionBasisEquiv (Placement.context p.size keys physical) frame separate)
        input).1)

/-- Independent point action retains the actual frame and reference in their full joint basis. -/
def target {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (Reference : Register) :
    UnitaryOperator
      (Register.prod (context p.size keys physical frame separate).register Reference) :=
  UnitaryOperator.reindex
    (ContextUnion.referenceBasis (Placement.context p.size keys physical) frame separate
      Reference).symm (Placement.target E Q keys physical (Register.prod frame.register Reference))

/-- The same actual framed point body proves the full independent point action on its domain. -/
theorem body_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size keys physical frame separate) Reference H)
    (support : ∀ input :
      (Register.prod (context p.size keys physical frame separate).register Reference).Index,
      ¬admissible E Q keys physical frame separate input.1 →
        original.quantumMarginal.matrix input input = 0) :
    ((body E Q keys physical frame separate).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (target E Q keys physical frame separate Reference)
        original.quantumMarginal := by
  let coordinates := ContextUnion.referenceBasis
    (Placement.context p.size keys physical) frame separate Reference
  let splitInput := ContextUnion.splitState
    (Placement.context p.size keys physical) frame separate original
  have splitSupport : ∀ input :
      (Register.prod (Placement.context p.size keys physical).register
        (Register.prod frame.register Reference)).Index,
      ¬MeasuredPointAddition.admissible E Q
        ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
          input.1) → splitInput.quantumMarginal.matrix input input = 0 := by
    intro input outside
    dsimp only [splitInput]
    rw [split_marginal, DensityOperator.reindex_entry]
    apply support (coordinates.symm input)
    have returns := congrArg (fun value => value.1) (coordinates.apply_symm_apply input)
    change (ContextUnion.unionBasisEquiv (Placement.context p.size keys physical) frame separate
      (coordinates.symm input).1).1 = input.1 at returns
    change ¬MeasuredPointAddition.admissible E Q
      ((ContextRelabeling.basis (MeasuredPointAddition.context p.size) keys physical).symm
        ((ContextUnion.unionBasisEquiv (Placement.context p.size keys physical) frame separate)
          (coordinates.symm input).1).1)
    rw [returns]
    exact outside
  have execution := body_execute E Q keys physical frame separate original
  have marginal := congrArg (fun result : State (Placement.context p.size keys physical)
    (Register.prod frame.register Reference)
    (Store frame × (H × (body E Q keys physical frame separate).Path)) =>
      result.quantumMarginal) execution
  let histories := fun record : (Store frame × H) × (Placement.body E Q keys physical).Path =>
    (record.1.1, (record.1.2, ContextUnion.frameLocalPathEquiv _
      (Placement.body_isLocal E Q keys physical) frame separate record.2))
  have collapsed := marginal.trans (State.mapHistory_quantumMarginal
    ((Placement.body E Q keys physical).execute (Register.prod frame.register Reference) splitInput)
    histories)
  rw [Placement.body_density E Q keys physical splitInput splitSupport,
    split_marginal, split_marginal] at collapsed
  have result := congrArg (fun density => density.reindex coordinates.symm) collapsed
  rw [DensityOperator.applyUnitary_reindex, DensityOperator.reindex_trans,
    DensityOperator.reindex_trans] at result
  have inverse : coordinates.trans coordinates.symm = Equiv.refl _ :=
    Equiv.self_trans_symm coordinates
  rw [inverse, DensityOperator.reindex_refl] at result
  exact result

end

end Framing
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement

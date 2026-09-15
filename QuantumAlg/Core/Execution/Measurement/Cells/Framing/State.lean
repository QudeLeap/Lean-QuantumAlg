/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Framing
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Joint-state preservation of actual framed cell allocation

The existing retained-cell instructions preserve the complete quantum matrix
of both resident contexts jointly with the external reference. Borrowed
classical and quantum observations are restored separately. The new classical
cells remain real resident storage; no quantum system is prepared by them.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- The original complete quantum basis is unchanged by each actual classical retain. -/
def framedBasisEquiv (ctx frame : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame) →
      (ctx.disjointUnion frame
        (original_disjoint ctx frame dimension count separate)).register.Index ≃
        ((context ctx dimension count).disjointUnion frame separate).register.Index
  | 0, _ => Equiv.refl _
  | count + 1, separate =>
      framedBasisEquiv ctx frame dimension count
        (retained_disjoint (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh separate)

/-- Both original resident quantum contexts remain joint with the untouched external reference. -/
def framedJointBasisEquiv (ctx frame : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    (Reference : Register) :
    (Register.prod
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate)).register
      Reference).Index ≃
        (Register.prod ((context ctx dimension count).disjointUnion frame separate).register
          Reference).Index :=
  (framedBasisEquiv ctx frame dimension count separate).prodCongr (Equiv.refl Reference.Index)

/-- The complete quantum/reference matrix is preserved by the actual retained allocations. -/
theorem allocateFramed_quantumMarginal (ctx frame : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate))
      Reference H) :
    ((allocateFramed ctx frame dimension count separate).execute Reference state).quantumMarginal =
      state.quantumMarginal.reindex (framedJointBasisEquiv ctx frame dimension count separate
        Reference) := by
  induction count with
  | zero =>
      rw [allocateFramed, Circuit.execute_id, State.skip_quantumMarginal]
      exact (DensityOperator.reindex_refl state.quantumMarginal).symm
  | succ count ih =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      change ((Circuit.seq (allocateFramed ctx frame dimension count prefixSeparate)
        (.retain (middle.disjointUnion frame prefixSeparate) middle.canonicalFreshKey
          (.finite dimension) (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
            middle.canonicalFreshKey_fresh separate))).execute Reference state).quantumMarginal = _
      rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]
      change (State.retain
        ((allocateFramed ctx frame dimension count prefixSeparate).execute Reference state)
        middle.canonicalFreshKey (.finite dimension)
        (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
          middle.canonicalFreshKey_fresh separate)).quantumMarginal = _
      rw [State.retain_quantumMarginal]
      exact ih prefixSeparate state

/-- Actual allocation restores the full borrowed classical-quantum-reference observation. -/
theorem allocateFramed_borrowedRestored (ctx frame : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (context ctx dimension count) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State
      (ctx.disjointUnion frame (original_disjoint ctx frame dimension count separate))
      Reference H) :
    (allocateFramed ctx frame dimension count separate).BorrowedRestored Reference state
      ((allocateFramed ctx frame dimension count separate).execute Reference state) := by
  induction count with
  | zero =>
      change observeBorrowed Reference state.skip = observeBorrowed Reference state
      exact observeBorrowed_mapHistory state (fun history => (history, ()))
  | succ count ih =>
      let middle := context ctx dimension count
      let prefixSeparate := retained_disjoint middle.canonicalFreshKey (.finite dimension)
        middle.canonicalFreshKey_fresh separate
      exact Circuit.borrowedRestored_seq _ _ state (ih prefixSeparate state)
        (Circuit.borrowedRestored_retain middle.canonicalFreshKey (.finite dimension)
          (retained_fresh_union middle.canonicalFreshKey (.finite dimension)
            middle.canonicalFreshKey_fresh separate)
          ((allocateFramed ctx frame dimension count prefixSeparate).execute Reference state))

end

end QuantumAlg.Execution.MeasurementCells

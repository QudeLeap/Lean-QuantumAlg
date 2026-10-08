/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Store
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained.Semantics

/-!
# Complete persistent allocation state and caller frame

Actual retain instructions initialize all seven destinations and preserve every
original structural read, complete quantum-reference block and prior history.
Canonical key uniqueness discharges separation without a caller layout premise.
No execution or interpretation of a candidate is part of this allocation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Apply precisely the actual seven-cell allocation record to every incoming state block. -/
def persistentAllocationState (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (History × (retainPersistent ctx width scalarWidth).Path)) :=
  state.mapClassical (fun entry =>
    ((persistentAllocationStep width scalarWidth entry.1).1,
      (entry.2.1, (entry.2.2, (persistentAllocationStep width scalarWidth entry.1).2))))

private theorem retain2_execute (ctx : RuntimeCtx model.kind) (s0 s1 : CShape)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    let c1 := ctx.addRetained ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh
    (Circuit.seq (.retain ctx ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh) (.retain c1
      c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh)).execute Reference state =
      state.mapClassical (fun entry => (((entry.1).pushRetained ctx.canonicalFreshKey s0
      ctx.canonicalFreshKey_fresh).pushRetained c1.canonicalFreshKey s1
      c1.canonicalFreshKey_fresh, (entry.2.1, (entry.2.2, ((), ()))))) := by
  dsimp only
  erw [Circuit.execute_seq, Circuit.execute_retain, Circuit.execute_retain]
  simp only [State.mapHistory]
  exact three_maps_eq _ _ _ _ state _ _ _

private theorem retain3_execute (ctx : RuntimeCtx model.kind) (s0 s1 s2 : CShape)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    let c1 := ctx.addRetained ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh
    let c2 := c1.addRetained c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh
    (Circuit.seq (.retain ctx ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh) (Circuit.seq
      (.retain c1 c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh) (.retain c2
      c2.canonicalFreshKey s2 c2.canonicalFreshKey_fresh))).execute Reference state =
      state.mapClassical (fun entry => ((((entry.1).pushRetained ctx.canonicalFreshKey s0
      ctx.canonicalFreshKey_fresh).pushRetained c1.canonicalFreshKey s1
      c1.canonicalFreshKey_fresh).pushRetained c2.canonicalFreshKey s2
      c2.canonicalFreshKey_fresh, (entry.2.1, (entry.2.2, ((), ((), ())))))) := by
  dsimp only
  erw [Circuit.execute_seq, Circuit.execute_retain, retain2_execute]
  simp only [State.mapHistory]
  exact three_maps_eq _ _ _ _ state _ _ _

private theorem retain4_execute (ctx : RuntimeCtx model.kind) (s0 s1 s2 s3 : CShape)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    let c1 := ctx.addRetained ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh
    let c2 := c1.addRetained c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh
    let c3 := c2.addRetained c2.canonicalFreshKey s2 c2.canonicalFreshKey_fresh
    (Circuit.seq (.retain ctx ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh) (Circuit.seq
      (.retain c1 c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh) (Circuit.seq (.retain c2
      c2.canonicalFreshKey s2 c2.canonicalFreshKey_fresh) (.retain c3 c3.canonicalFreshKey s3
      c3.canonicalFreshKey_fresh)))).execute Reference state =
      state.mapClassical (fun entry => (((((entry.1).pushRetained ctx.canonicalFreshKey s0
      ctx.canonicalFreshKey_fresh).pushRetained c1.canonicalFreshKey s1
      c1.canonicalFreshKey_fresh).pushRetained c2.canonicalFreshKey s2
      c2.canonicalFreshKey_fresh).pushRetained c3.canonicalFreshKey s3
      c3.canonicalFreshKey_fresh, (entry.2.1, (entry.2.2, ((), ((), ((), ()))))))) := by
  dsimp only
  erw [Circuit.execute_seq, Circuit.execute_retain, retain3_execute]
  simp only [State.mapHistory]
  exact three_maps_eq _ _ _ _ state _ _ _

private theorem retain5_execute (ctx : RuntimeCtx model.kind) (s0 s1 s2 s3 s4 : CShape)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    let c1 := ctx.addRetained ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh
    let c2 := c1.addRetained c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh
    let c3 := c2.addRetained c2.canonicalFreshKey s2 c2.canonicalFreshKey_fresh
    let c4 := c3.addRetained c3.canonicalFreshKey s3 c3.canonicalFreshKey_fresh
    (Circuit.seq (.retain ctx ctx.canonicalFreshKey s0 ctx.canonicalFreshKey_fresh) (Circuit.seq
      (.retain c1 c1.canonicalFreshKey s1 c1.canonicalFreshKey_fresh) (Circuit.seq (.retain c2
      c2.canonicalFreshKey s2 c2.canonicalFreshKey_fresh) (Circuit.seq (.retain c3
      c3.canonicalFreshKey s3 c3.canonicalFreshKey_fresh) (.retain c4 c4.canonicalFreshKey s4
      c4.canonicalFreshKey_fresh))))).execute Reference state =
      state.mapClassical (fun entry => ((((((entry.1).pushRetained ctx.canonicalFreshKey s0
      ctx.canonicalFreshKey_fresh).pushRetained c1.canonicalFreshKey s1
      c1.canonicalFreshKey_fresh).pushRetained c2.canonicalFreshKey s2
      c2.canonicalFreshKey_fresh).pushRetained c3.canonicalFreshKey s3
      c3.canonicalFreshKey_fresh).pushRetained c4.canonicalFreshKey s4
      c4.canonicalFreshKey_fresh,
        (entry.2.1, (entry.2.2, ((), ((), ((), ((), ())))))))) := by
  dsimp only
  erw [Circuit.execute_seq, Circuit.execute_retain, retain4_execute]
  simp only [State.mapHistory]
  exact three_maps_eq _ _ _ _ state _ _ _

private theorem persistentPrefix_execute (ctx : RuntimeCtx model.kind) (scalarWidth : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (retainPersistentPrefix ctx scalarWidth).execute Reference state =
      state.mapClassical (fun entry => ((((((entry.1).pushRetained ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh).pushRetained (persistentLatchCtx ctx).canonicalFreshKey
      (.unsignedWord scalarWidth)
      (persistentLatchCtx ctx).canonicalFreshKey_fresh).pushRetained (persistentSelectedCtx ctx
      scalarWidth).canonicalFreshKey .bit
      (persistentSelectedCtx ctx scalarWidth).canonicalFreshKey_fresh).pushRetained
      (persistentInverseCtx ctx scalarWidth).canonicalFreshKey (.unsignedWord scalarWidth)
      (persistentInverseCtx ctx scalarWidth).canonicalFreshKey_fresh).pushRetained
      (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey .bit
      (persistentCandidateCtx ctx scalarWidth).canonicalFreshKey_fresh,
        (entry.2.1, (entry.2.2, ((), ((), ((), ((), ())))))))) := by
  exact retain5_execute ctx .bit (.unsignedWord scalarWidth) .bit
    (.unsignedWord scalarWidth) .bit Reference state

private theorem persistentTwoMaps_eq {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] {R : Register}
    (firstDecision : DecidableEq B) (secondDecision finalDecision : DecidableEq C)
    (state : ExecutionState A R) (first : A → B) (second : B → C) :
    @ExecutionState.mapClassical B C _ _ R secondDecision
      (@ExecutionState.mapClassical A B _ _ R firstDecision state first) second =
        @ExecutionState.mapClassical A C _ _ R finalDecision state (second ∘ first) := by
  let : DecidableEq B := firstDecision
  let : DecidableEq C := secondDecision
  rw [ExecutionState.executionState_mapClassical_comp]
  exact (Circuit.mapClassical_canonicalDecision secondDecision state _).trans
    (Circuit.mapClassical_canonicalDecision finalDecision state _).symm

private theorem retainedHistory_execute (ctx : RuntimeCtx model.kind) (width : Nat)
    (Reference : Register) {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference (model.HiddenState × (H × K))) :
    ((retainOutputs ctx width).execute Reference state).mapHistory
      (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) =
        state.mapClassical (fun entry =>
          (retainedInitialStore width entry.1,
            (entry.2.1, (entry.2.2.1, (entry.2.2.2, ((), ())))))) := by
  erw [retainOutputs_execute]
  simp only [State.mapHistory]
  exact persistentTwoMaps_eq _ _ _ state _ _

private theorem retainedPair_after (pre middle : RuntimeCtx model.kind) (width : Nat)
    (first : Circuit model pre middle) (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    (Circuit.seq first (retainOutputs middle width)).execute Reference state =
      (first.execute Reference state).mapClassical (fun entry =>
        (retainedInitialStore width entry.1,
          (entry.2.1, (entry.2.2.1, (entry.2.2.2, ((), ())))))) := by
  have combined := Circuit.execute_seq first (retainOutputs middle width) state
  exact combined.trans (retainedHistory_execute middle width Reference
    (H := History) (K := first.Path) (first.execute Reference state))

/-- The complete actual allocator preserves arbitrary incoming quantum-reference correlations. -/
theorem retainPersistent_execute (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (retainPersistent ctx width scalarWidth).execute Reference state =
      persistentAllocationState ctx width scalarWidth Reference state := by
  have earlier := persistentPrefix_execute ctx scalarWidth Reference state
  have whole := retainedPair_after ctx (persistentBaseCtx ctx scalarWidth) width
    (retainPersistentPrefix ctx scalarWidth) Reference state
  conv at whole =>
    rhs
    arg 1
    rw [earlier]
  conv at whole =>
    rhs
    erw [persistentTwoMaps_eq _ _ (Classical.decEq _) state _ _]
  refine whole.trans ?_
  unfold persistentAllocationState
  exact (Circuit.mapClassical_canonicalDecision _ state _).symm


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Depth

/-!
# Native counts and depth of the actual reusable-bank repetition

The literal retain-then-round recursion executes its entire measured,
packed, reset and reloaded round once per chronological outcome. Its
independent native pool and serial depth are therefore the count times the
already proved per-round allowances. Retention contributes live storage,
accounted separately; it emits no native operation and prepares no quantum
system. The zero-round branch is the actual identity.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

noncomputable section

/-- Every native coordinate is counted once for each actual repeated round. -/
theorem shortDLP_runtimeRepetition_resourcePool_le {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat)
    (path : (code m ell width N generator target ctx sameWires parameter cells count).Path) :
    (code m ell width N generator target ctx sameWires parameter cells count).resourcePool path ≤
      count • RuntimeRound.eventEnvelope m ell width N := by
  induction count generalizing ctx with
  | zero =>
      change (0 : ResourcePool RuntimeRound.model) ≤ 0 • RuntimeRound.eventEnvelope m ell width N
      rw [zero_nsmul]
  | succ count ih =>
      let nextCtx := RuntimeResults.next m ell width ctx
      let nextWires :=
        (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
      let nextParameter := parameter.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let first := RuntimeRound.code m ell width nextWires nextParameter N generator target
        nextCells (RuntimeResults.head m ell width ctx)
      let later := code m ell width N generator target nextCtx nextWires nextParameter
        nextCells count
      change ResourcePool.ofList ([] ++ (first.eventTrace path.2.1 ++
        later.eventTrace path.2.2)) ≤ _
      rw [List.nil_append, ResourcePool.ofList_append]
      calc
        _ ≤ RuntimeRound.eventEnvelope m ell width N +
            count • RuntimeRound.eventEnvelope m ell width N :=
          add_le_add
            (RuntimeRound.shortDLP_runtimeRound_resourcePool_le m ell width nextWires
              nextParameter N generator target nextCells (RuntimeResults.head m ell width ctx)
              path.2.1)
            (ih nextCtx nextWires nextParameter nextCells path.2.2)
        _ = (count + 1) • RuntimeRound.eventEnvelope m ell width N := by
          rw [succ_nsmul]
          exact add_comm _ _

/-- Every actual dependency path includes each complete reset and reload before the next round. -/
theorem shortDLP_runtimeRepetition_unitDepth_le {shape : CShape} (m ell width N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
    (parameter : CInputRef ctx shape)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (count : Nat)
    (path : (code m ell width N generator target ctx sameWires parameter cells count).Path) :
    (code m ell width N generator target ctx sameWires parameter cells count).depth
      (fun _ => 1) path ≤ count * RuntimeRound.unitDepthBound m ell width N := by
  induction count generalizing ctx with
  | zero =>
      change 0 ≤ 0 * RuntimeRound.unitDepthBound m ell width N
      exact Nat.zero_le _
  | succ count ih =>
      let nextCtx := RuntimeResults.next m ell width ctx
      let nextWires :=
        (RuntimeResults.shortDLP_runtimeResult_next_wires m ell width ctx).trans sameWires
      let nextParameter := parameter.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let nextCells := fun index => (cells index).underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh
      let first := RuntimeRound.code m ell width nextWires nextParameter N generator target
        nextCells (RuntimeResults.head m ell width ctx)
      let later := code m ell width N generator target nextCtx nextWires nextParameter
        nextCells count
      have firstBound := RuntimeRound.shortDLP_runtimeRound_unitDepth_le m ell width nextWires
        nextParameter N generator target nextCells (RuntimeResults.head m ell width ctx) path.2.1
      have laterBound := ih nextCtx nextWires nextParameter nextCells path.2.2
      change 0 + (first.depth (fun _ => 1) path.2.1 +
        later.depth (fun _ => 1) path.2.2) ≤ _
      rw [Nat.zero_add, Nat.succ_mul]
      exact (Nat.add_le_add firstBound laterBound).trans_eq (Nat.add_comm _ _)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRepetition

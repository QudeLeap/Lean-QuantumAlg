/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Preparation
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources

/-!
# Native quantum time through the actual classical table stages

Zero quantum time follows from the actual event pool, while actual
parallel query layers retain their original dependency depth. Paid native
classical instructions remain present with their independent classical
weight; their existing quantum duration is zero.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- The original actual pool, with no gate or quantum-query occurrence, has zero quantum time. -/
lemma quantumTime_zero (code : Circuit model ctx ctx)
    (zero : ∀ focus : Resource.Event model,
      (∀ coordinate, focus ≠ .classicalOperation coordinate) →
      ∀ path, ResourcePool.count focus (code.resourcePool path) = 0)
    (path : code.Path) : code.quantumTime path = 0 := by
  have work : ResourcePool.weightedCount Resource.Event.quantumDuration
      (code.resourcePool path) = 0 := by
    apply ResourcePool.weightedCount_eq_zero_of_mem
    intro event present
    cases event with
    | classicalOperation coordinate => rfl
    | classicalQuery coordinate => rfl
    | preparation dimension => rfl
    | measurement dimension => rfl
    | gate coordinate =>
        have missing := zero (.gate coordinate) (fun _ same => by cases same) path
        exact False.elim ((Multiset.count_eq_zero.mp missing) present)
    | oracle coordinate =>
        have missing := zero (.oracle coordinate) (fun _ same => by cases same) path
        exact False.elim ((Multiset.count_eq_zero.mp missing) present)
  exact Nat.eq_zero_of_le_zero
    ((code.depth_le_weightedCount_of_pool_le Resource.Event.quantumDuration
      (code.resourcePool path) path le_rfl).trans_eq work)

/-- Sequential actual component depths add at the same chronological path. -/
lemma seq_depth_le (duration : Resource.Event model → Nat) (first second : Circuit model ctx ctx)
    (firstLimit secondLimit : Nat) (path : (first.seq second).Path)
    (left : first.depth duration path.1 ≤ firstLimit)
    (right : second.depth duration path.2 ≤ secondLimit) :
    (first.seq second).depth duration path ≤ firstLimit + secondLimit := by
  change first.depth duration path.1 + second.depth duration path.2 ≤ _
  exact Nat.add_le_add left right

/-- Actual finite chronological depths retain their original component depths. -/
lemma range_depth_le (duration : Resource.Event model → Nat) (count : Nat)
    (body : Fin count → Circuit model ctx ctx) (bound : Nat)
    (bounded : ∀ index path, (body index).depth duration path ≤ bound)
    (path : (Circuit.forRange count body).Path) :
    (Circuit.forRange count body).depth duration path ≤ count * bound := by
  induction count with
  | zero => simp [Circuit.forRange, Circuit.depth, Circuit.eventDepth]
  | succ count ih =>
      change (body 0).depth duration path.1 +
        (Circuit.forRange count (fun index => body index.succ)).depth duration path.2 ≤ _
      have first := bounded 0 path.1
      have rest := ih _ (fun index => bounded index.succ) path.2
      rw [Nat.succ_mul]
      omega

/-- Abstract real syntax keeps preparation paths separate from the finite stream bodies. -/
lemma preparedStreams_depth_le (duration : Resource.Event model → Nat)
    (first second : Circuit model ctx ctx) (streams windows : Nat)
    (full : Fin streams → Fin windows → Circuit model ctx ctx)
    (tail : Fin streams → Circuit model ctx ctx)
    (firstLimit secondLimit fullLimit tailLimit : Nat)
    (firstBound : ∀ path, first.depth duration path ≤ firstLimit)
    (secondBound : ∀ path, second.depth duration path ≤ secondLimit)
    (fullBound : ∀ stream window path, (full stream window).depth duration path ≤ fullLimit)
    (tailBound : ∀ stream path, (tail stream).depth duration path ≤ tailLimit)
    (path : (first.seq (second.seq (Circuit.forRange streams fun stream =>
      (Circuit.forRange windows (full stream)).seq (tail stream)))).Path) :
    (first.seq (second.seq (Circuit.forRange streams fun stream =>
      (Circuit.forRange windows (full stream)).seq (tail stream)))).depth duration path ≤
      firstLimit + (secondLimit + streams * (windows * fullLimit + tailLimit)) := by
  have current := range_depth_le duration streams
    (fun stream => (Circuit.forRange windows (full stream)).seq (tail stream))
    (windows * fullLimit + tailLimit) (fun stream chosen =>
      seq_depth_le duration _ _ _ _ chosen
        (range_depth_le duration windows (full stream) fullLimit (fullBound stream) chosen.1)
        (tailBound stream chosen.2)) path.2.2
  exact seq_depth_le duration _ _ _ _ path (firstBound path.1)
    (seq_depth_le duration _ _ _ _ path.2 (secondBound path.2.1) current)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.QuantumAccounting

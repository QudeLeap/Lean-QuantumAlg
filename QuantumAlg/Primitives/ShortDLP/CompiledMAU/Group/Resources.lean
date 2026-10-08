/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Exponentiation.Depth

/-!
# Native resources of the shared-workspace short-DLP group action

The two exponent registers select actual unit-multiplier stages on one
shared power and auxiliary pair. Register insertion and reassociation do
not introduce events. Independent coordinate budgets include every gate in
the native control expansion; a separate bound counts all occurrences.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- The first register embedding preserves the actual eventCost. -/
@[simp] theorem firstExponentiationProgram_eventCost (m ell width N : Nat) (g : (ZMod N)ˣ) :
    (firstExponentiationProgram m ell width N g).eventCost =
      (exponentiationProgram (ell + m) width N g).eventCost :=
  UnitaryCircuit.insertMiddle_eventCost (middleWidth := ell)
    (exponentiationProgram (ell + m) width N g)

/-- The second register embedding and reassociation preserve the actual eventCost. -/
@[simp] theorem secondExponentiationProgram_eventCost (m ell width N : Nat) (x : (ZMod N)ˣ) :
    (secondExponentiationProgram m ell width N x).eventCost =
      (exponentiationProgram ell width N x⁻¹).eventCost := by
  exact (castProgram_eventCost
    (Nat.add_assoc (firstBits (registerParameters m ell width)) ell (workspaceBits width)).symm
    (UnitaryCircuit.prodRight
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹))).trans
    (UnitaryCircuit.prodRight_eventCost
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹))

/-- The first register embedding preserves the actual eventDepth. -/
@[simp] theorem firstExponentiationProgram_eventDepth (m ell width N : Nat) (g : (ZMod N)ˣ) :
    (firstExponentiationProgram m ell width N g).eventDepth =
      (exponentiationProgram (ell + m) width N g).eventDepth :=
  UnitaryCircuit.insertMiddle_eventDepth (middleWidth := ell)
    (exponentiationProgram (ell + m) width N g)

/-- The second register embedding and reassociation preserve the actual eventDepth. -/
@[simp] theorem secondExponentiationProgram_eventDepth (m ell width N : Nat) (x : (ZMod N)ˣ) :
    (secondExponentiationProgram m ell width N x).eventDepth =
      (exponentiationProgram ell width N x⁻¹).eventDepth := by
  exact (castProgram_eventDepth
    (Nat.add_assoc (firstBits (registerParameters m ell width)) ell (workspaceBits width)).symm
    (UnitaryCircuit.prodRight
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹))).trans
    (UnitaryCircuit.prodRight_eventDepth
      (m := firstBits (registerParameters m ell width))
      (exponentiationProgram ell width N x⁻¹))

/-- Independent native coordinates of the first lifted selected-power fold. -/
def firstExponentiationEventEnvelope (m ell width N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  exponentiationEventEnvelope (ell + m) width N

/-- Independent native coordinates of the second lifted selected-power fold. -/
def secondExponentiationEventEnvelope (ell width N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  exponentiationEventEnvelope ell width N

theorem firstExponentiationProgram_eventCost_le (m ell width N : Nat) (g : (ZMod N)ˣ) :
    (firstExponentiationProgram m ell width N g).eventCost ≤
      firstExponentiationEventEnvelope m ell width N := by
  rw [firstExponentiationProgram_eventCost]
  exact exponentiationProgram_eventCost_le (ell + m) width N g

theorem secondExponentiationProgram_eventCost_le (m ell width N : Nat) (x : (ZMod N)ˣ) :
    (secondExponentiationProgram m ell width N x).eventCost ≤
      secondExponentiationEventEnvelope ell width N := by
  rw [secondExponentiationProgram_eventCost]
  exact exponentiationProgram_eventCost_le ell width N x⁻¹

/-- The two independently capped coordinate pools on their shared arithmetic workspace. -/
def compiledGroupActionEventEnvelope (m ell width N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  firstExponentiationEventEnvelope m ell width N + secondExponentiationEventEnvelope ell width N

/-- Cardinality of the two independent coordinate pools. -/
def groupActionPrimitiveBound (m ell width N : Nat) : Nat :=
  exponentiationPrimitiveBound (ell + m) width N + exponentiationPrimitiveBound ell width N

/-- Width-only ceiling for the sum of the independent coordinate caps. -/
def groupActionPrimitiveWidthBound (m ell width : Nat) : Nat :=
  exponentiationPrimitiveWidthBound (ell + m) width + exponentiationPrimitiveWidthBound ell width

@[simp] theorem compiledGroupActionEventEnvelope_card (m ell width N : Nat) :
    (compiledGroupActionEventEnvelope m ell width N).card =
      groupActionPrimitiveBound m ell width N := by
  simp only [compiledGroupActionEventEnvelope, Multiset.card_add,
    firstExponentiationEventEnvelope, secondExponentiationEventEnvelope,
    exponentiationEventEnvelope_card, groupActionPrimitiveBound]

theorem groupActionPrimitiveBound_le_widthBound (m ell width N : Nat) :
    groupActionPrimitiveBound m ell width N ≤ groupActionPrimitiveWidthBound m ell width :=
  Nat.add_le_add (exponentiationPrimitiveBound_le_widthBound (ell + m) width N)
    (exponentiationPrimitiveBound_le_widthBound ell width N)

theorem compiledGroupActionProgram_eventCost_le (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).eventCost ≤
      compiledGroupActionEventEnvelope m ell width N := by
  rw [compiledGroupActionProgram, UnitaryCircuit.seq_eventCost,
    compiledGroupActionEventEnvelope]
  exact ResourcePool.add_mono
    (firstExponentiationProgram_eventCost_le m ell width N g)
    (secondExponentiationProgram_eventCost_le m ell width N x)

/-- The event pool bound also bounds its total cardinality. -/
theorem compiledGroupActionProgram_eventCount_le (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).eventCost.card ≤
      groupActionPrimitiveBound m ell width N :=
  (Multiset.card_le_card
    (compiledGroupActionProgram_eventCost_le m ell width N g x)).trans_eq
      (compiledGroupActionEventEnvelope_card m ell width N)

/-- A tighter bound on actual occurrences, before independently capping every native coordinate. -/
def groupActionActualEventBound (m ell width : Nat) : Nat :=
  (m + 2 * ell) * MAU.Exponentiation.Gidney.stageEventBound width

theorem compiledGroupActionProgram_actual_event_bound
    (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).eventCost.card ≤
      groupActionActualEventBound m ell width := by
  rw [compiledGroupActionProgram, UnitaryCircuit.seq_eventCost, Multiset.card_add,
    firstExponentiationProgram_eventCost, secondExponentiationProgram_eventCost]
  have first := exponentiationProgram_actual_event_bound (ell + m) width N g
  have second := exponentiationProgram_actual_event_bound ell width N x⁻¹
  calc
    _ ≤ (ell + m) * MAU.Exponentiation.Gidney.stageEventBound width +
        ell * MAU.Exponentiation.Gidney.stageEventBound width := Nat.add_le_add first second
    _ = groupActionActualEventBound m ell width := by
      unfold groupActionActualEventBound
      ring

/-- The untouched middle word contributes no duration to the first member's envelope. -/
def firstExponentiationDepthEnvelope (m ell width N : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  exponentiationDepthEnvelope (ell + m) width N

/-- The untouched first word contributes no duration to the second member's envelope. -/
def secondExponentiationDepthEnvelope (ell width N : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  exponentiationDepthEnvelope ell width N

theorem firstExponentiationProgram_eventDepth_le (m ell width N : Nat) (g : (ZMod N)ˣ)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment (firstExponentiationProgram m ell width N g).eventDepth ≤
      DepthExpr.depthEval assignment (firstExponentiationDepthEnvelope m ell width N) := by
  rw [firstExponentiationProgram_eventDepth, firstExponentiationDepthEnvelope]
  exact exponentiationProgram_eventDepth_le (ell + m) width N g assignment

theorem secondExponentiationProgram_eventDepth_le (m ell width N : Nat) (x : (ZMod N)ˣ)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment (secondExponentiationProgram m ell width N x).eventDepth ≤
      DepthExpr.depthEval assignment (secondExponentiationDepthEnvelope ell width N) := by
  rw [secondExponentiationProgram_eventDepth, secondExponentiationDepthEnvelope]
  exact exponentiationProgram_eventDepth_le ell width N x⁻¹ assignment

/-- The two members execute sequentially on the same actual arithmetic words. -/
def compiledGroupActionDepthEnvelope (m ell width N : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  .seq (firstExponentiationDepthEnvelope m ell width N)
    (secondExponentiationDepthEnvelope ell width N)

theorem compiledGroupActionProgram_eventDepth_le (m ell width N : Nat) (g x : (ZMod N)ˣ)
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    DepthExpr.depthEval assignment (compiledGroupActionProgram m ell width N g x).eventDepth ≤
      DepthExpr.depthEval assignment (compiledGroupActionDepthEnvelope m ell width N) := by
  rw [compiledGroupActionProgram, UnitaryCircuit.seq_eventDepth,
    compiledGroupActionDepthEnvelope, DepthExpr.depthEval_seq]
  exact Nat.add_le_add
    (firstExponentiationProgram_eventDepth_le m ell width N g assignment)
    (secondExponentiationProgram_eventDepth_le m ell width N x assignment)

@[simp] theorem compiledGroupActionDepthEnvelope_unit (m ell width N : Nat) :
    DepthExpr.depthEval (fun _ => 1) (compiledGroupActionDepthEnvelope m ell width N) =
      groupActionPrimitiveBound m ell width N := by
  simp [compiledGroupActionDepthEnvelope, firstExponentiationDepthEnvelope,
    secondExponentiationDepthEnvelope, groupActionPrimitiveBound]

/-- Unit-duration depth of the actual serial group action is its actual event count. -/
theorem compiledGroupActionProgram_depth_eq_events (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).evaluatedEventDepth (fun _ => 1) =
      (compiledGroupActionProgram m ell width N g x).eventCost.card := by
  change DepthExpr.depthEval (fun _ => 1)
    (compiledGroupActionProgram m ell width N g x).eventDepth = _
  simp only [compiledGroupActionProgram, UnitaryCircuit.seq_eventDepth,
    UnitaryCircuit.seq_eventCost, Multiset.card_add, DepthExpr.depthEval_seq,
    firstExponentiationProgram_eventDepth, firstExponentiationProgram_eventCost,
    secondExponentiationProgram_eventDepth, secondExponentiationProgram_eventCost]
  exact congrArg₂ Nat.add (exponentiationProgram_depth_eq_events (ell + m) width N g)
    (exponentiationProgram_depth_eq_events ell width N x⁻¹)

/-- The actual serial depth obeys the same tighter total-occurrence bound. -/
theorem compiledGroupActionProgram_actual_depth_bound
    (m ell width N : Nat) (g x : (ZMod N)ˣ) :
    (compiledGroupActionProgram m ell width N g x).evaluatedEventDepth (fun _ => 1) ≤
      groupActionActualEventBound m ell width := by
  rw [compiledGroupActionProgram_depth_eq_events]
  exact compiledGroupActionProgram_actual_event_bound m ell width N g x

end

end QuantumAlg.ShortDLP.CompiledMAU

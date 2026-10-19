/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# Complete events of the actual streaming stage

The native preparation, literal point body, actual stored feedback and final
measured same-cell correction retain their original complete paths. Feedback
reads only earlier indices in the same exponent bank. An injection into the
bank's residue positions bounds its gate allowance by the bank width, including
arbitrary stored bits and every syntactic branch outcome.

The complete coordinatewise pool retains all native gates and the real readout
measurement. It adds no allocation events. No input state or cleanliness premise is
used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage.Events

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

def single : ResourcePool Model := ResourcePool.singleton (.gate .singleQubit)

def cnot : ResourcePool Model := ResourcePool.singleton (.gate .cnot)

def measured : ResourcePool Model := ResourcePool.singleton (.measurement (2 : ℕ+))

/-- Independent complete event allowance for one actual preparation/point/readout stage. -/
def stageBudget (width m : Nat) : ResourcePool Model :=
  MeasuredPointAddition.events width + ((m + 9) • single + 4 • cnot + measured)

private lemma repeat_mono {small large : Nat} (bounded : small ≤ large)
    (pool : ResourcePool Model) : small • pool ≤ large • pool := by
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [ResourcePool.count_nsmul, ResourcePool.count_nsmul]
  exact Nat.mul_le_mul_right _ bounded

private lemma native_program_pool (gates : List Recovery.Point.Extension.Gate) :
    (Recovery.Point.Program.program gates).eventCost =
      Recovery.Point.Extension.oneQubitCount gates • single + Recovery.Point.Extension.cnotCount
        gates • cnot := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, Recovery.Point.Program.program_trace]
  induction gates with
  | nil => simp [Recovery.Point.Extension.oneQubitCount, Recovery.Point.Extension.cnotCount]
  | cons gate tail ih =>
      cases gate <;>
        simp [List.map_cons, ResourcePool.ofList_cons, Recovery.Point.Program.event,
          Recovery.Point.Extension.oneQubitCount, Recovery.Point.Extension.cnotCount,
          Recovery.Point.Extension.Gate.isCnot, List.filter_cons, ih, single, cnot,
          add_nsmul, add_comm, add_left_comm]; ac_rfl

/-- The actual placed two-wire preparation uses at most seven one-qubit and four CNOT gates. -/
lemma preparation_budget (width m r remaining : Nat) :
    (Recovery.Layout.preparation width m r remaining).eventCost ≤ 7 • single + 4 • cnot := by
  let half := 2 ^ remaining
  let cut := r % (2 * half)
  have within : cut < 2 * half := Nat.mod_lt r (by dsimp [half]; positivity)
  let gates := Recovery.Point.Extension.fixedGates half cut within
  have counts := Recovery.Point.Program.fixed_native_counts half cut within
  rw [(Recovery.Point.Program.program_counts gates).1, (Recovery.Point.Program.program_counts
    gates).2] at counts
  have bounded : Recovery.Point.Extension.oneQubitCount gates ≤ 7 ∧
      Recovery.Point.Extension.cnotCount gates ≤ 4 := by
    split_ifs at counts <;> simp only [Prod.mk.injEq] at counts <;> omega
  rw [Recovery.Layout.preparation, UnitaryCircuit.placeAt_eventCost]
  change (Recovery.Point.Program.program gates).eventCost ≤ _
  rw [native_program_pool]
  exact add_le_add (repeat_mono bounded.1 single) (repeat_mono bounded.2 cnot)

private lemma phaseProgram_budget (width m : Nat) (previous current : Fin (2 * m))
    (value : CShape.Value (.finite 2)) :
    (phaseProgram width m previous current value).eventCost ≤ single := by
  cases value with
  | finite bit =>
      change (if bit.val = 1 then
        Gate.singleQubitAt (Context width m).quantumLayout .empty
          (phaseGateOp (-(QuantumFourierTransform.Source.phaseAngle
            (current.val - previous.val - 1))))
          (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)
        else UnitaryCircuit.identity AlgorithmGate.model .empty
          (Context width m).quantumLayout).eventCost ≤ single
      split_ifs
      · rw [Gate.singleQubitAt_eventCost]
        exact le_rfl
      · change (0 : ResourcePool Model) ≤ single
        exact zero_le

private lemma conditional_pool_bound {model : ExecutionModel}
    {ctx : RuntimeCtx model.kind} {allowAllocation : Bool}
    (condition : Prop) (codeDecision boundDecision : Decidable condition)
    (first second : Circuit model ctx ctx allowAllocation)
    (firstBound secondBound : ResourcePool model)
    (positive : ∀ path, first.resourcePool path ≤ firstBound)
    (negative : ∀ path, second.resourcePool path ≤ secondBound) :
    ∀ path : (@ite (Circuit model ctx ctx allowAllocation) condition codeDecision
        first second).Path,
      (@ite (Circuit model ctx ctx allowAllocation) condition codeDecision
        first second).resourcePool path ≤
          @ite (ResourcePool model) condition boundDecision firstBound secondBound := by
  cases codeDecision with
  | isTrue applicable =>
      cases boundDecision with
      | isTrue _ => exact positive
      | isFalse contrary => exact False.elim (contrary applicable)
  | isFalse inapplicable =>
      cases boundDecision with
      | isTrue contrary => exact False.elim (inapplicable contrary)
      | isFalse _ => exact negative

private lemma feedbackOne_budget (width m : Nat) (previous current : Fin (2 * m))
    (path : (feedbackOne width m previous current).Path) :
    (feedbackOne width m previous current).resourcePool path ≤
      if Recovery.Layout.feeds m previous current then single else 0 := by
  revert path
  unfold feedbackOne
  refine conditional_pool_bound (Recovery.Layout.feeds m previous current) _ _ _ _ single 0 ?_ ?_
  · intro path
    change ResourcePool.ofList
      (phaseProgram width m previous current path.1).eventTrace ≤ single
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
    exact phaseProgram_budget width m previous current path.1
  · intro path
    change (0 : ResourcePool Model) ≤ 0
    exact le_rfl

private lemma feedback_budget (width m : Nat) (current : Fin (2 * m))
    (previous : List (Fin (2 * m))) (path : (feedback width m current previous).Path) :
    (feedback width m current previous).resourcePool path ≤
      (previous.filter (fun index => decide (Recovery.Layout.feeds m index current))).length •
        single := by
  induction previous with
  | nil => exact le_rfl
  | cons head tail ih =>
      change ResourcePool.ofList
        ((feedbackOne width m head current).eventTrace path.1 ++
          (feedback width m current tail).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      have bounded := add_le_add (feedbackOne_budget width m head current path.1) (ih path.2)
      refine bounded.trans_eq ?_
      by_cases applicable : Recovery.Layout.feeds m head current
      · rw [if_pos applicable, List.filter_cons_of_pos
          (p := fun index => decide (Recovery.Layout.feeds m index current))
          (a := head) (l := tail) (decide_eq_true applicable), List.length_cons, succ_nsmul]
        ac_rfl
      · rw [if_neg applicable, List.filter_cons_of_neg
          (p := fun index => decide (Recovery.Layout.feeds m index current))
          (a := head) (l := tail)
          (fun present => applicable (of_decide_eq_true present)), zero_add]

/-- The actual feedback index set injects into the positions of one exponent bank. -/
lemma feedback_order_length_le (m : Nat) (current : Fin (2 * m)) :
    ((Recovery.Layout.order m).filter
      (fun previous => decide (Recovery.Layout.feeds m previous current))).length ≤ m := by
  have positive : 0 < m := by have within := current.isLt; omega
  let relevant := (Recovery.Layout.order m).filter
    (fun previous => decide (Recovery.Layout.feeds m previous current))
  have distinct : relevant.Nodup := (List.nodup_finRange (2 * m)).filter _
  have cardinality := List.toFinset_card_of_nodup distinct
  have bounded := Finset.card_le_card_of_injOn (s := relevant.toFinset)
    (t := Finset.range m) (fun previous : Fin (2 * m) => previous.val % m)
    (by
      intro previous _present
      exact Finset.mem_range.mpr (Nat.mod_lt previous.val positive))
    (by
      intro left leftPresent right rightPresent same
      have leftFeeds : Recovery.Layout.feeds m left current := by
        exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp leftPresent)).2
      have rightFeeds : Recovery.Layout.feeds m right current := by
        exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp rightPresent)).2
      have quotient : left.val / m = right.val / m := leftFeeds.2.trans rightFeeds.2.symm
      apply Fin.ext
      have leftDecomposition := Nat.mod_add_div left.val m
      have rightDecomposition := Nat.mod_add_div right.val m
      change left.val % m = right.val % m at same
      rw [same, quotient] at leftDecomposition
      exact leftDecomposition.symm.trans rightDecomposition)
  simpa only [cardinality, Finset.card_range] using bounded

/-- Every stored feedback branch of the actual order pays at most one gate per bank position. -/
lemma feedback_order_budget (width m : Nat) (current : Fin (2 * m))
    (path : (feedback width m current (Recovery.Layout.order m)).Path) :
    (feedback width m current (Recovery.Layout.order m)).resourcePool path ≤ m • single :=
  (feedback_budget width m current (Recovery.Layout.order m) path).trans
    (repeat_mono (feedback_order_length_le m current) single)

private lemma correction_budget (width m : Nat)
    (value : CShape.Value (.finite
      ((Context width m).quantumLayout.wire (Recovery.Layout.position width m 0)).dimension)) :
    (correction width m value).eventCost ≤ single := by
  unfold correction
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, QuditShift.qubitShiftCircuit_events]
  split_ifs <;> simp [ResourcePool.ofList, single, ResourcePool.singleton]

/-- Actual H, Z write and correction of that same stored outcome retain the full event pool. -/
lemma readout_budget (width m : Nat) (index : Fin (2 * m))
    (path : (readout width m index).Path) :
    (readout width m index).resourcePool path ≤ 2 • single + measured := by
  have corrected := correction_budget width m path.2.2.1
  change ResourcePool.ofList
    ((Gate.singleQubitAt (Context width m).quantumLayout .empty Gate.HOp
      (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).eventTrace ++
      (Circuit.zEvent
        ((Context width m).quantumLayout.wire (Recovery.Layout.position width m 0)).dimension ::
          (correction width m path.2.2.1).eventTrace)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_cons,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, Gate.singleQubitAt_eventCost]
  have measurementPool :
      (ResourcePool.singleton (Circuit.zEvent
        ((Context width m).quantumLayout.wire (Recovery.Layout.position width m 0)).dimension) :
          ResourcePool Model) = measured :=
    congrArg (fun dimension : ℕ+ =>
      (ResourcePool.singleton (Circuit.zEvent dimension) : ResourcePool Model))
      (Recovery.Layout.position_qubit width m 0)
  refine (congrArg (fun pool : ResourcePool Model =>
    single + (pool + (correction width m path.2.2.1).eventCost)) measurementPool).trans_le ?_
  refine (add_le_add le_rfl (add_le_add le_rfl corrected)).trans_eq ?_
  rw [two_nsmul]
  ac_rfl

/-- Both actual physical embeddings preserve every event of the same point-body Path. -/
lemma streamingPointCall_budget {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (path : (Recovery.Point.streamingPointCall E points index).Path) :
    (Recovery.Point.streamingPointCall E points index).resourcePool path ≤
      MeasuredPointAddition.events p.size := by
  change (Recovery.Point.pointBody E (points index)).resourcePool path ≤ _
  exact Recovery.Point.Events.pointBody_budget E (points index) path

/-- The complete actual stage obeys its independent native gate and measurement allowance. -/
lemma stage_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (path : (stage E r points index).Path) :
    (stage E r points index).resourcePool path ≤ stageBudget p.size m := by
  have prepared := preparation_budget p.size m r (Recovery.Layout.remaining m index)
  have point := streamingPointCall_budget E points index path.2.1
  have feedback := feedback_order_budget p.size m index path.2.2.1
  have last := readout_budget p.size m index path.2.2.2
  change ResourcePool.ofList
    ((Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m index)).eventTrace ++
      ((Recovery.Point.streamingPointCall E points index).eventTrace path.2.1 ++
        ((Recovery.Stage.feedback p.size m index (Recovery.Layout.order m)).eventTrace path.2.2.1 ++
          (readout p.size m index).eventTrace path.2.2.2))) ≤ _
  simp only [ResourcePool.ofList_append]
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  refine (add_le_add prepared (add_le_add point (add_le_add feedback last))).trans_eq ?_
  unfold stageBudget
  rw [show m + 9 = 7 + (m + 2) by omega, add_nsmul, add_nsmul]
  ac_rfl

/-- Every actual stage of an arbitrary finite schedule retains its complete event allowance. -/
lemma stages_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (indices : List (Fin (2 * m))) (path : (stages E r points indices).Path) :
    (stages E r points indices).resourcePool path ≤ indices.length • stageBudget p.size m := by
  induction indices with
  | nil => exact le_rfl
  | cons index tail ih =>
      change ResourcePool.ofList
        ((stage E r points index).eventTrace path.1 ++
          (stages E r points tail).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      refine (add_le_add (stage_budget E r points index path.1) (ih path.2)).trans_eq ?_
      rw [List.length_cons, succ_nsmul]
      ac_rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage.Events

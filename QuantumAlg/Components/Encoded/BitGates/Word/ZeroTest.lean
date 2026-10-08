/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Clean encoded-word zero test

This module gives the physical compute-copy-uncompute skeleton for testing a
word of width `tail + 2`.  It uses only X, CNOT, and Toffoli leaves.  The
workspace is a chain of exactly `tail = (tail + 2) - 2` clean bits.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit
namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {tail : Nat}

/-- Lenses and wire separation needed by a clean, width-at-least-two zero
test.  The tested word has width `tail + 2`, while the conjunction chain uses
exactly `tail` clean work bits. -/
structure ZeroTestLayout (tail : Nat) where
  /-- Read-only source word. -/
  source : Word encoding (tail + 2)
  /-- Xor-output bit receiving the zero predicate. -/
  output : EncodedBit encoding
  /-- Clean conjunction-chain workspace. -/
  work : Word encoding tail
  source_source_ne :
    ∀ i j, i ≠ j → (source.bit i).wire ≠ (source.bit j).wire
  source_output_ne : ∀ i, (source.bit i).wire ≠ output.wire
  source_work_ne : ∀ i j, (source.bit i).wire ≠ (work.bit j).wire
  work_work_ne :
    ∀ i j, i ≠ j → (work.bit i).wire ≠ (work.bit j).wire
  work_output_ne : ∀ j, (work.bit j).wire ≠ output.wire

namespace ZeroTestLayout

variable (layout : ZeroTestLayout (encoding := encoding) tail)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- The source index consumed alongside the previous conjunction result at a
non-initial chain stage. -/
def chainSourceIndex (j : Fin tail) : Fin (tail + 2) :=
  ⟨j.val + 1, by omega⟩

/-- The preceding conjunction-work index at a non-initial chain stage.  The
proof argument enforces the call-site restriction but does not affect the index. -/
@[nolint unusedArguments]
def previousWorkIndex (j : Fin tail) (_h : j.val ≠ 0) : Fin tail :=
  ⟨j.val - 1, by
    have hj := j.isLt
    omega⟩

/-- The final work index when the conjunction chain is nonempty. -/
def lastWorkIndex (tail : Nat) (h : tail ≠ 0) : Fin tail :=
  ⟨tail - 1, by
    have htail : 0 < tail := Nat.pos_of_ne_zero h
    omega⟩

/-- The final source index of a width-`tail + 2` source word. -/
def lastSourceIndex (tail : Nat) : Fin (tail + 2) :=
  ⟨tail + 1, by omega⟩

theorem zero_ne_chainSourceIndex (j : Fin tail) :
    (0 : Fin (tail + 2)) ≠ chainSourceIndex j := by
  intro h
  have hval := congrArg Fin.val h
  dsimp [chainSourceIndex] at hval
  omega

theorem previousWorkIndex_ne_self (j : Fin tail) (h : j.val ≠ 0) :
    previousWorkIndex j h ≠ j := by
  intro heq
  have hval := congrArg Fin.val heq
  dsimp [previousWorkIndex] at hval
  omega

/-- First control for one conjunction-chain Toffoli: the first source bit at
stage zero, then the preceding work bit. -/
def chainControlA (j : Fin tail) : EncodedBit encoding :=
  if h : j.val = 0 then layout.source.bit 0
  else layout.work.bit (previousWorkIndex j h)

/-- Second control for one conjunction-chain Toffoli. -/
def chainControlB (j : Fin tail) : EncodedBit encoding :=
  layout.source.bit (chainSourceIndex j)

theorem chainControlA_ne_chainControlB (j : Fin tail) :
    (chainControlA layout j).wire ≠ (chainControlB layout j).wire := by
  unfold chainControlA chainControlB
  split
  · exact layout.source_source_ne 0 (chainSourceIndex j)
      (zero_ne_chainSourceIndex j)
  · exact (layout.source_work_ne (chainSourceIndex j)
      (previousWorkIndex j _)).symm

theorem chainControlA_ne_work (j : Fin tail) :
    (chainControlA layout j).wire ≠ (layout.work.bit j).wire := by
  unfold chainControlA
  split
  · exact layout.source_work_ne 0 j
  · exact layout.work_work_ne (previousWorkIndex j _ ) j
      (previousWorkIndex_ne_self j _)

theorem chainControlB_ne_work (j : Fin tail) :
    (chainControlB layout j).wire ≠ (layout.work.bit j).wire :=
  layout.source_work_ne (chainSourceIndex j) j

theorem chainControlA_output_ne (j : Fin tail) :
    (chainControlA layout j).wire ≠ layout.output.wire := by
  unfold chainControlA
  split
  · exact layout.source_output_ne 0
  · exact layout.work_output_ne _

theorem chainControlB_output_ne (j : Fin tail) :
    (chainControlB layout j).wire ≠ layout.output.wire :=
  layout.source_output_ne (chainSourceIndex j)

/-- One forward conjunction-chain Toffoli.  With source bits pre-negated and
clean work, its target accumulates the conjunction of the prefix seen so far. -/
def andGateAt (j : Fin tail) : GateSpec encoding :=
  GateSpec.toffoli (chainControlA layout j) (chainControlB layout j)
    (layout.work.bit j) (chainControlA_ne_chainControlB layout j)
    (chainControlA_ne_work layout j) (chainControlB_ne_work layout j)

/-- Ordered forward Toffoli conjunction chain. -/
def andGates : List (GateSpec encoding) :=
  List.ofFn fun j : Fin tail => andGateAt layout j

/-- Indices of the conjunction stages in increasing source-bit order. -/
def andStageIndices : List (Fin tail) :=
  List.ofFn fun j : Fin tail => j

/-- Folded semantic action of the forward conjunction chain over its stage
indices. -/
def andStageIndexStep : Data → Data :=
  (andStageIndices (tail := tail)).foldl
    (fun y j => (andGateAt layout j).step y)

/-- Prefix action of the forward conjunction chain. -/
def andStagePrefixStep (t : Nat) : Data → Data :=
  ((andStageIndices (tail := tail)).take t).foldl
    (fun y j => (andGateAt layout j).step y)

/-- The concrete `List.ofFn` gate list agrees with the indexed conjunction
fold. -/
theorem andGates_stepList_eq_indexStep (x : Data) :
    GateSpec.stepList (andGates layout) x = andStageIndexStep layout x := by
  rw [andGates, GateSpec.stepList_eq_foldl]
  unfold andStageIndexStep andStageIndices
  let gateOfIndex : Fin tail → GateSpec encoding := fun j => andGateAt layout j
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y j => (gateOfIndex j).step y) x
        (List.ofFn fun j : Fin tail => j)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun j : Fin tail => j).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun j : Fin tail => j) gateOfIndex)]
  generalize List.ofFn (fun j : Fin tail => j) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      simp [ih]

/-- One conjunction stage xors its two controls into its designated work bit. -/
theorem andGateAt_get_work (j : Fin tail) (x : Data) :
    (layout.work.bit j).get ((andGateAt layout j).step x) =
      ((layout.work.bit j).get x ^^
        ((chainControlA layout j).get x && (chainControlB layout j).get x)) := by
  unfold andGateAt GateSpec.step
  exact EncodedBit.toffoliStep_get_target
    (chainControlA layout j) (chainControlB layout j) (layout.work.bit j) x

/-- A conjunction stage leaves each source bit unchanged. -/
theorem andGateAt_get_source (j : Fin tail) (i : Fin (tail + 2)) (x : Data) :
    (layout.source.bit i).get ((andGateAt layout j).step x) =
      (layout.source.bit i).get x := by
  unfold andGateAt GateSpec.step
  exact EncodedBit.toffoliStep_get_of_target_ne
    (chainControlA layout j) (chainControlB layout j) (layout.work.bit j)
    (layout.source.bit i) (layout.source_work_ne i j).symm x

/-- A conjunction stage leaves every other work bit unchanged. -/
theorem andGateAt_get_work_of_ne (j k : Fin tail) (hne : j ≠ k) (x : Data) :
    (layout.work.bit k).get ((andGateAt layout j).step x) =
      (layout.work.bit k).get x := by
  unfold andGateAt GateSpec.step
  exact EncodedBit.toffoliStep_get_of_target_ne
    (chainControlA layout j) (chainControlB layout j) (layout.work.bit j)
    (layout.work.bit k) (layout.work_work_ne j k hne) x

/-- Any fold of conjunction stages preserves every source readout. -/
theorem foldl_andGateAt_get_source (indices : List (Fin tail))
    (i : Fin (tail + 2)) (x : Data) :
    (layout.source.bit i).get
        (indices.foldl (fun y j => (andGateAt layout j).step y) x) =
      (layout.source.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.source.bit i).get
            (rest.foldl (fun y j => (andGateAt layout j).step y)
              ((andGateAt layout j).step x)) =
          (layout.source.bit i).get x
      rw [ih]
      exact andGateAt_get_source layout j i x

/-- A fold preserves a work bit when its stage index is absent from the fold. -/
theorem foldl_andGateAt_get_work_of_forall_ne (indices : List (Fin tail))
    (k : Fin tail) (hne : ∀ j, j ∈ indices → j ≠ k) (x : Data) :
    (layout.work.bit k).get
        (indices.foldl (fun y j => (andGateAt layout j).step y) x) =
      (layout.work.bit k).get x := by
  induction indices generalizing x with
  | nil =>
      rfl
  | cons j rest ih =>
      change
        (layout.work.bit k).get
            (rest.foldl (fun y j => (andGateAt layout j).step y)
              ((andGateAt layout j).step x)) =
          (layout.work.bit k).get x
      rw [ih]
      · exact andGateAt_get_work_of_ne layout j k (hne j (by simp)) x
      · intro next hnext
        exact hne next (by simp [hnext])

@[simp] theorem andStageIndices_length :
    (andStageIndices (tail := tail)).length = tail := by
  simp [andStageIndices]

theorem andStageIndices_getElem_val {i : Nat}
    (hi : i < (andStageIndices (tail := tail)).length) :
    ((andStageIndices (tail := tail))[i]'hi).val = i := by
  simp [andStageIndices]

/-- Every stage in the prefix before `j` has a smaller index. -/
theorem andStageIndices_mem_take_val_lt {j k : Fin tail}
    (hmem : k ∈ (andStageIndices (tail := tail)).take j.val) :
    k.val < j.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have htakeLen :
      ((andStageIndices (tail := tail)).take j.val).length = j.val := by
    rw [List.length_take, andStageIndices_length]
    exact Nat.min_eq_left (le_of_lt j.isLt)
  have hij : i < j.val := by
    simpa [htakeLen] using hi
  have hiOrig : i < (andStageIndices (tail := tail)).length := by
    rw [andStageIndices_length]
    exact lt_trans hij j.isLt
  rw [← List.getElem_take' hiOrig hij] at hki
  have hkval : k.val = i := by
    rw [← hki]
    exact andStageIndices_getElem_val (tail := tail) hiOrig
  omega

/-- Every stage in the suffix after `j` has a larger index. -/
theorem andStageIndices_mem_drop_succ_val_gt {j k : Fin tail}
    (hmem : k ∈ (andStageIndices (tail := tail)).drop (j.val + 1)) :
    j.val < k.val := by
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨i, hi, hki⟩
  have hiOrig : j.val + 1 + i < (andStageIndices (tail := tail)).length := by
    have h := hi
    have hjLe : j.val + 1 ≤ tail := Nat.succ_le_of_lt j.isLt
    rw [andStageIndices_length]
    rw [List.length_drop, andStageIndices_length] at h
    omega
  rw [List.getElem_drop] at hki
  have hkval : k.val = j.val + 1 + i := by
    rw [← hki]
    exact andStageIndices_getElem_val (tail := tail) hiOrig
  omega

theorem andStagePrefixStep_get_source (t : Nat) (i : Fin (tail + 2))
    (x : Data) :
    (layout.source.bit i).get (andStagePrefixStep layout t x) =
      (layout.source.bit i).get x := by
  unfold andStagePrefixStep
  exact foldl_andGateAt_get_source layout
    ((andStageIndices (tail := tail)).take t) i x

/-- The work bit for stage `j` is clean immediately before that stage. -/
theorem andStagePrefixStep_get_work_before (j : Fin tail) (x : Data) :
    (layout.work.bit j).get (andStagePrefixStep layout j.val x) =
      (layout.work.bit j).get x := by
  unfold andStagePrefixStep
  exact foldl_andGateAt_get_work_of_forall_ne layout
    ((andStageIndices (tail := tail)).take j.val) j
    (by
      intro k hmem hkj
      have hklt : k.val < j.val :=
        andStageIndices_mem_take_val_lt (tail := tail) hmem
      have hval := congrArg Fin.val hkj
      omega)
    x

/-- On clean incoming work, the prefix ending at `j` computes that stage's
two-control conjunction into `work[j]`. -/
theorem andStagePrefixStep_get_work_current (j : Fin tail) (x : Data)
    (hclean : ∀ k, (layout.work.bit k).get x = false) :
    (layout.work.bit j).get (andStagePrefixStep layout (j.val + 1) x) =
      ((chainControlA layout j).get (andStagePrefixStep layout j.val x) &&
        (chainControlB layout j).get (andStagePrefixStep layout j.val x)) := by
  have hjLt : j.val < (andStageIndices (tail := tail)).length := by
    rw [andStageIndices_length]
    exact j.isLt
  have hget : (andStageIndices (tail := tail))[j.val]'hjLt = j := by
    apply Fin.ext
    exact andStageIndices_getElem_val (tail := tail) hjLt
  have htake :
      (andStageIndices (tail := tail)).take (j.val + 1) =
        (andStageIndices (tail := tail)).take j.val ++ [j] := by
    rw [← List.take_concat_get' (andStageIndices (tail := tail)) j.val hjLt]
    rw [hget]
  have hcleanBefore :
      (layout.work.bit j).get (andStagePrefixStep layout j.val x) = false := by
    rw [andStagePrefixStep_get_work_before]
    exact hclean j
  have hlocal := andGateAt_get_work layout j
    (andStagePrefixStep layout j.val x)
  rw [hcleanBefore] at hlocal
  have hlocal' :
      (layout.work.bit j).get
          ((andGateAt layout j).step (andStagePrefixStep layout j.val x)) =
        ((chainControlA layout j).get (andStagePrefixStep layout j.val x) &&
          (chainControlB layout j).get (andStagePrefixStep layout j.val x)) := by
    rw [hlocal]
    cases (chainControlA layout j).get (andStagePrefixStep layout j.val x) <;>
      cases (chainControlB layout j).get (andStagePrefixStep layout j.val x) <;>
        rfl
  unfold andStagePrefixStep
  rw [htake, List.foldl_append]
  simpa [andStagePrefixStep, List.foldl] using hlocal'

/-- The suffix after stage `j` does not modify `work[j]`. -/
theorem andStageIndexStep_get_work_from_prefix (j : Fin tail) (x : Data) :
    (layout.work.bit j).get (andStageIndexStep layout x) =
      (layout.work.bit j).get (andStagePrefixStep layout (j.val + 1) x) := by
  unfold andStageIndexStep andStagePrefixStep
  nth_rw 1 [← List.take_append_drop (j.val + 1)
    (andStageIndices (tail := tail))]
  rw [List.foldl_append]
  exact foldl_andGateAt_get_work_of_forall_ne layout
    ((andStageIndices (tail := tail)).drop (j.val + 1)) j
    (by
      intro k hmem hkj
      have hkgt : j.val < k.val :=
        andStageIndices_mem_drop_succ_val_gt (tail := tail) hmem
      have hval := congrArg Fin.val hkj
      omega)
    (((andStageIndices (tail := tail)).take (j.val + 1)).foldl
      (fun y k => (andGateAt layout k).step y) x)

theorem andStageIndexStep_get_source (i : Fin (tail + 2)) (x : Data) :
    (layout.source.bit i).get (andStageIndexStep layout x) =
      (layout.source.bit i).get x := by
  unfold andStageIndexStep
  exact foldl_andGateAt_get_source layout
    (andStageIndices (tail := tail)) i x

theorem andStagePrefixStep_previousWork_eq_indexStep (j : Fin tail)
    (h : j.val ≠ 0) (x : Data) :
    (layout.work.bit (previousWorkIndex j h)).get
        (andStagePrefixStep layout j.val x) =
      (layout.work.bit (previousWorkIndex j h)).get
        (andStageIndexStep layout x) := by
  let previous := previousWorkIndex j h
  have hprevious : previous.val + 1 = j.val := by
    dsimp [previous, previousWorkIndex]
    omega
  have hfull := andStageIndexStep_get_work_from_prefix layout previous x
  rw [hprevious] at hfull
  exact hfull.symm

theorem chainControlA_get_prefix_eq_indexStep (j : Fin tail) (x : Data) :
    (chainControlA layout j).get (andStagePrefixStep layout j.val x) =
      (chainControlA layout j).get (andStageIndexStep layout x) := by
  unfold chainControlA
  split
  · rw [andStagePrefixStep_get_source, andStageIndexStep_get_source]
  · exact andStagePrefixStep_previousWork_eq_indexStep layout j _ x

theorem chainControlB_get_prefix_eq_indexStep (j : Fin tail) (x : Data) :
    (chainControlB layout j).get (andStagePrefixStep layout j.val x) =
      (chainControlB layout j).get (andStageIndexStep layout x) := by
  unfold chainControlB
  rw [andStagePrefixStep_get_source, andStageIndexStep_get_source]

/-- Full-chain recurrence for one work bit, expressed at the final forward
stage state. -/
theorem andStageIndexStep_get_work_recurrence (j : Fin tail) (x : Data)
    (hclean : ∀ k, (layout.work.bit k).get x = false) :
    (layout.work.bit j).get (andStageIndexStep layout x) =
      ((chainControlA layout j).get (andStageIndexStep layout x) &&
        (chainControlB layout j).get (andStageIndexStep layout x)) := by
  rw [andStageIndexStep_get_work_from_prefix]
  rw [andStagePrefixStep_get_work_current layout j x hclean]
  rw [chainControlA_get_prefix_eq_indexStep,
    chainControlB_get_prefix_eq_indexStep]

theorem andGateAt_output_bitDisjoint (j : Fin tail) :
    GateSpec.bitDisjoint layout.output (andGateAt layout j) := by
  change
    (chainControlA layout j).wire ≠ layout.output.wire ∧
      (chainControlB layout j).wire ≠ layout.output.wire ∧
        (layout.work.bit j).wire ≠ layout.output.wire
  exact ⟨chainControlA_output_ne layout j, chainControlB_output_ne layout j,
    layout.work_output_ne j⟩

theorem andGates_output_bitDisjoint :
    ∀ gate, gate ∈ andGates layout →
      GateSpec.bitDisjoint layout.output gate := by
  intro gate hgate
  simp only [andGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨j, rfl⟩
  exact andGateAt_output_bitDisjoint layout j

theorem source_zero_ne_one :
    (layout.source.bit (0 : Fin (tail + 2))).wire ≠
      (layout.source.bit (1 : Fin (tail + 2))).wire := by
  apply layout.source_source_ne
  intro heq
  have hval := congrArg Fin.val heq
  norm_num at hval

/-- Final output Toffoli.  A two-bit word is handled directly; otherwise the
last work bit is combined with the final source bit. -/
def finalGate : GateSpec encoding :=
  if h : tail = 0 then
    GateSpec.toffoli (layout.source.bit 0) (layout.source.bit 1) layout.output
      (source_zero_ne_one layout) (layout.source_output_ne 0)
      (layout.source_output_ne 1)
  else
    GateSpec.toffoli (layout.work.bit (lastWorkIndex tail h))
      (layout.source.bit (lastSourceIndex tail)) layout.output
      (layout.source_work_ne (lastSourceIndex tail) (lastWorkIndex tail h)).symm
      (layout.work_output_ne (lastWorkIndex tail h))
      (layout.source_output_ne (lastSourceIndex tail))

/-- Whether the final physical Toffoli fires on a state. -/
def finalControl (x : Data) : Bool :=
  if h : tail = 0 then
    (layout.source.bit 0).get x && (layout.source.bit 1).get x
  else
    (layout.work.bit (lastWorkIndex tail h)).get x &&
      (layout.source.bit (lastSourceIndex tail)).get x

theorem finalGate_step_eq_if (x : Data) :
    (finalGate layout).step x =
      if finalControl layout x then layout.output.flip x else x := by
  by_cases h : tail = 0 <;>
    simp [finalGate, finalControl, GateSpec.step, toffoliStep, h]

/-- X gates that convert the all-zero source predicate to an all-true
conjunction predicate. -/
def sourceXGates : List (GateSpec encoding) :=
  List.ofFn fun i : Fin (tail + 2) => GateSpec.x (layout.source.bit i)

/-- Folded X action over an explicit source-index list. -/
def sourceXIndicesStep (indices : List (Fin (tail + 2))) : Data → Data :=
  fun x => indices.foldl (fun y i => (layout.source.bit i).flip y) x

theorem sourceXGates_stepList_eq_indicesStep (x : Data) :
    GateSpec.stepList (sourceXGates layout) x =
      sourceXIndicesStep layout (List.ofFn fun i : Fin (tail + 2) => i) x := by
  rw [sourceXGates, GateSpec.stepList_eq_foldl, sourceXIndicesStep]
  let gateOfIndex : Fin (tail + 2) → GateSpec encoding := fun i =>
    GateSpec.x (layout.source.bit i)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin (tail + 2) => i)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin (tail + 2) => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin (tail + 2) => i) gateOfIndex)]
  generalize List.ofFn (fun i : Fin (tail + 2) => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

theorem sourceXIndicesStep_get_source (indices : List (Fin (tail + 2)))
    (hnodup : indices.Nodup) (bit : Fin (tail + 2))
    (hsourceSource :
      ∀ other, other ≠ bit →
        (layout.source.bit other).wire ≠ (layout.source.bit bit).wire)
    (x : Data) :
    (layout.source.bit bit).get (sourceXIndicesStep layout indices x) =
      ((layout.source.bit bit).get x ^^ decide (bit ∈ indices)) := by
  induction indices generalizing x with
  | nil =>
      simp [sourceXIndicesStep]
  | cons head rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hheadNotMem : head ∉ rest := hnodup.notMem
      unfold sourceXIndicesStep at *
      change
        (layout.source.bit bit).get
            (rest.foldl (fun y i => (layout.source.bit i).flip y)
              ((layout.source.bit head).flip x)) =
          ((layout.source.bit bit).get x ^^
            decide (bit ∈ head :: rest))
      by_cases hhead : head = bit
      · subst head
        rw [ih hrestNodup ((layout.source.bit bit).flip x)]
        rw [EncodedBit.get_flip_self]
        simp [hheadNotMem]
      · rw [ih hrestNodup ((layout.source.bit head).flip x)]
        have hget :
            (layout.source.bit bit).get ((layout.source.bit head).flip x) =
              (layout.source.bit bit).get x := by
          rw [EncodedBit.get_flip_of_wire_ne (layout.source.bit head)
            (layout.source.bit bit) (hsourceSource head hhead)]
        rw [hget]
        have hbitHead : bit ≠ head := Ne.symm hhead
        by_cases hmem : bit ∈ rest <;> simp [hbitHead, hmem]

/-- Every source bit is inverted exactly once by the source-X stage. -/
theorem sourceXGates_get_source (i : Fin (tail + 2)) (x : Data) :
    (layout.source.bit i).get (GateSpec.stepList (sourceXGates layout) x) =
      !(layout.source.bit i).get x := by
  rw [sourceXGates_stepList_eq_indicesStep]
  have hnodup :
      (List.ofFn fun bit : Fin (tail + 2) => bit).Nodup := by
    exact List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun bit : Fin (tail + 2) => bit) := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  calc
    (layout.source.bit i).get
        (sourceXIndicesStep layout (List.ofFn fun bit : Fin (tail + 2) => bit) x) =
        ((layout.source.bit i).get x ^^
          decide (i ∈ (List.ofFn fun bit : Fin (tail + 2) => bit))) :=
      sourceXIndicesStep_get_source layout
        (List.ofFn fun bit : Fin (tail + 2) => bit) hnodup i
        (fun other hne => layout.source_source_ne other i hne) x
    _ = ((layout.source.bit i).get x ^^ true) := by
      rw [decide_eq_true hmem]
    _ = !(layout.source.bit i).get x := by
      cases (layout.source.bit i).get x <;> rfl

/-- The source-X stage leaves each conjunction-work bit unchanged. -/
theorem sourceXGates_get_work (j : Fin tail) (x : Data) :
    (layout.work.bit j).get (GateSpec.stepList (sourceXGates layout) x) =
      (layout.work.bit j).get x := by
  unfold sourceXGates
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rcases List.mem_ofFn.mp hgate with ⟨i, rfl⟩
  change ∀ y, (layout.work.bit j).get ((layout.source.bit i).flip y) =
    (layout.work.bit j).get y
  intro y
  exact EncodedBit.get_flip_of_wire_ne (layout.source.bit i)
    (layout.work.bit j) (layout.source_work_ne i j) y

/-- The first `count` source positions all read true. -/
def sourcePrefixTrue (x : Data) (count : Nat) : Prop :=
  ∀ i : Fin (tail + 2), i.val < count → (layout.source.bit i).get x = true

/-- On clean work, `work[j]` is true exactly when source positions through
`j + 1` are all true after the source-X stage. -/
theorem andStageIndexStep_get_work_eq_true_iff (j : Fin tail) (x : Data)
    (hclean : ∀ k, (layout.work.bit k).get x = false) :
    (layout.work.bit j).get (andStageIndexStep layout x) = true ↔
      sourcePrefixTrue layout x (j.val + 2) := by
  have hmain : ∀ m, ∀ j : Fin tail, j.val = m →
      ((layout.work.bit j).get (andStageIndexStep layout x) = true ↔
        sourcePrefixTrue layout x (j.val + 2)) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih j hjm
    rw [andStageIndexStep_get_work_recurrence layout j x hclean]
    constructor
    · intro hwork
      have hcontrols :
          (chainControlA layout j).get (andStageIndexStep layout x) = true ∧
            (chainControlB layout j).get (andStageIndexStep layout x) = true :=
        (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hwork
      intro i hi
      by_cases hlast : i.val = j.val + 1
      · have hindex : i = chainSourceIndex j := by
          apply Fin.ext
          dsimp [chainSourceIndex]
          exact hlast
        subst i
        have hsource :
            (layout.source.bit (chainSourceIndex j)).get x = true := by
          have hstage :
              (layout.source.bit (chainSourceIndex j)).get
                  (andStageIndexStep layout x) = true := by
            simpa [chainControlB] using hcontrols.2
          rw [andStageIndexStep_get_source] at hstage
          exact hstage
        exact hsource
      · by_cases hzero : j.val = 0
        · have hizero : i.val = 0 := by
            omega
          have hindex : i = 0 := by
            apply Fin.ext
            exact hizero
          subst i
          have hsource : (layout.source.bit 0).get x = true := by
            have hstage :
                (layout.source.bit 0).get (andStageIndexStep layout x) = true := by
              simpa [chainControlA, hzero] using hcontrols.1
            rw [andStageIndexStep_get_source] at hstage
            exact hstage
          exact hsource
        · let previous := previousWorkIndex j hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous, previousWorkIndex]
            omega
          have hpreviousWork :
              (layout.work.bit previous).get (andStageIndexStep layout x) = true := by
            simpa [chainControlA, hzero, previous] using hcontrols.1
          have hpreviousPrefix :
              sourcePrefixTrue layout x (previous.val + 2) :=
            (ih previous.val hpreviousLt previous rfl).mp hpreviousWork
          have hilow : i.val < previous.val + 2 := by
            dsimp [previous, previousWorkIndex]
            omega
          exact hpreviousPrefix i hilow
    · intro hprefix
      apply (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mpr
      constructor
      · by_cases hzero : j.val = 0
        · have hsource : (layout.source.bit 0).get x = true :=
            hprefix 0 (by simp)
          have hstage :
              (layout.source.bit 0).get (andStageIndexStep layout x) = true := by
            rw [andStageIndexStep_get_source]
            exact hsource
          simpa [chainControlA, hzero] using hstage
        · let previous := previousWorkIndex j hzero
          have hpreviousLt : previous.val < m := by
            dsimp [previous, previousWorkIndex]
            omega
          have hpreviousPrefix :
              sourcePrefixTrue layout x (previous.val + 2) := by
            intro i hi
            exact hprefix i (by
              dsimp [previous, previousWorkIndex] at hi ⊢
              omega)
          have hpreviousWork :
              (layout.work.bit previous).get (andStageIndexStep layout x) = true :=
            (ih previous.val hpreviousLt previous rfl).mpr hpreviousPrefix
          simpa [chainControlA, hzero, previous] using hpreviousWork
      · have hsource :
            (layout.source.bit (chainSourceIndex j)).get x = true :=
          hprefix (chainSourceIndex j) (by
            dsimp [chainSourceIndex]
            omega)
        have hstage :
            (layout.source.bit (chainSourceIndex j)).get
                (andStageIndexStep layout x) = true := by
          rw [andStageIndexStep_get_source]
          exact hsource
        simpa [chainControlB] using hstage
  exact hmain j.val j (by rfl)

/-- The final conjunction control is true exactly when every source bit is
true, provided the chain workspace began clean. -/
theorem finalControl_andStage_eq_true_iff (x : Data)
    (hclean : ∀ k, (layout.work.bit k).get x = false) :
    finalControl layout (andStageIndexStep layout x) = true ↔
      ∀ i, (layout.source.bit i).get x = true := by
  by_cases htail : tail = 0
  · subst tail
    rw [finalControl, dif_pos rfl]
    rw [andStageIndexStep_get_source, andStageIndexStep_get_source]
    constructor
    · intro h i
      have hbits := (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h
      fin_cases i
      · exact hbits.1
      · exact hbits.2
    · intro h
      exact (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mpr ⟨h 0, h 1⟩
  · rw [finalControl, dif_neg htail]
    constructor
    · intro h
      have hbits := (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp h
      have hprefix := (andStageIndexStep_get_work_eq_true_iff layout
        (lastWorkIndex tail htail) x hclean).mp hbits.1
      intro i
      by_cases hlast : i = lastSourceIndex tail
      · subst i
        rw [andStageIndexStep_get_source] at hbits
        exact hbits.2
      · have hilow : i.val < (lastWorkIndex tail htail).val + 2 := by
          have hnot : i.val ≠ tail + 1 := by
            intro hval
            apply hlast
            apply Fin.ext
            dsimp [lastSourceIndex]
            exact hval
          dsimp [lastWorkIndex]
          have hpositive : 0 < tail := Nat.pos_of_ne_zero htail
          omega
        exact hprefix i hilow
    · intro h
      apply (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mpr
      constructor
      · apply (andStageIndexStep_get_work_eq_true_iff layout
          (lastWorkIndex tail htail) x hclean).mpr
        intro i _hi
        exact h i
      · rw [andStageIndexStep_get_source]
        exact h (lastSourceIndex tail)

theorem sourceXGates_output_bitDisjoint :
    ∀ gate, gate ∈ sourceXGates layout →
      GateSpec.bitDisjoint layout.output gate := by
  intro gate hgate
  simp only [sourceXGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨i, rfl⟩
  change (layout.source.bit i).wire ≠ layout.output.wire
  exact layout.source_output_ne i

/-- Reversible computation preceding the output copy. -/
def computeGates : List (GateSpec encoding) :=
  sourceXGates layout ++ andGates layout

/-- With clean work, the physical compute stage fires its final control
exactly for an all-zero source word. -/
theorem finalControl_compute_eq_true_iff (x : Data)
    (hclean : ∀ j, (layout.work.bit j).get x = false) :
    finalControl layout (GateSpec.stepList (computeGates layout) x) = true ↔
      ∀ i, (layout.source.bit i).get x = false := by
  rw [computeGates, GateSpec.stepList_append,
    andGates_stepList_eq_indexStep]
  have hcleanAfterX :
      ∀ j, (layout.work.bit j).get
          (GateSpec.stepList (sourceXGates layout) x) = false := by
    intro j
    rw [sourceXGates_get_work]
    exact hclean j
  constructor
  · intro h i
    have htrue := (finalControl_andStage_eq_true_iff layout
      (GateSpec.stepList (sourceXGates layout) x) hcleanAfterX).mp h i
    rw [sourceXGates_get_source] at htrue
    cases hsource : (layout.source.bit i).get x with
    | false =>
        rfl
    | true =>
        simp [hsource] at htrue
  · intro h
    apply (finalControl_andStage_eq_true_iff layout
      (GateSpec.stepList (sourceXGates layout) x) hcleanAfterX).mpr
    intro i
    have hfalse := h i
    rw [sourceXGates_get_source]
    cases hsource : (layout.source.bit i).get x with
    | false =>
        rfl
    | true =>
        simp [hsource] at hfalse

theorem computeGates_output_bitDisjoint :
    ∀ gate, gate ∈ computeGates layout →
      GateSpec.bitDisjoint layout.output gate := by
  intro gate hgate
  simp only [computeGates, List.mem_append] at hgate
  rcases hgate with hgate | hgate
  · exact sourceXGates_output_bitDisjoint layout gate hgate
  · exact andGates_output_bitDisjoint layout gate hgate

/-- Actual X/Toffoli compute-copy-uncompute gate schedule.  It preserves the
source and restores the work chain, while xoring the computed zero bit into
the fresh output. -/
def gates : List (GateSpec encoding) :=
  computeGates layout ++ [finalGate layout] ++ (computeGates layout).reverse

/-- A zero-test schedule is disjoint from any external observed bit that is
disjoint from each of its source, output, and work wires. -/
theorem gates_bitDisjoint (observed : EncodedBit encoding)
    (hsource : ∀ i, (layout.source.bit i).wire ≠ observed.wire)
    (houtput : layout.output.wire ≠ observed.wire)
    (hwork : ∀ j, (layout.work.bit j).wire ≠ observed.wire) :
    ∀ gate, gate ∈ gates layout → GateSpec.bitDisjoint observed gate := by
  have hsourceX : ∀ gate, gate ∈ sourceXGates layout →
      GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    simp only [sourceXGates] at hgate
    rcases List.mem_ofFn.mp hgate with ⟨i, rfl⟩
    exact hsource i
  have hand : ∀ gate, gate ∈ andGates layout →
      GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    simp only [andGates] at hgate
    rcases List.mem_ofFn.mp hgate with ⟨j, rfl⟩
    change
      (chainControlA layout j).wire ≠ observed.wire ∧
        (chainControlB layout j).wire ≠ observed.wire ∧
          (layout.work.bit j).wire ≠ observed.wire
    refine ⟨?_, ?_, hwork j⟩
    · unfold chainControlA
      split
      · exact hsource 0
      · exact hwork _
    · exact hsource (chainSourceIndex j)
  have hcompute : ∀ gate, gate ∈ computeGates layout →
      GateSpec.bitDisjoint observed gate := by
    intro gate hgate
    rw [computeGates, List.mem_append] at hgate
    exact hgate.elim (hsourceX gate) (hand gate)
  have hfinal : GateSpec.bitDisjoint observed (finalGate layout) := by
    unfold finalGate
    split
    · exact ⟨hsource 0, hsource 1, houtput⟩
    · exact ⟨hwork _, hsource _, houtput⟩
  intro gate hgate
  rw [gates, List.mem_append, List.mem_reverse] at hgate
  rcases hgate with hforward | hreverse
  · rw [List.mem_append] at hforward
    rcases hforward with hcomputeGate | hfinalGate
    · exact hcompute gate hcomputeGate
    · rw [List.mem_singleton] at hfinalGate
      subst gate
      exact hfinal
  · exact hcompute gate hreverse

private theorem finalGate_xMultiplicity :
    GateSpec.xMultiplicity (finalGate layout) = 0 := by
  unfold finalGate
  split <;> rfl

private theorem finalGate_cnotMultiplicity :
    GateSpec.cnotMultiplicity (finalGate layout) = 0 := by
  unfold finalGate
  split <;> rfl

private theorem finalGate_toffoliMultiplicity :
    GateSpec.toffoliMultiplicity (finalGate layout) = 1 := by
  unfold finalGate
  split <;> rfl

/-- Exact leaf count of the clean width-`tail+2` zero test. -/
theorem gates_length :
    (gates layout).length = 4 * tail + 5 := by
  simp [gates, computeGates, sourceXGates, andGates]
  omega

/-- Exact X coordinate of the clean zero-test gate list. -/
theorem gates_xMultiplicity_sum :
    ((gates layout).map GateSpec.xMultiplicity).sum = 2 * tail + 4 := by
  simp [gates, computeGates, sourceXGates, andGates, andGateAt,
    finalGate_xMultiplicity, List.sum_ofFn]
  omega

/-- The clean zero test contains no CNOT leaves. -/
theorem gates_cnotMultiplicity_sum :
    ((gates layout).map GateSpec.cnotMultiplicity).sum = 0 := by
  simp [gates, computeGates, sourceXGates, andGates, andGateAt,
    finalGate_cnotMultiplicity, List.sum_ofFn]

/-- Exact Toffoli coordinate of the clean zero-test gate list. -/
theorem gates_toffoliMultiplicity_sum :
    ((gates layout).map GateSpec.toffoliMultiplicity).sum = 2 * tail + 1 := by
  simp [gates, computeGates, sourceXGates, andGates, andGateAt,
    finalGate_toffoliMultiplicity, List.sum_ofFn]
  omega

/-- Directly compiled physical circuit for the clean zero-test schedule. -/
def program : UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (gates layout)

/-- Folded semantic action of the physical zero-test schedule. -/
def step : Data → Data :=
  GateSpec.stepList (gates layout)

/-- The physical zero-test circuit realizes its exact ordered gate-list step. -/
theorem realizes :
    UnitaryCircuit.Realizes encoding (program layout physical oracles) (step layout) :=
  GateSpec.realizesList physical oracles (gates layout)

theorem computeGates_reverse_output_flip (x : Data) :
    GateSpec.stepList (computeGates layout).reverse (layout.output.flip x) =
      layout.output.flip (GateSpec.stepList (computeGates layout).reverse x) := by
  apply GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hgate
  exact computeGates_output_bitDisjoint layout gate (List.mem_reverse.mp hgate)

/-- The complete schedule is exactly an xor into `output`; every other
encoded-bit readout is restored by the compute-copy-uncompute sandwich. -/
theorem step_eq_outputConditional (x : Data) :
    step layout x =
      if finalControl layout (GateSpec.stepList (computeGates layout) x) then
        layout.output.flip x
      else x := by
  unfold step gates
  rw [GateSpec.stepList_append]
  rw [GateSpec.stepList_append]
  change
    GateSpec.stepList (computeGates layout).reverse
        ((finalGate layout).step
          (GateSpec.stepList (computeGates layout) x)) = _
  rw [finalGate_step_eq_if]
  split
  · rw [computeGates_reverse_output_flip]
    exact congrArg layout.output.flip
      (GateSpec.stepList_reverse_stepList (computeGates layout) x)
  · exact GateSpec.stepList_reverse_stepList (computeGates layout) x

/-- The full clean schedule preserves every observed readout outside the xor
output wire. -/
theorem step_get_of_output_ne (observed : EncodedBit encoding)
    (houtput : layout.output.wire ≠ observed.wire) (x : Data) :
    observed.get (step layout x) = observed.get x := by
  rw [step_eq_outputConditional]
  split
  · exact EncodedBit.get_flip_of_wire_ne layout.output observed houtput x
  · rfl

/-- The source word is a read-only input of the physical zero-test schedule. -/
theorem step_get_source (i : Fin (tail + 2)) (x : Data) :
    (layout.source.bit i).get (step layout x) = (layout.source.bit i).get x :=
  step_get_of_output_ne layout (layout.source.bit i)
    (layout.source_output_ne i).symm x

/-- Every conjunction-work bit is restored by the physical zero-test schedule. -/
theorem step_get_work (j : Fin tail) (x : Data) :
    (layout.work.bit j).get (step layout x) = (layout.work.bit j).get x :=
  step_get_of_output_ne layout (layout.work.bit j)
    (layout.work_output_ne j).symm x

/-- Readout of the clean xor endpoint.  The predicate is the final conjunction
control evaluated after the explicitly exposed compute stage. -/
theorem step_get_output (x : Data) :
    layout.output.get (step layout x) =
      (layout.output.get x ^^
        finalControl layout (GateSpec.stepList (computeGates layout) x)) := by
  rw [step_eq_outputConditional]
  split <;> rename_i h
  · rw [EncodedBit.get_flip_self, h]
    cases layout.output.get x <;> rfl
  · have hfalse :
        finalControl layout (GateSpec.stepList (computeGates layout) x) = false :=
      Bool.eq_false_of_not_eq_true h
    rw [hfalse]
    cases layout.output.get x <;> rfl

/-- A clean work register remains clean after the zero-test schedule. -/
theorem step_preserves_clean_work (x : Data)
    (hclean : ∀ j, (layout.work.bit j).get x = false) :
    ∀ j, (layout.work.bit j).get (step layout x) = false := by
  intro j
  rw [step_get_work]
  exact hclean j

/-- Combined clean endpoint/frame statement for callers that allocate a fresh
output and clean conjunction workspace. -/
theorem step_cleanEndpoint (x : Data)
    (hclean : ∀ j, (layout.work.bit j).get x = false) :
    (∀ i, (layout.source.bit i).get (step layout x) = (layout.source.bit i).get x) ∧
      (∀ j, (layout.work.bit j).get (step layout x) = false) ∧
        layout.output.get (step layout x) =
          (layout.output.get x ^^
            finalControl layout (GateSpec.stepList (computeGates layout) x)) := by
  exact And.intro (fun i => step_get_source layout i x)
    (And.intro (step_preserves_clean_work layout x hclean) (step_get_output layout x))

/-- Public clean endpoint for the physical width-at-least-two zero test.  A
clean conjunction chain is restored, the source stays read-only, and the
fresh output is xored with the ordinary all-zero predicate. -/
theorem step_cleanZeroEndpoint (x : Data)
    (hclean : ∀ j, (layout.work.bit j).get x = false) :
    (∀ i, (layout.source.bit i).get (step layout x) = (layout.source.bit i).get x) ∧
      (∀ j, (layout.work.bit j).get (step layout x) = false) ∧
        layout.output.get (step layout x) =
          (layout.output.get x ^^
            decide (∀ i, (layout.source.bit i).get x = false)) := by
  refine And.intro (fun i => step_get_source layout i x) ?_
  refine And.intro (step_preserves_clean_work layout x hclean) ?_
  have hindicator :
      finalControl layout (GateSpec.stepList (computeGates layout) x) =
        decide (∀ i, (layout.source.bit i).get x = false) := by
    by_cases hzero : ∀ i, (layout.source.bit i).get x = false
    · have htrue := (finalControl_compute_eq_true_iff layout x hclean).mpr hzero
      rw [htrue]
      simp [hzero]
    · have hnotTrue :
          finalControl layout (GateSpec.stepList (computeGates layout) x) ≠ true := by
        intro htrue
        exact hzero ((finalControl_compute_eq_true_iff layout x hclean).mp htrue)
      have hfalse :
          finalControl layout (GateSpec.stepList (computeGates layout) x) = false :=
        Bool.eq_false_of_not_eq_true hnotTrue
      rw [hfalse]
      simp [hzero]
  rw [step_get_output, hindicator]

end ZeroTestLayout

end Word
end EncodedBit

end

end QuantumAlg

end

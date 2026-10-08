/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Swap

/-!
# Complete actual finite schedule for the source Sign exchange

The fixed schedule enumerates every complete pair of finite length values
and both first-phase values once. Each entry is the actual native equality,
controlled Sign/Work1 swap, and inverse equality list. No parameter of the
schedule is obtained by observing the quantum input. The explicit key
bijection includes every finite bit pattern and introduces no workspace.

For internally prepared Ctrl zero, every nonmatching entry is the identity.
There is at most one matching key. Its untruncated natural target adds one
to the old length sum in phase 2, retaining the baseline's updated-length
swap position [LYL+26, sec_EEA/sub_regshare.tex:281-296]. This repairs the
missing offset when the optimized listing moves the increment after the
swap [ibid., sub_opt.tex:52-59; NumberTheory.SharedEEA.SwapBoundary].
An out-of-range target is skipped. This finite refinement's actual gate
ledger belongs to this schedule, not to a source asymptotic constant.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionSchedule

noncomputable section

open EncodedBit SelectionKey

/-- Exact finite encoding of both complete length words and the first phase bit. -/
def keyIndex (width : Nat) : Key width ≃ Fin (2 ^ (width.size + (width.size + 1))) :=
  (Equiv.prodCongr BitVec.equivFin.toEquiv
    ((Equiv.prodCongr BitVec.equivFin.toEquiv finTwoEquiv.symm).trans
      (prodEquiv (m := width.size) (n := 1)))).trans
        (prodEquiv (m := width.size) (n := width.size + 1))

/-- Enumerate all possible actual length/phase keys through that proved complete encoding. -/
def keys (width : Nat) : List (Key width) := List.ofFn (keyIndex width).symm

theorem keys_nodup (width : Nat) : (keys width).Nodup :=
  List.nodup_ofFn_ofInjective (keyIndex width).symm.injective

theorem key_mem (width : Nat) (selected : Key width) : selected ∈ keys width :=
  List.mem_ofFn.mpr ⟨keyIndex width selected, (keyIndex width).symm_apply_apply selected⟩

/-- The schedule length counts the complete actual finite key enumeration. -/
theorem keys_length (width : Nat) :
    (keys width).length = 2 ^ (width.size + (width.size + 1)) := by
  rw [keys, List.length_ofFn]

private theorem condition_false_of_ne (width : Nat) (selected : Key width) (state : Registers width)
    (different : selected ≠ readKey state) :
    SelectionPredicate.condition (pattern selected) state = false :=
  decide_eq_false (fun matched => different
    ((matches_key_iff width selected state).mp matched).1.symm)

private theorem selector_inactive (width : Nat) (selected : Key width) (state : Registers width)
    (clean : state.control = false)
    (inactive : SelectionPredicate.condition (pattern selected) state = false) :
    SelectionSwap.step width selected state = state := by
  unfold SelectionSwap.step
  split
  · simp only [SelectionSwap.selectedStep, clean, Bool.false_xor, inactive,
      Bool.false_eq_true, if_false]
  · rfl

private theorem fold_inactive (width : Nat) (indices : List (Key width))
    (state : Registers width) (clean : state.control = false)
    (inactive : ∀ selected, selected ∈ indices →
      SelectionPredicate.condition (pattern selected) state = false) :
    indices.foldl (fun current selected => SelectionSwap.step width selected current) state =
      state := by
  induction indices with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, selector_inactive width selected state clean
        (inactive selected List.mem_cons_self)]
      exact ih (fun other present => inactive other (List.mem_cons_of_mem _ present))

private theorem fold_once (width : Nat) (indices : List (Key width)) :
    ∀ state : Registers width, state.control = false → indices.Nodup →
      indices.foldl (fun current selected => SelectionSwap.step width selected current) state =
        if readKey state ∈ indices then
          SelectionSwap.step width (readKey state) state else state := by
  induction indices with
  | nil =>
      intro state _clean _unique
      simp only [List.foldl_nil, List.not_mem_nil, if_false]
  | cons selected rest ih =>
      intro state clean unique
      rw [List.foldl_cons]
      by_cases same : selected = readKey state
      · subst selected
        have inactive : ∀ other, other ∈ rest →
            SelectionPredicate.condition (pattern other)
              (SelectionSwap.step width (readKey state) state) = false := by
          intro other present
          rw [SelectionSwap.step_condition]
          apply condition_false_of_ne
          intro equal
          subst other
          exact unique.notMem present
        rw [fold_inactive width rest _ ((SelectionSwap.step_control width _ state).trans clean)
          inactive, if_pos List.mem_cons_self]
      · rw [selector_inactive width selected state clean
          (condition_false_of_ne width selected state same), ih state clean unique.tail]
        simp only [List.mem_cons, Ne.symm same, false_or]

/-- Concatenate the actual complete native gate list of every finite selector. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  (keys width).flatMap (SelectionSwap.gates width)

/-- The mathematical full-frame fold of the actual finite selector actions. -/
def step (width : Nat) (state : Registers width) : Registers width :=
  (keys width).foldl (fun current selected => SelectionSwap.step width selected current) state

private theorem stepList_flatMap (width : Nat) (indices : List (Key width))
    (state : Registers width) :
    GateSpec.stepList (indices.flatMap (SelectionSwap.gates width)) state =
      indices.foldl (fun current selected => SelectionSwap.step width selected current) state := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.flatMap_cons, GateSpec.stepList_append, SelectionSwap.gates_step,
        List.foldl_cons, ih]

/-- Complete native-list correctness holds for every frame, including nonzero incoming Ctrl. -/
theorem gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state = step width state := stepList_flatMap width _ state

/-- Internal Ctrl zero reduces the executed full enumeration to its unique actual matching key. -/
theorem step_prepared (width : Nat) (state : Registers width) (clean : state.control = false) :
    step width state = SelectionSwap.step width (readKey state) state := by
  have actual := fold_once width (keys width) state clean (keys_nodup width)
  rw [if_pos (key_mem width (readKey state))] at actual
  exact actual

private theorem own_condition (width : Nat) (state : Registers width) :
    SelectionPredicate.condition (pattern (readKey state)) state = phaseSelected state := by
  apply Bool.eq_iff_iff.mpr
  simp only [SelectionPredicate.condition, decide_eq_true_eq, matches_key_iff,
    true_and]

/-- The independent action retains the baseline boundary and skips bad natural indices. -/
def sourceStep (width : Nat) (state : Registers width) : Registers width :=
  if within : state.coefficientLength.toNat + state.quotientLength.toNat +
      (if state.flags.first then 0 else 1) < width + 3 then
    if phaseSelected state then
      SelectionSwap.exchange width
        ⟨state.coefficientLength.toNat + state.quotientLength.toNat +
          (if state.flags.first then 0 else 1), within⟩ state
    else state
  else state

/-- Exact source-selected exchange by the actual complete native schedule on initialized frames. -/
theorem step_eq_sourceStep (width : Nat) (state : Registers width) (clean : state.control = false) :
    step width state = sourceStep width state := by
  rw [step_prepared width state clean]
  unfold SelectionSwap.step sourceStep
  change (if within : state.coefficientLength.toNat + state.quotientLength.toNat +
      (if state.flags.first then 0 else 1) < width + 3 then
    SelectionSwap.selectedStep width (readKey state)
      ⟨state.coefficientLength.toNat + state.quotientLength.toNat +
        (if state.flags.first then 0 else 1), within⟩ state else state) = _
  simp only [SelectionSwap.selectedStep, clean, Bool.false_xor, own_condition]

/-- Compile the same complete native schedule whose full frame fold was proved above. -/
def program (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width)

theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) (step width) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width) (gates_step width)

/-- The actual native program implements the source-selected exchange with its relative phases. -/
theorem program_apply_prepared (width : Nat) (state : Registers width)
    (clean : state.control = false) :
    (program width).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (sourceStep width state))) := by
  rw [(program_realizes width).apply_encoded_ket, step_eq_sourceStep width state clean]

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionSchedule

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.QubitPrimitive
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.NormNum
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-!
# Encoded-word cyclic shifts

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- Gates for swapping one adjacent pair of word bits. -/
def adjacentSwapGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    List (GateSpec encoding) :=
  EncodedBit.swapGates
    (word.bit (adjacentLeftIndex width i))
    (word.bit (adjacentRightIndex width i))
    (hword (adjacentLeftIndex width i) (adjacentRightIndex width i)
      (adjacentLeftIndex_ne_adjacentRightIndex width i))

/-- CNOT gate list for the cyclic shift obtained by sweeping adjacent swaps
from low index to high index. -/
def adjacentShiftLeftGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin (width - 1) => i).flatMap
    (adjacentSwapGates word hword)

/-- CNOT gate list for the inverse cyclic shift, sweeping adjacent swaps from
high index back to low index. -/
def adjacentShiftRightGates
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (adjacentShiftLeftGates word hword).reverse

/-- An adjacent-swap sweep contains three CNOT leaves for every adjacent word
position. -/
theorem adjacentShiftLeftGates_length
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    (adjacentShiftLeftGates word hword).length = 3 * (width - 1) := by
  simp [adjacentShiftLeftGates, adjacentSwapGates, EncodedBit.swapGates,
    List.length_flatMap, Function.comp_def, Nat.mul_comm]

/-- Reversing the adjacent-swap sweep preserves its exact leaf count. -/
theorem adjacentShiftRightGates_length
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    (adjacentShiftRightGates word hword).length = 3 * (width - 1) := by
  simpa only [adjacentShiftRightGates, List.length_reverse] using
    adjacentShiftLeftGates_length word hword

private theorem flatMap_adjacentSwapGates_multiplicity_sums
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ∀ indices : List (Fin (width - 1)),
      (((indices.flatMap (adjacentSwapGates word hword)).map
          GateSpec.xMultiplicity).sum = 0) ∧
        (((indices.flatMap (adjacentSwapGates word hword)).map
          GateSpec.cnotMultiplicity).sum = 3 * indices.length) ∧
        (((indices.flatMap (adjacentSwapGates word hword)).map
          GateSpec.toffoliMultiplicity).sum = 0) := by
  intro indices
  induction indices with
  | nil => simp
  | cons index rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        adjacentSwapGates, EncodedBit.swapGates, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, GateSpec.xMultiplicity_cnot,
        GateSpec.cnotMultiplicity_cnot, GateSpec.toffoliMultiplicity_cnot,
        List.length_cons]
      omega

/-- An adjacent-swap sweep contains no physical X leaves. -/
theorem adjacentShiftLeftGates_xMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftLeftGates word hword).map
      GateSpec.xMultiplicity).sum = 0 := by
  exact (flatMap_adjacentSwapGates_multiplicity_sums word hword
    (List.ofFn fun i : Fin (width - 1) => i)).1

/-- Every leaf in an adjacent-swap sweep is a CNOT. -/
theorem adjacentShiftLeftGates_cnotMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftLeftGates word hword).map
      GateSpec.cnotMultiplicity).sum = 3 * (width - 1) := by
  simpa only [adjacentShiftLeftGates, List.length_ofFn] using
    (flatMap_adjacentSwapGates_multiplicity_sums word hword
      (List.ofFn fun i : Fin (width - 1) => i)).2.1

/-- An adjacent-swap sweep contains no Toffoli leaves. -/
theorem adjacentShiftLeftGates_toffoliMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftLeftGates word hword).map
      GateSpec.toffoliMultiplicity).sum = 0 := by
  exact (flatMap_adjacentSwapGates_multiplicity_sums word hword
    (List.ofFn fun i : Fin (width - 1) => i)).2.2

/-- Reversing the sweep preserves its zero X coordinate. -/
theorem adjacentShiftRightGates_xMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftRightGates word hword).map
        GateSpec.xMultiplicity).sum = 0 := by
  simp only [adjacentShiftRightGates, List.map_reverse, List.sum_reverse,
    adjacentShiftLeftGates_xMultiplicity_sum]

/-- Reversing the sweep preserves its exact CNOT coordinate. -/
theorem adjacentShiftRightGates_cnotMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftRightGates word hword).map
        GateSpec.cnotMultiplicity).sum = 3 * (width - 1) := by
  simp only [adjacentShiftRightGates, List.map_reverse, List.sum_reverse,
    adjacentShiftLeftGates_cnotMultiplicity_sum]

/-- Reversing the sweep preserves its zero Toffoli coordinate. -/
theorem adjacentShiftRightGates_toffoliMultiplicity_sum
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    ((adjacentShiftRightGates word hword).map
        GateSpec.toffoliMultiplicity).sum = 0 := by
  simp only [adjacentShiftRightGates, List.map_reverse, List.sum_reverse,
    adjacentShiftLeftGates_toffoliMultiplicity_sum]

/-- Base-gate program for the adjacent-swap cyclic shift. -/
def adjacentShiftLeftProgram
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (adjacentShiftLeftGates word hword)

/-- Folded semantic action for the adjacent-swap cyclic shift. -/
def adjacentShiftLeftStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList (adjacentShiftLeftGates word hword)

/-- Base-gate program for the inverse adjacent-swap cyclic shift. -/
def adjacentShiftRightProgram
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (adjacentShiftRightGates word hword)

/-- Folded semantic action for the inverse adjacent-swap cyclic shift. -/
def adjacentShiftRightStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList (adjacentShiftRightGates word hword)

/-- Source-index permutation induced by executing adjacent swaps in list order.
If `p := adjacentSwapIndexPerm width indices`, then after running those swaps,
the readout at target index `i` is the original readout at source index
`p i`. -/
def adjacentSwapIndexPerm (width : Nat) :
    List (Fin (width - 1)) -> Equiv.Perm (Fin width)
  | [] => Equiv.refl _
  | i :: rest =>
      (adjacentSwapIndexPerm width rest).trans
        (Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i))

/-- Appending one adjacent-swap index composes that swap before the source
permutation represented by the preceding list. -/
theorem adjacentSwapIndexPerm_concat (width : Nat)
    (indices : List (Fin (width - 1))) (i : Fin (width - 1)) :
    adjacentSwapIndexPerm width (indices.concat i) =
      (Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i)).trans
        (adjacentSwapIndexPerm width indices) := by
  induction indices with
  | nil =>
      ext target
      simp [adjacentSwapIndexPerm]
  | cons j rest ih =>
      ext target
      simp only [List.concat_eq_append, List.cons_append, adjacentSwapIndexPerm,
        Equiv.trans_apply]
      rw [show adjacentSwapIndexPerm width (rest ++ [i]) target =
          adjacentSwapIndexPerm width rest
            ((Equiv.swap (adjacentLeftIndex width i)
              (adjacentRightIndex width i)) target) by
        simpa [List.concat_eq_append, Equiv.trans_apply] using
          congrArg (fun p : Equiv.Perm (Fin width) => p target) ih]

/-- Extending every adjacent-swap index by `Fin.castSucc` preserves the action
on non-last target indices. -/
theorem adjacentSwapIndexPerm_map_castSucc_apply_castSucc
    (tail : Nat) (indices : List (Fin tail)) (target : Fin tail.succ) :
    adjacentSwapIndexPerm tail.succ.succ (indices.map Fin.castSucc)
        (Fin.castSucc target) =
      Fin.castSucc (adjacentSwapIndexPerm tail.succ indices target) := by
  induction indices generalizing target with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, adjacentSwapIndexPerm, Equiv.trans_apply]
      rw [ih]
      by_cases hleft :
          adjacentSwapIndexPerm tail.succ rest target =
            adjacentLeftIndex tail.succ i
      · rw [hleft]
        simp [adjacentLeftIndex, adjacentRightIndex]
      · by_cases hright :
          adjacentSwapIndexPerm tail.succ rest target =
            adjacentRightIndex tail.succ i
        · rw [hright]
          simp [adjacentLeftIndex, adjacentRightIndex]
        · rw [Equiv.swap_apply_of_ne_of_ne hleft hright]
          rw [Equiv.swap_apply_of_ne_of_ne]
          · intro h
            apply hleft
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa [adjacentLeftIndex] using hv
          · intro h
            apply hright
            apply Fin.ext
            have hv := congrArg Fin.val h
            simpa [adjacentRightIndex] using hv

/-- Extending every adjacent-swap index by `Fin.castSucc` leaves the new last
target index fixed. -/
theorem adjacentSwapIndexPerm_map_castSucc_apply_last
    (tail : Nat) (indices : List (Fin tail)) :
    adjacentSwapIndexPerm tail.succ.succ (indices.map Fin.castSucc)
        (Fin.last tail.succ) =
      Fin.last tail.succ := by
  induction indices with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.map_cons, adjacentSwapIndexPerm, Equiv.trans_apply]
      rw [ih]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h
        have hv := congrArg Fin.val h
        simp [adjacentLeftIndex] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        simp [adjacentRightIndex] at hv
        omega

/-- The full low-to-high adjacent-swap sweep induces `finRotate` as its
source-index permutation on a nonempty word. -/
theorem adjacentSwapIndexPerm_ofFn_eq_finRotate_succ (tail : Nat) :
    adjacentSwapIndexPerm tail.succ
        (List.ofFn fun i : Fin tail =>
          (Fin.cast (by omega) i : Fin (tail.succ - 1))) =
      finRotate tail.succ := by
  induction tail with
  | zero =>
      ext target
      fin_cases target
      rfl
  | succ tail ih =>
      rw [show
          List.ofFn
              (fun i : Fin tail.succ =>
                (Fin.cast (by omega) i : Fin (tail.succ.succ - 1))) =
            (List.ofFn fun i : Fin tail =>
              (Fin.cast (by omega) (Fin.castSucc i) :
                Fin (tail.succ.succ - 1))).concat
              (Fin.cast (by omega) (Fin.last tail) :
                Fin (tail.succ.succ - 1)) by
        rw [List.ofFn_succ']]
      rw [adjacentSwapIndexPerm_concat]
      ext target
      have hih :
          adjacentSwapIndexPerm tail.succ (List.ofFn fun i : Fin tail => i) =
            finRotate tail.succ := by
        simpa using ih
      refine Fin.lastCases ?last ?cast target
      · have hq :=
          adjacentSwapIndexPerm_map_castSucc_apply_castSucc tail
            (List.ofFn fun i : Fin tail => i) (Fin.last tail)
        have hleft :
            adjacentLeftIndex (tail + 1).succ
                (Fin.cast (by omega) (Fin.last tail)) =
              Fin.castSucc (Fin.last tail) := by
          ext
          simp [adjacentLeftIndex]
        have hright :
            adjacentRightIndex (tail + 1).succ
                (Fin.cast (by omega) (Fin.last tail)) =
              Fin.last (tail + 1) := by
          ext
          simp [adjacentRightIndex]
        have hswap :
            (Equiv.swap
                (adjacentLeftIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)))
                (adjacentRightIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail))))
              (Fin.last (tail + 1)) =
            Fin.castSucc (Fin.last tail) := by
          rw [hleft, hright, Equiv.swap_apply_right]
        rw [Equiv.trans_apply, hswap]
        have hih_last := congrArg
          (fun p : Equiv.Perm (Fin tail.succ) =>
            Fin.castSucc (p (Fin.last tail))) hih
        have hq' := hq.trans hih_last
        have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq'
        simpa [List.ofFn_comp', Function.comp_def, finRotate_last] using hqv
      · intro k
        by_cases hlast : k = Fin.last tail
        · subst k
          have hq :=
            adjacentSwapIndexPerm_map_castSucc_apply_last tail
              (List.ofFn fun i : Fin tail => i)
          have hleft :
              adjacentLeftIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)) =
                Fin.castSucc (Fin.last tail) := by
            ext
            simp [adjacentLeftIndex]
          have hright :
              adjacentRightIndex (tail + 1).succ
                  (Fin.cast (by omega) (Fin.last tail)) =
                Fin.last (tail + 1) := by
            ext
            simp [adjacentRightIndex]
          have hswap :
              (Equiv.swap
                  (adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)))
                  (adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail))))
                (Fin.castSucc (Fin.last tail)) =
              Fin.last (tail + 1) := by
            rw [hleft, hright, Equiv.swap_apply_left]
          rw [Equiv.trans_apply, hswap]
          have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq
          simpa [List.ofFn_comp', Function.comp_def] using hqv
        · have hq :=
            adjacentSwapIndexPerm_map_castSucc_apply_castSucc tail
              (List.ofFn fun i : Fin tail => i) k
          have hswap :
              (Equiv.swap
                  (adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)))
                  (adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail))))
                (Fin.castSucc k) =
              Fin.castSucc k := by
            have hleft :
                adjacentLeftIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)) =
                  Fin.castSucc (Fin.last tail) := by
              ext
              simp [adjacentLeftIndex]
            have hright :
                adjacentRightIndex (tail + 1).succ
                    (Fin.cast (by omega) (Fin.last tail)) =
                  Fin.last (tail + 1) := by
              ext
              simp [adjacentRightIndex]
            rw [hleft, hright]
            rw [Equiv.swap_apply_of_ne_of_ne]
            · intro h
              apply hlast
              exact Fin.castSucc_injective _ h
            · intro h
              have hv := congrArg Fin.val h
              simp at hv
              omega
          rw [Equiv.trans_apply, hswap]
          have hih_k := congrArg
            (fun p : Equiv.Perm (Fin tail.succ) => Fin.castSucc (p k)) hih
          have hq' := hq.trans hih_k
          have hqv := congrArg (fun q : Fin (tail + 1 + 1) => q.val) hq'
          have hkadd : ((k + 1 : Fin tail.succ) : Nat) = k.val + 1 := by
            exact Fin.val_add_one_of_lt (Fin.val_lt_last hlast)
          simpa [List.ofFn_comp', Function.comp_def, hkadd] using hqv

/-- The full low-to-high adjacent-swap sweep induces `finRotate` as its
source-index permutation. -/
theorem adjacentSwapIndexPerm_ofFn_eq_finRotate (width : Nat) :
    adjacentSwapIndexPerm width (List.ofFn fun i : Fin (width - 1) => i) =
      finRotate width := by
  cases width with
  | zero =>
      ext target
      exact Fin.elim0 target
  | succ tail =>
      simpa using adjacentSwapIndexPerm_ofFn_eq_finRotate_succ tail

/-- A single adjacent swap implements the corresponding source-index
permutation on word-bit readouts. -/
theorem adjacentSwapStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) (target : Fin width) (x : Data) :
    (word.bit target).get
        (EncodedBit.swapStep
          (word.bit (adjacentLeftIndex width i))
          (word.bit (adjacentRightIndex width i))
          (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
          x) =
      (word.bit
        ((Equiv.swap (adjacentLeftIndex width i) (adjacentRightIndex width i))
          target)).get x := by
  by_cases hleft : target = adjacentLeftIndex width i
  · subst target
    rw [EncodedBit.swapStep_get_left]
    simp
  · by_cases hright : target = adjacentRightIndex width i
    · subst target
      rw [EncodedBit.swapStep_get_right]
      simp
    · calc
        (word.bit target).get
            (EncodedBit.swapStep
              (word.bit (adjacentLeftIndex width i))
              (word.bit (adjacentRightIndex width i))
              (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
              x) =
          (word.bit target).get x := by
            exact EncodedBit.swapStep_get_observed_of_swap_ne
              (word.bit (adjacentLeftIndex width i))
              (word.bit (adjacentRightIndex width i))
              (word.bit target)
              (hword _ _ (adjacentLeftIndex_ne_adjacentRightIndex width i))
              (hword _ _ (Ne.symm hleft))
              (hword _ _ (Ne.symm hright))
              x
        _ =
          (word.bit
            ((Equiv.swap (adjacentLeftIndex width i)
              (adjacentRightIndex width i)) target)).get x := by
            simp [Equiv.swap_apply_of_ne_of_ne hleft hright]

/-- An indexed adjacent-swap gate list implements its source-index
permutation on word-bit readouts. -/
theorem adjacentSwapIndexListStep_get
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1))) (target : Fin width) (x : Data) :
    (word.bit target).get
        (GateSpec.stepList (indices.flatMap (adjacentSwapGates word hword))
          x) =
      (word.bit (adjacentSwapIndexPerm width indices target)).get x := by
  induction indices generalizing target x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, GateSpec.stepList_append]
      calc
        (word.bit target).get
            (GateSpec.stepList (rest.flatMap (adjacentSwapGates word hword))
              (GateSpec.stepList (adjacentSwapGates word hword i) x)) =
          (word.bit (adjacentSwapIndexPerm width rest target)).get
              (GateSpec.stepList (adjacentSwapGates word hword i) x) := by
            exact ih target (GateSpec.stepList (adjacentSwapGates word hword i)
              x)
        _ =
          (word.bit
              ((Equiv.swap (adjacentLeftIndex width i)
                (adjacentRightIndex width i))
                (adjacentSwapIndexPerm width rest target))).get x := by
            simpa [adjacentSwapGates, EncodedBit.swapStep] using
              adjacentSwapStep_get_indexPerm word hword i
                (adjacentSwapIndexPerm width rest target) x
        _ =
          (word.bit (adjacentSwapIndexPerm width (i :: rest) target)).get x :=
            rfl

/-- The low-to-high adjacent-swap cyclic shift implements the corresponding
source-index permutation on word-bit readouts. -/
theorem adjacentShiftLeftStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin width) (x : Data) :
    (word.bit target).get (adjacentShiftLeftStep word hword x) =
      (word.bit
        (adjacentSwapIndexPerm width
          (List.ofFn fun i : Fin (width - 1) => i) target)).get x := by
  simpa [adjacentShiftLeftStep, adjacentShiftLeftGates] using
    adjacentSwapIndexListStep_get word hword
      (List.ofFn fun i : Fin (width - 1) => i) target x

/-- The low-to-high adjacent-swap cyclic shift reads each non-last target from
the next higher source bit. -/
theorem adjacentShiftLeftStep_get_castSucc
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin tail) (x : Data) :
    (word.bit (Fin.castSucc target)).get
        (adjacentShiftLeftStep word hword x) =
      (word.bit target.succ).get x := by
  have h :=
    adjacentShiftLeftStep_get_indexPerm word hword (Fin.castSucc target) x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  simpa [finRotate_apply] using h

/-- The low-to-high adjacent-swap cyclic shift wraps the last target bit from
source bit zero. -/
theorem adjacentShiftLeftStep_get_last
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    (word.bit (Fin.last tail)).get (adjacentShiftLeftStep word hword x) =
      (word.bit 0).get x := by
  have h := adjacentShiftLeftStep_get_indexPerm word hword (Fin.last tail) x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  simpa [finRotate_last] using h

/-- The adjacent-swap cyclic-shift program realizes its folded semantics. -/
theorem adjacentShiftLeft_realizes
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (adjacentShiftLeftProgram physical oracles word hword)
      (adjacentShiftLeftStep word hword) :=
  GateSpec.realizesList physical oracles (adjacentShiftLeftGates word hword)

/-- The inverse adjacent-swap cyclic-shift program realizes its folded
semantics. -/
theorem adjacentShiftRight_realizes
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (adjacentShiftRightProgram physical oracles word hword)
      (adjacentShiftRightStep word hword) :=
  GateSpec.realizesList physical oracles (adjacentShiftRightGates word hword)

/-- Direct realization proof for the adjacent-swap cyclic shift. -/
theorem adjacentShiftLeftWitness
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding (adjacentShiftLeftProgram physical oracles word hword)
      (adjacentShiftLeftStep word hword) :=
  adjacentShiftLeft_realizes physical oracles word hword

/-- Direct realization proof for the inverse adjacent-swap cyclic shift. -/
theorem adjacentShiftRightWitness
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (adjacentShiftRightProgram physical oracles word hword)
      (adjacentShiftRightStep word hword) :=
  adjacentShiftRight_realizes physical oracles word hword

/-- The inverse adjacent-swap cyclic shift undoes the low-to-high sweep. -/
theorem adjacentShiftRightStep_adjacentShiftLeftStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    adjacentShiftRightStep word hword
        (adjacentShiftLeftStep word hword x) =
      x := by
  simpa [adjacentShiftRightStep, adjacentShiftLeftStep,
    adjacentShiftRightGates] using
      GateSpec.stepList_reverse_stepList (adjacentShiftLeftGates word hword) x

/-- The low-to-high adjacent-swap cyclic shift undoes the inverse sweep. -/
theorem adjacentShiftLeftStep_adjacentShiftRightStep
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    adjacentShiftLeftStep word hword
        (adjacentShiftRightStep word hword x) =
      x := by
  have h :=
    GateSpec.stepList_reverse_stepList
      (gates := (adjacentShiftLeftGates word hword).reverse) x
  simpa [adjacentShiftRightStep, adjacentShiftLeftStep,
    adjacentShiftRightGates] using h

/-- The high-to-low inverse adjacent-swap cyclic shift implements the inverse
source-index permutation on word-bit readouts. -/
theorem adjacentShiftRightStep_get_indexPerm
    (word : Word encoding width)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin width) (x : Data) :
    (word.bit target).get (adjacentShiftRightStep word hword x) =
      (word.bit
        ((adjacentSwapIndexPerm width
          (List.ofFn fun i : Fin (width - 1) => i)).symm target)).get x := by
  let p : Equiv.Perm (Fin width) :=
    adjacentSwapIndexPerm width (List.ofFn fun i : Fin (width - 1) => i)
  have h :=
    adjacentShiftLeftStep_get_indexPerm word hword (p.symm target)
      (adjacentShiftRightStep word hword x)
  rw [adjacentShiftLeftStep_adjacentShiftRightStep] at h
  simpa [p] using h.symm

/-- The high-to-low inverse adjacent-swap cyclic shift wraps target bit zero
from the last source bit. -/
theorem adjacentShiftRightStep_get_zero
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    (word.bit 0).get (adjacentShiftRightStep word hword x) =
      (word.bit (Fin.last tail)).get x := by
  have h := adjacentShiftRightStep_get_indexPerm word hword 0 x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  have hlast : (-1 : Fin tail.succ) = Fin.last tail := by
    ext
    simp [Fin.coe_neg_one]
  simpa [finRotate_symm_apply, hlast] using h

/-- The high-to-low inverse adjacent-swap cyclic shift reads each successor
target bit from the previous lower source bit. -/
theorem adjacentShiftRightStep_get_succ
    {tail : Nat} (word : Word encoding tail.succ)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (target : Fin tail) (x : Data) :
    (word.bit target.succ).get (adjacentShiftRightStep word hword x) =
      (word.bit (Fin.castSucc target)).get x := by
  have h := adjacentShiftRightStep_get_indexPerm word hword target.succ x
  rw [adjacentSwapIndexPerm_ofFn_eq_finRotate] at h
  have hpred : (target.succ - 1 : Fin tail.succ) = Fin.castSucc target := by
    ext
    simp [Fin.val_sub_one_of_ne_zero]
  simpa [finRotate_symm_apply, hpred] using h

/-- Gates for swapping one adjacent pair of word bits under a single encoded
control bit. -/
def controlledAdjacentSwapGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    List (GateSpec encoding) :=
  EncodedBit.controlledSwapGates control
    (word.bit (adjacentLeftIndex width i))
    (word.bit (adjacentRightIndex width i))
    (hcontrol (adjacentLeftIndex width i))
    (hcontrol (adjacentRightIndex width i))
    (hword (adjacentLeftIndex width i) (adjacentRightIndex width i)
      (adjacentLeftIndex_ne_adjacentRightIndex width i))

/-- One controlled adjacent swap contains three physical leaves. -/
@[simp] theorem controlledAdjacentSwapGates_length
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    (controlledAdjacentSwapGates control word hcontrol hword i).length = 3 := by
  simp [controlledAdjacentSwapGates]

/-- One controlled adjacent swap contains no X gate. -/
@[simp] theorem controlledAdjacentSwapGates_xMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    ((controlledAdjacentSwapGates control word hcontrol hword i).map
      GateSpec.xMultiplicity).sum = 0 := by
  simp [controlledAdjacentSwapGates]

/-- One controlled adjacent swap contains no CNOT gate. -/
@[simp] theorem controlledAdjacentSwapGates_cnotMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    ((controlledAdjacentSwapGates control word hcontrol hword i).map
      GateSpec.cnotMultiplicity).sum = 0 := by
  simp [controlledAdjacentSwapGates]

/-- One controlled adjacent swap contains exactly three Toffoli gates. -/
@[simp] theorem controlledAdjacentSwapGates_toffoliMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (i : Fin (width - 1)) :
    ((controlledAdjacentSwapGates control word hcontrol hword i).map
      GateSpec.toffoliMultiplicity).sum = 3 := by
  simp [controlledAdjacentSwapGates]

/-- Gate list for a single-control cyclic shift obtained by sweeping
controlled adjacent swaps from low index to high index. -/
def controlledAdjacentShiftLeftGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin (width - 1) => i).flatMap
    (controlledAdjacentSwapGates control word hcontrol hword)

/-- Gate list for the inverse single-control cyclic shift, sweeping controlled
adjacent swaps from high index back to low index. -/
def controlledAdjacentShiftRightGates
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    List (GateSpec encoding) :=
  (controlledAdjacentShiftLeftGates control word hcontrol hword).reverse

/-- A controlled adjacent left shift is disjoint from an observed bit when
its control and every word bit are disjoint from that observation. -/
theorem controlledAdjacentShiftLeftGates_bitDisjoint
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (observed : EncodedBit encoding)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (hwordObserved : ∀ i, (word.bit i).wire ≠ observed.wire) :
    ∀ gate,
      gate ∈ controlledAdjacentShiftLeftGates control word hcontrol hword →
        GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  unfold controlledAdjacentShiftLeftGates at hgate
  simp only [List.mem_flatMap] at hgate
  rcases hgate with ⟨i, _hi, hgate⟩
  exact EncodedBit.controlledSwapGates_bitDisjoint control
    (word.bit (adjacentLeftIndex width i))
    (word.bit (adjacentRightIndex width i)) observed
    (hcontrol (adjacentLeftIndex width i))
    (hcontrol (adjacentRightIndex width i))
    (hword (adjacentLeftIndex width i) (adjacentRightIndex width i)
      (adjacentLeftIndex_ne_adjacentRightIndex width i))
    hcontrolObserved (hwordObserved _) (hwordObserved _) gate hgate

/-- The inverse controlled adjacent shift has the same noninterference
boundary as its forward gate list. -/
theorem controlledAdjacentShiftRightGates_bitDisjoint
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (observed : EncodedBit encoding)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (hwordObserved : ∀ i, (word.bit i).wire ≠ observed.wire) :
    ∀ gate,
      gate ∈ controlledAdjacentShiftRightGates control word hcontrol hword →
        GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  unfold controlledAdjacentShiftRightGates at hgate
  exact controlledAdjacentShiftLeftGates_bitDisjoint control word hcontrol
    hword observed hcontrolObserved hwordObserved gate
      (List.mem_reverse.mp hgate)

private theorem controlledAdjacentSwap_length_of_indices
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (indices : List (Fin (width - 1))) :
    (indices.flatMap
      (controlledAdjacentSwapGates control word hcontrol hword)).length =
      3 * indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      rw [List.flatMap_cons, List.length_append,
        controlledAdjacentSwapGates_length, ih]
      simp only [List.length_cons]
      omega

private theorem controlledAdjacentSwap_multiplicity_of_indices
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire)
    (multiplicity : GateSpec encoding → Nat) (count : Nat)
    (hcount : ∀ i,
      ((controlledAdjacentSwapGates control word hcontrol hword i).map
        multiplicity).sum = count)
    (indices : List (Fin (width - 1))) :
    ((indices.flatMap
      (controlledAdjacentSwapGates control word hcontrol hword)).map
        multiplicity).sum = count * indices.length := by
  induction indices with
  | nil => simp
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons]
      rw [hcount i, ih]
      simp [Nat.mul_add, Nat.add_comm]

/-- A controlled adjacent cyclic left shift has one three-Toffoli swap for
each adjacent word position. -/
theorem controlledAdjacentShiftLeftGates_length
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    (controlledAdjacentShiftLeftGates control word hcontrol hword).length =
      3 * (width - 1) := by
  unfold controlledAdjacentShiftLeftGates
  rw [controlledAdjacentSwap_length_of_indices]
  simp

/-- A controlled adjacent cyclic left shift contains no X gate. -/
theorem controlledAdjacentShiftLeftGates_xMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftLeftGates control word hcontrol hword).map
      GateSpec.xMultiplicity).sum = 0 := by
  simpa only [controlledAdjacentShiftLeftGates, List.length_ofFn,
    Nat.zero_mul] using
    (controlledAdjacentSwap_multiplicity_of_indices control word hcontrol hword
      GateSpec.xMultiplicity 0
      (controlledAdjacentSwapGates_xMultiplicity_sum control word hcontrol
        hword)
      (List.ofFn fun i : Fin (width - 1) => i))

/-- A controlled adjacent cyclic left shift contains no CNOT gate. -/
theorem controlledAdjacentShiftLeftGates_cnotMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftLeftGates control word hcontrol hword).map
      GateSpec.cnotMultiplicity).sum = 0 := by
  simpa only [controlledAdjacentShiftLeftGates, List.length_ofFn,
    Nat.zero_mul] using
    (controlledAdjacentSwap_multiplicity_of_indices control word hcontrol hword
      GateSpec.cnotMultiplicity 0
      (controlledAdjacentSwapGates_cnotMultiplicity_sum control word hcontrol
        hword)
      (List.ofFn fun i : Fin (width - 1) => i))

/-- Exact Toffoli coordinate of a controlled adjacent cyclic left shift. -/
theorem controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftLeftGates control word hcontrol hword).map
      GateSpec.toffoliMultiplicity).sum = 3 * (width - 1) := by
  simpa only [controlledAdjacentShiftLeftGates, List.length_ofFn] using
    (controlledAdjacentSwap_multiplicity_of_indices control word hcontrol hword
      GateSpec.toffoliMultiplicity 3
      (controlledAdjacentSwapGates_toffoliMultiplicity_sum control word hcontrol
        hword)
      (List.ofFn fun i : Fin (width - 1) => i))

/-- Reversing the adjacent-swap sweep preserves its exact physical length. -/
theorem controlledAdjacentShiftRightGates_length
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    (controlledAdjacentShiftRightGates control word hcontrol hword).length =
      3 * (width - 1) := by
  simpa only [controlledAdjacentShiftRightGates, List.length_reverse] using
    controlledAdjacentShiftLeftGates_length control word hcontrol hword

/-- Reversing the adjacent-swap sweep preserves its zero X coordinate. -/
theorem controlledAdjacentShiftRightGates_xMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftRightGates control word hcontrol hword).map
      GateSpec.xMultiplicity).sum = 0 := by
  simpa only [controlledAdjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    controlledAdjacentShiftLeftGates_xMultiplicity_sum control word hcontrol
      hword

/-- Reversing the adjacent-swap sweep preserves its zero CNOT coordinate. -/
theorem controlledAdjacentShiftRightGates_cnotMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftRightGates control word hcontrol hword).map
      GateSpec.cnotMultiplicity).sum = 0 := by
  simpa only [controlledAdjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    controlledAdjacentShiftLeftGates_cnotMultiplicity_sum control word hcontrol
      hword

/-- Reversing the adjacent-swap sweep preserves its exact Toffoli coordinate. -/
theorem controlledAdjacentShiftRightGates_toffoliMultiplicity_sum
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j → (word.bit i).wire ≠ (word.bit j).wire) :
    ((controlledAdjacentShiftRightGates control word hcontrol hword).map
      GateSpec.toffoliMultiplicity).sum = 3 * (width - 1) := by
  simpa only [controlledAdjacentShiftRightGates, List.map_reverse,
    List.sum_reverse] using
    controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum control word
      hcontrol hword

/-- Base-gate program for the single-control adjacent-swap cyclic shift. -/
def controlledAdjacentShiftLeftProgram
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- Folded semantic action for the single-control adjacent-swap cyclic shift. -/
def controlledAdjacentShiftLeftStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- Base-gate program for the inverse single-control adjacent-swap cyclic
shift. -/
def controlledAdjacentShiftRightProgram
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- Folded semantic action for the inverse single-control adjacent-swap cyclic
shift. -/
def controlledAdjacentShiftRightStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    Data -> Data :=
  GateSpec.stepList
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- The single-control adjacent-swap cyclic-shift program realizes its folded
semantics. -/
theorem controlledAdjacentShiftLeft_realizes
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledAdjacentShiftLeftProgram physical oracles control word hcontrol hword)
      (controlledAdjacentShiftLeftStep control word hcontrol hword) :=
  GateSpec.realizesList physical oracles
    (controlledAdjacentShiftLeftGates control word hcontrol hword)

/-- The inverse single-control adjacent-swap cyclic-shift program realizes its
folded semantics. -/
theorem controlledAdjacentShiftRight_realizes
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledAdjacentShiftRightProgram physical oracles control word hcontrol hword)
      (controlledAdjacentShiftRightStep control word hcontrol hword) :=
  GateSpec.realizesList physical oracles
    (controlledAdjacentShiftRightGates control word hcontrol hword)

/-- Direct realization proof for the controlled adjacent cyclic shift. -/
theorem controlledAdjacentShiftLeftWitness
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledAdjacentShiftLeftProgram physical oracles control word hcontrol hword)
      (controlledAdjacentShiftLeftStep control word hcontrol hword) :=
  controlledAdjacentShiftLeft_realizes physical oracles control word hcontrol hword

/-- Direct realization proof for the inverse controlled adjacent cyclic
shift. -/
theorem controlledAdjacentShiftRightWitness
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledAdjacentShiftRightProgram physical oracles control word hcontrol hword)
      (controlledAdjacentShiftRightStep control word hcontrol hword) :=
  controlledAdjacentShiftRight_realizes physical oracles control word hcontrol hword

/-- The inverse single-control adjacent-swap cyclic shift undoes the
low-to-high controlled sweep. -/
theorem controlledAdjacentShiftRightStep_controlledAdjacentShiftLeftStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    controlledAdjacentShiftRightStep control word hcontrol hword
        (controlledAdjacentShiftLeftStep control word hcontrol hword x) =
      x := by
  simpa [controlledAdjacentShiftRightStep, controlledAdjacentShiftLeftStep,
    controlledAdjacentShiftRightGates] using
      GateSpec.stepList_reverse_stepList
        (controlledAdjacentShiftLeftGates control word hcontrol hword) x

/-- The low-to-high controlled sweep undoes the inverse single-control
adjacent-swap cyclic shift. -/
theorem controlledAdjacentShiftLeftStep_controlledAdjacentShiftRightStep
    (control : EncodedBit encoding) (word : Word encoding width)
    (hcontrol : ∀ i, control.wire ≠ (word.bit i).wire)
    (hword : ∀ i j, i ≠ j -> (word.bit i).wire ≠ (word.bit j).wire)
    (x : Data) :
    controlledAdjacentShiftLeftStep control word hcontrol hword
        (controlledAdjacentShiftRightStep control word hcontrol hword x) =
      x := by
  have h :=
    GateSpec.stepList_reverse_stepList
      (gates := (controlledAdjacentShiftLeftGates control word hcontrol
        hword).reverse) x
  simpa [controlledAdjacentShiftRightStep, controlledAdjacentShiftLeftStep,
    controlledAdjacentShiftRightGates] using h

end Word

end EncodedBit

end

end QuantumAlg

end

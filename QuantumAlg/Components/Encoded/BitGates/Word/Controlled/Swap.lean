/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-!
# Controlled encoded-word swaps

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- Three-Toffoli controlled swaps for every bit of two encoded words. -/
def controlledSwapGates (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin width => i).flatMap fun i =>
    EncodedBit.controlledSwapGates control (left.bit i) (right.bit i)
      (hcontrolLeft i) (hcontrolRight i) (hleftRight i)

/-- Base-gate program for controlled bitwise swap of two encoded words. -/
def controlledSwapProgram (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Semantic action of controlled bitwise swap of two encoded words. -/
def controlledSwapStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Folded semantic action for controlled word swap over an explicit list of
indices. -/
def controlledSwapIndicesStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) :
    Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i =>
        EncodedBit.controlledSwapStep control (left.bit i) (right.bit i)
          (hcontrolLeft i) (hcontrolRight i) (hleftRight i) y) x

/-- The concrete word-swap gate list agrees with the indexed fold semantics. -/
theorem controlledSwapStep_eq_indicesStep (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight =
      controlledSwapIndicesStep control left right
        hcontrolLeft hcontrolRight hleftRight
        (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [controlledSwapStep, controlledSwapGates, controlledSwapIndicesStep,
    GateSpec.stepList_eq_foldl]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simpa [List.flatMap, EncodedBit.controlledSwapStep,
        GateSpec.stepList_eq_foldl] using
        ih
          (List.foldl (fun y gate => gate.step y) x
            (EncodedBit.controlledSwapGates control (left.bit i)
              (right.bit i) (hcontrolLeft i) (hcontrolRight i)
              (hleftRight i)))

/-- A controlled word-swap fold preserves any observed readout whose wire is
distinct from every folded left and right target bit. -/
theorem controlledSwapIndicesStep_get_observed_of_swap_ne
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (observed : EncodedBit encoding)
    (hleftObserved :
      ∀ i, i ∈ indices -> (left.bit i).wire ≠ observed.wire)
    (hrightObserved :
      ∀ i, i ∈ indices -> (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons i rest ih =>
      unfold controlledSwapIndicesStep
      change
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)) =
          observed.get x
      calc
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x))
            =
          observed.get
            (EncodedBit.controlledSwapStep control (left.bit i)
              (right.bit i) (hcontrolLeft i) (hcontrolRight i)
              (hleftRight i) x) := by
            simpa [controlledSwapIndicesStep] using
              ih
                (fun j hj => hleftObserved j (by simp [hj]))
                (fun j hj => hrightObserved j (by simp [hj]))
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x)
        _ = observed.get x := by
          exact EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit i) (right.bit i) observed
            (hcontrolLeft i) (hcontrolRight i) (hleftRight i)
            (hleftObserved i (by simp)) (hrightObserved i (by simp)) x

/-- The complete controlled word swap preserves an observed readout whose wire
is distinct from every left and right target bit. -/
theorem controlledSwapStep_get_observed_of_swap_ne
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (observed : EncodedBit encoding)
    (hleftObserved : ∀ i, (left.bit i).wire ≠ observed.wire)
    (hrightObserved : ∀ i, (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      observed.get x := by
  rw [controlledSwapStep_eq_indicesStep]
  exact
    controlledSwapIndicesStep_get_observed_of_swap_ne
      control left right hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hleftObserved i)
      (fun i _ => hrightObserved i)
      x

/-- A controlled word-swap fold sends the original right readout to the selected
left bit exactly when the control is set and the selected index is present. -/
theorem controlledSwapIndicesStep_get_left
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i -> (right.bit j).wire ≠
        (right.bit i).wire)
    (x : Data) :
    (left.bit i).get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      if i ∈ indices then
        if control.get x then (right.bit i).get x else (left.bit i).get x
      else
        (left.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledSwapIndicesStep at *
      change
        (left.bit i).get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit j)
                (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then
            if control.get x then (right.bit i).get x
            else (left.bit i).get x
          else
            (left.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (left.bit i).get
                (rest.foldl
                  (fun y j =>
                    EncodedBit.controlledSwapStep control (left.bit j)
                      (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                      (hleftRight j) y)
                  (EncodedBit.controlledSwapStep control (left.bit i)
                    (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                    (hleftRight i) x)) =
              (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x) := by
          simpa [controlledSwapIndicesStep] using
            controlledSwapIndicesStep_get_observed_of_swap_ne
              control left right hcontrolLeft hcontrolRight hleftRight
              rest (left.bit i)
              (fun k hk =>
                hleftLeft k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (fun k hk => hrightLeft k (by simp [hk]))
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)
        rw [hpreserve]
        rw [EncodedBit.controlledSwapStep_get_left]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.controlledSwapStep control (left.bit j)
              (right.bit j) (hcontrolLeft j) (hcontrolRight j)
              (hleftRight j) x)
        rw [htail]
        have hcontrol :
            control.get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              control.get x :=
          EncodedBit.controlledSwapStep_get_control control (left.bit j)
            (right.bit j) (hcontrolLeft j) (hcontrolRight j)
            (hleftRight j) x
        have hleft :
            (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (left.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (right.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hcontrol, hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- A controlled word-swap fold sends the original left readout to the selected
right bit exactly when the control is set and the selected index is present. -/
theorem controlledSwapIndicesStep_get_right
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i -> (right.bit j).wire ≠
        (right.bit i).wire)
    (x : Data) :
    (right.bit i).get
        (controlledSwapIndicesStep control left right
          hcontrolLeft hcontrolRight hleftRight indices x) =
      if i ∈ indices then
        if control.get x then (left.bit i).get x else (right.bit i).get x
      else
        (right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [controlledSwapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledSwapIndicesStep at *
      change
        (right.bit i).get
            (rest.foldl
              (fun y i =>
                EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) y)
              (EncodedBit.controlledSwapStep control (left.bit j)
                (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then
            if control.get x then (left.bit i).get x
            else (right.bit i).get x
          else
            (right.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (right.bit i).get
                (rest.foldl
                  (fun y j =>
                    EncodedBit.controlledSwapStep control (left.bit j)
                      (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                      (hleftRight j) y)
                  (EncodedBit.controlledSwapStep control (left.bit i)
                    (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                    (hleftRight i) x)) =
              (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit i)
                  (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                  (hleftRight i) x) := by
          simpa [controlledSwapIndicesStep] using
            controlledSwapIndicesStep_get_observed_of_swap_ne
              control left right hcontrolLeft hcontrolRight hleftRight
              rest (right.bit i)
              (fun k hk => hleftRightObserved k (by simp [hk]))
              (fun k hk =>
                hrightRight k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (EncodedBit.controlledSwapStep control (left.bit i)
                (right.bit i) (hcontrolLeft i) (hcontrolRight i)
                (hleftRight i) x)
        rw [hpreserve]
        rw [EncodedBit.controlledSwapStep_get_right]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.controlledSwapStep control (left.bit j)
              (right.bit j) (hcontrolLeft j) (hcontrolRight j)
              (hleftRight j) x)
        rw [htail]
        have hcontrol :
            control.get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              control.get x :=
          EncodedBit.controlledSwapStep_get_control control (left.bit j)
            (right.bit j) (hcontrolLeft j) (hcontrolRight j)
            (hleftRight j) x
        have hleft :
            (left.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (left.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.controlledSwapStep control (left.bit j)
                  (right.bit j) (hcontrolLeft j) (hcontrolRight j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.controlledSwapStep_get_observed_of_swap_ne
            control (left.bit j) (right.bit j) (right.bit i)
            (hcontrolLeft j) (hcontrolRight j) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hcontrol, hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- The complete controlled word swap sends the original right readout to the
selected left bit when the control is set. -/
theorem controlledSwapStep_get_left
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (left.bit i).get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then (right.bit i).get x else (left.bit i).get x := by
  rw [controlledSwapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledSwapIndicesStep_get_left control left right
      hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj)
      x

/-- The complete controlled word swap sends the original left readout to the
selected right bit when the control is set. -/
theorem controlledSwapStep_get_right
    (control : EncodedBit encoding) (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (right.bit i).get
        (controlledSwapStep control left right
          hcontrolLeft hcontrolRight hleftRight x) =
      if control.get x then (left.bit i).get x else (right.bit i).get x := by
  rw [controlledSwapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledSwapIndicesStep_get_right control left right
      hcontrolLeft hcontrolRight hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj)
      x

/-- The controlled word-swap program realizes its folded semantic action. -/
theorem controlledSwap_realizes (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledSwapProgram physical oracles control left right
        hcontrolLeft hcontrolRight hleftRight)
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  GateSpec.realizesList physical oracles
    (controlledSwapGates control left right
      hcontrolLeft hcontrolRight hleftRight)

/-- Direct realization proof for controlled bitwise word swap. -/
theorem controlledSwapWitness (control : EncodedBit encoding)
    (left right : Word encoding width)
    (hcontrolLeft : ∀ i, control.wire ≠ (left.bit i).wire)
    (hcontrolRight : ∀ i, control.wire ≠ (right.bit i).wire)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit.Realizes encoding
      (controlledSwapProgram physical oracles control left right
        hcontrolLeft hcontrolRight hleftRight)
      (controlledSwapStep control left right
        hcontrolLeft hcontrolRight hleftRight) :=
  controlledSwap_realizes physical oracles control left right
    hcontrolLeft hcontrolRight hleftRight

end Word

end EncodedBit

end

end QuantumAlg

end

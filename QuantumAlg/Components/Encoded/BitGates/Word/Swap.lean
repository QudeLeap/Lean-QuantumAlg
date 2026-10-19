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
# Unconditional encoded-word swaps

This module lifts the three-CNOT encoded-bit swap uniformly across two
fixed-width words.  The concrete gate list is the single source for the
program, folded semantics, direct realization proof, normalized basis endpoint,
and exact resource projections.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit
namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)
variable {environment : oracles.Interpretation}

/-- Three-CNOT swaps for every corresponding bit of two encoded words. -/
def swapGates (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    List (GateSpec encoding) :=
  (List.ofFn fun i : Fin width => i).flatMap fun i =>
    EncodedBit.swapGates (left.bit i) (right.bit i) (hleftRight i)

/-- Base-gate program for bitwise swap of two encoded words. -/
def swapProgram (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (swapGates left right hleftRight)

/-- Semantic action of bitwise swap of two encoded words. -/
def swapStep (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    Data -> Data :=
  GateSpec.stepList (swapGates left right hleftRight)

/-- A word-swap fold preserves every projection preserved by flips in both
swapped words. -/
lemma swapStep_preserves_projection
    {Projection : Type} (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (project : Data → Projection)
    (hleft : ∀ i x, project ((left.bit i).flip x) = project x)
    (hright : ∀ i x, project ((right.bit i).flip x) = project x)
    (x : Data) :
    project (swapStep left right hleftRight x) = project x := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact hright bit
  · exact hleft bit
  · exact hright bit

/-- Folded semantic action for word swap over an explicit index list. -/
def swapIndicesStep (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) : Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i =>
        EncodedBit.swapStep (left.bit i) (right.bit i) (hleftRight i) y) x

/-- The concrete word-swap gate list agrees with the indexed fold semantics. -/
lemma swapStep_eq_indicesStep (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    swapStep left right hleftRight =
      swapIndicesStep left right hleftRight
        (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [swapStep, swapGates, swapIndicesStep, GateSpec.stepList_eq_foldl]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simpa [List.flatMap, EncodedBit.swapStep,
        GateSpec.stepList_eq_foldl] using
        ih
          (List.foldl (fun y gate => gate.step y) x
            (EncodedBit.swapGates (left.bit i) (right.bit i)
              (hleftRight i)))

/-- A word-swap fold preserves an observed bit disjoint from every selected
left and right word bit. -/
lemma swapIndicesStep_get_observed_of_swap_ne
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (observed : EncodedBit encoding)
    (hleftObserved :
      ∀ i, i ∈ indices -> (left.bit i).wire ≠ observed.wire)
    (hrightObserved :
      ∀ i, i ∈ indices -> (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (swapIndicesStep left right hleftRight indices x) =
      observed.get x := by
  induction indices generalizing x with
  | nil =>
      simp [swapIndicesStep]
  | cons i rest ih =>
      unfold swapIndicesStep
      change
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.swapStep (left.bit i) (right.bit i)
                  (hleftRight i) y)
              (EncodedBit.swapStep (left.bit i) (right.bit i)
                (hleftRight i) x)) =
          observed.get x
      calc
        observed.get
            (rest.foldl
              (fun y i =>
                EncodedBit.swapStep (left.bit i) (right.bit i)
                  (hleftRight i) y)
              (EncodedBit.swapStep (left.bit i) (right.bit i)
                (hleftRight i) x)) =
          observed.get
            (EncodedBit.swapStep (left.bit i) (right.bit i)
              (hleftRight i) x) := by
            simpa [swapIndicesStep] using
              ih
                (fun j hj => hleftObserved j (by simp [hj]))
                (fun j hj => hrightObserved j (by simp [hj]))
                (EncodedBit.swapStep (left.bit i) (right.bit i)
                  (hleftRight i) x)
        _ = observed.get x := by
          exact EncodedBit.swapStep_get_observed_of_swap_ne
            (left.bit i) (right.bit i) observed (hleftRight i)
            (hleftObserved i (by simp)) (hrightObserved i (by simp)) x

/-- The complete word swap preserves an observed bit disjoint from both
words. -/
lemma swapStep_get_observed_of_swap_ne
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (observed : EncodedBit encoding)
    (hleftObserved : ∀ i, (left.bit i).wire ≠ observed.wire)
    (hrightObserved : ∀ i, (right.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get (swapStep left right hleftRight x) = observed.get x := by
  rw [swapStep_eq_indicesStep]
  exact
    swapIndicesStep_get_observed_of_swap_ne left right hleftRight
      (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hleftObserved i) (fun i _ => hrightObserved i) x

/-- A word-swap fold sends the original right readout to the selected left bit
exactly when the selected index occurs in the fold. -/
lemma swapIndicesStep_get_left
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i ->
        (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i ->
        (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (left.bit i).get
        (swapIndicesStep left right hleftRight indices x) =
      if i ∈ indices then (right.bit i).get x else (left.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [swapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold swapIndicesStep at *
      change
        (left.bit i).get
            (rest.foldl
              (fun y k =>
                EncodedBit.swapStep (left.bit k) (right.bit k)
                  (hleftRight k) y)
              (EncodedBit.swapStep (left.bit j) (right.bit j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then (right.bit i).get x
          else (left.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (left.bit i).get
                (rest.foldl
                  (fun y k =>
                    EncodedBit.swapStep (left.bit k) (right.bit k)
                      (hleftRight k) y)
                  (EncodedBit.swapStep (left.bit i) (right.bit i)
                    (hleftRight i) x)) =
              (left.bit i).get
                (EncodedBit.swapStep (left.bit i) (right.bit i)
                  (hleftRight i) x) := by
          simpa [swapIndicesStep] using
            swapIndicesStep_get_observed_of_swap_ne
              left right hleftRight rest (left.bit i)
              (fun k hk =>
                hleftLeft k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (fun k hk => hrightLeft k (by simp [hk]))
              (EncodedBit.swapStep (left.bit i) (right.bit i)
                (hleftRight i) x)
        rw [hpreserve, EncodedBit.swapStep_get_left]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.swapStep (left.bit j) (right.bit j)
              (hleftRight j) x)
        rw [htail]
        have hleft :
            (left.bit i).get
                (EncodedBit.swapStep (left.bit j) (right.bit j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.swapStep_get_observed_of_swap_ne
            (left.bit j) (right.bit j) (left.bit i) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.swapStep (left.bit j) (right.bit j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.swapStep_get_observed_of_swap_ne
            (left.bit j) (right.bit j) (right.bit i) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- A word-swap fold sends the original left readout to the selected right bit
exactly when the selected index occurs in the fold. -/
lemma swapIndicesStep_get_right
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ∈ indices -> j ≠ i ->
        (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft :
      ∀ j, j ∈ indices -> (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved :
      ∀ j, j ∈ indices -> (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ∈ indices -> j ≠ i ->
        (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (right.bit i).get
        (swapIndicesStep left right hleftRight indices x) =
      if i ∈ indices then (left.bit i).get x else (right.bit i).get x := by
  induction indices generalizing x with
  | nil =>
      simp [swapIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold swapIndicesStep at *
      change
        (right.bit i).get
            (rest.foldl
              (fun y k =>
                EncodedBit.swapStep (left.bit k) (right.bit k)
                  (hleftRight k) y)
              (EncodedBit.swapStep (left.bit j) (right.bit j)
                (hleftRight j) x)) =
          if i ∈ j :: rest then (left.bit i).get x
          else (right.bit i).get x
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (right.bit i).get
                (rest.foldl
                  (fun y k =>
                    EncodedBit.swapStep (left.bit k) (right.bit k)
                      (hleftRight k) y)
                  (EncodedBit.swapStep (left.bit i) (right.bit i)
                    (hleftRight i) x)) =
              (right.bit i).get
                (EncodedBit.swapStep (left.bit i) (right.bit i)
                  (hleftRight i) x) := by
          simpa [swapIndicesStep] using
            swapIndicesStep_get_observed_of_swap_ne
              left right hleftRight rest (right.bit i)
              (fun k hk => hleftRightObserved k (by simp [hk]))
              (fun k hk =>
                hrightRight k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (EncodedBit.swapStep (left.bit i) (right.bit i)
                (hleftRight i) x)
        rw [hpreserve, EncodedBit.swapStep_get_right]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => hleftLeft k (by simp [hk]) hki)
            (fun k hk => hrightLeft k (by simp [hk]))
            (fun k hk => hleftRightObserved k (by simp [hk]))
            (fun k hk hki => hrightRight k (by simp [hk]) hki)
            (EncodedBit.swapStep (left.bit j) (right.bit j)
              (hleftRight j) x)
        rw [htail]
        have hleft :
            (left.bit i).get
                (EncodedBit.swapStep (left.bit j) (right.bit j)
                  (hleftRight j) x) =
              (left.bit i).get x :=
          EncodedBit.swapStep_get_observed_of_swap_ne
            (left.bit j) (right.bit j) (left.bit i) (hleftRight j)
            (hleftLeft j (by simp) hji) (hrightLeft j (by simp)) x
        have hright :
            (right.bit i).get
                (EncodedBit.swapStep (left.bit j) (right.bit j)
                  (hleftRight j) x) =
              (right.bit i).get x :=
          EncodedBit.swapStep_get_observed_of_swap_ne
            (left.bit j) (right.bit j) (right.bit i) (hleftRight j)
            (hleftRightObserved j (by simp))
            (hrightRight j (by simp) hji) x
        rw [hleft, hright]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest <;> simp [hji', himem]

/-- The complete word swap sends each original right readout to the
corresponding left bit. -/
lemma swapStep_get_left
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (left.bit i).get (swapStep left right hleftRight x) =
      (right.bit i).get x := by
  rw [swapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    swapIndicesStep_get_left left right hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj) x

/-- The complete word swap sends each original left readout to the
corresponding right bit. -/
lemma swapStep_get_right
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (i : Fin width)
    (hleftLeft :
      ∀ j, j ≠ i -> (left.bit j).wire ≠ (left.bit i).wire)
    (hrightLeft : ∀ j, (right.bit j).wire ≠ (left.bit i).wire)
    (hleftRightObserved : ∀ j, (left.bit j).wire ≠ (right.bit i).wire)
    (hrightRight :
      ∀ j, j ≠ i -> (right.bit j).wire ≠ (right.bit i).wire)
    (x : Data) :
    (right.bit i).get (swapStep left right hleftRight x) =
      (left.bit i).get x := by
  rw [swapStep_eq_indicesStep]
  have hnodup : (List.ofFn fun j : Fin width => j).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    swapIndicesStep_get_right left right hleftRight
      (List.ofFn fun j : Fin width => j) hnodup i
      (fun j _ hj => hleftLeft j hj)
      (fun j _ => hrightLeft j)
      (fun j _ => hleftRightObserved j)
      (fun j _ hj => hrightRight j hj) x

/-- Whole-word left readout endpoint under pairwise-disjoint word layouts. -/
lemma swapStep_get_left_word
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (hleftDistinct :
      ∀ i j, i ≠ j -> (left.bit i).wire ≠ (left.bit j).wire)
    (hrightDistinct :
      ∀ i j, i ≠ j -> (right.bit i).wire ≠ (right.bit j).wire)
    (hcross : ∀ i j, (left.bit i).wire ≠ (right.bit j).wire)
    (x : Data) :
    (fun i => (left.bit i).get (swapStep left right hleftRight x)) =
      fun i => (right.bit i).get x := by
  funext i
  exact swapStep_get_left left right hleftRight i
    (fun j hji => hleftDistinct j i hji)
    (fun j => Ne.symm (hcross i j))
    (fun j => hcross j i)
    (fun j hji => hrightDistinct j i hji) x

/-- Whole-word right readout endpoint under pairwise-disjoint word layouts. -/
lemma swapStep_get_right_word
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (hleftDistinct :
      ∀ i j, i ≠ j -> (left.bit i).wire ≠ (left.bit j).wire)
    (hrightDistinct :
      ∀ i j, i ≠ j -> (right.bit i).wire ≠ (right.bit j).wire)
    (hcross : ∀ i j, (left.bit i).wire ≠ (right.bit j).wire)
    (x : Data) :
    (fun i => (right.bit i).get (swapStep left right hleftRight x)) =
      fun i => (left.bit i).get x := by
  funext i
  exact swapStep_get_right left right hleftRight i
    (fun j hji => hleftDistinct j i hji)
    (fun j => Ne.symm (hcross i j))
    (fun j => hcross j i)
    (fun j hji => hrightDistinct j i hji) x

/-- Swapping two zero-width words is the identity semantic action. -/
lemma swapStep_eq_id_of_width_zero
    (left right : Word encoding 0)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    swapStep left right hleftRight = id := by
  funext x
  simp [swapStep, swapGates, GateSpec.stepList]

/-- The word-swap program realizes its folded semantic action. -/
lemma swap_realizes (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit.Realizes encoding
      (swapProgram physical oracles left right hleftRight) environment
      (swapStep left right hleftRight) :=
  GateSpec.realizesList physical oracles (swapGates left right hleftRight) environment

/-- Direct realization proof for bitwise swap of two encoded words. -/
lemma swapWitness (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit.Realizes encoding (swapProgram physical oracles left right hleftRight)
      environment
      (swapStep left right hleftRight) :=
  swap_realizes physical oracles left right hleftRight

/-- Typed circuit folded from the exact word-swap program. -/
def swapCircuit (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  swapProgram physical oracles left right hleftRight

/-- Normalized encoded-basis endpoint of the exact word-swap circuit. -/
lemma swapCircuit_applyNormalized_encoded_ket
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (x : Data) :
    (swapCircuit physical oracles left right hleftRight).applyNormalized environment
        (NormalizedVector.ket (physical.basisEquiv.symm (encoding.encode x))) =
      NormalizedVector.ket
        (physical.basisEquiv.symm (encoding.encode (swapStep left right hleftRight x))) :=
  (swapWitness physical oracles left right hleftRight).apply_encoded_ket x

/-- The exact gate list contains three CNOTs per word bit. -/
lemma swapGates_length (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    (swapGates left right hleftRight).length = 3 * width := by
  simp [swapGates, EncodedBit.swapGates, List.length_flatMap,
    Function.comp_def, Nat.mul_comm]

/-- The exact gate list contains three CNOTs per word bit. -/
@[simp] lemma swapGates_cnotMultiplicity_sum
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    ((swapGates left right hleftRight).map
        GateSpec.cnotMultiplicity).sum = 3 * width := by
  have hsum :
      ∀ indices : List (Fin width),
        ((indices.flatMap fun i =>
            EncodedBit.swapGates (left.bit i) (right.bit i)
              (hleftRight i)).map GateSpec.cnotMultiplicity).sum =
          3 * indices.length := by
    intro indices
    induction indices with
    | nil => rfl
    | cons i rest ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          EncodedBit.swapGates, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, GateSpec.cnotMultiplicity_cnot, List.length_cons]
        have ih' :
            ((rest.flatMap fun j =>
                [ GateSpec.cnot (left.bit j) (right.bit j) (hleftRight j)
                , GateSpec.cnot (right.bit j) (left.bit j)
                    (Ne.symm (hleftRight j))
                , GateSpec.cnot (left.bit j) (right.bit j)
                    (hleftRight j) ]).map
              GateSpec.cnotMultiplicity).sum = 3 * rest.length := by
          simpa only [EncodedBit.swapGates] using ih
        rw [ih']
        omega
  simpa only [swapGates, List.length_ofFn] using
    hsum (List.ofFn fun i : Fin width => i)


/-- A literal word swap contains no Toffoli gate. -/
lemma swapGates_toffoliMultiplicity_sum
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    ((swapGates left right hleftRight).map
        GateSpec.toffoliMultiplicity).sum = 0 := by
  unfold swapGates
  generalize (List.ofFn fun i : Fin width => i) = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        EncodedBit.swapGates, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, GateSpec.toffoliMultiplicity_cnot, Nat.zero_add]
      have ih' :
          ((rest.flatMap fun i =>
              [ GateSpec.cnot (left.bit i) (right.bit i) (hleftRight i)
              , GateSpec.cnot (right.bit i) (left.bit i)
                  (Ne.symm (hleftRight i))
              , GateSpec.cnot (left.bit i) (right.bit i)
                  (hleftRight i) ]).map
            GateSpec.toffoliMultiplicity).sum = 0 := by
        simpa only [EncodedBit.swapGates] using ih
      exact ih'

/-- The word-swap program emits exactly three targeted primitive events per bit. -/
lemma swapProgram_primitiveEventCount (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    GateSpec.primitiveEventCount (swapProgram physical oracles left right hleftRight) =
      3 * width := by
  rw [swapProgram, GateSpec.primitiveEventCount_programList,
    swapGates_length]

private def isCnotGate : GateSpec encoding -> Prop
  | .cnot _ _ _ => True
  | _ => False

private lemma swapGates_isCnot (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    ∀ gate, gate ∈ swapGates left right hleftRight -> isCnotGate gate := by
  intro gate hgate
  simp only [swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨i, _hi, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with hgate | hgate | hgate <;> subst gate <;>
    trivial



private lemma cnotList_eventCount (gates : List (GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isCnotGate gate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (GateSpec.programList physical oracles gates).eventCost = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isCnotGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isCnotGate] at hgate
      | cnot control target hct =>
          change
            ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
                (ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
                    (.gate .cnot) +
                  (GateSpec.programList physical oracles rest).eventCost) =
              (GateSpec.cnot control target hct :: rest).length
          rw [ResourcePool.count_add, ResourcePool.count_singleton_self,
            ih hrest]
          change 1 + rest.length = rest.length + 1
          exact Nat.add_comm _ _
      | toffoli controlA controlB target hab ha hb =>
          simp [isCnotGate] at hgate



private lemma cnotList_unitEventDepth (gates : List (GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isCnotGate gate) :
    (GateSpec.programList physical oracles gates).evaluatedEventDepth (fun _ => 1) =
      gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isCnotGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isCnotGate] at hgate
      | cnot control target hct =>
          change
            1 +
                (GateSpec.programList physical oracles rest).evaluatedEventDepth (fun _ => 1) =
              (GateSpec.cnot control target hct :: rest).length
          simp [ih hrest, Nat.add_comm]
      | toffoli controlA controlB target hab ha hb =>
          simp [isCnotGate] at hgate



private lemma cnotList_eventQueryDepth (gates : List (GateSpec encoding))
    (hall : ∀ gate, gate ∈ gates → isCnotGate gate) :
    (GateSpec.programList physical oracles gates).eventQueryDepth
        (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .cnot) =
      gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      have hgate := hall gate (by simp)
      have hrest : ∀ next, next ∈ rest → isCnotGate next :=
        fun next hnext => hall next (by simp [hnext])
      cases gate with
      | x target => simp [isCnotGate] at hgate
      | cnot control target hct =>
          change
            1 +
                (GateSpec.programList physical oracles rest).eventQueryDepth
                  (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .cnot) =
              (GateSpec.cnot control target hct :: rest).length
          simp [ih hrest, Nat.add_comm]
      | toffoli controlA controlB target hab ha hb =>
          simp [isCnotGate] at hgate



/-- Exact CNOT-event coefficient in the circuit's strict event pool. -/
lemma swapCircuit_cnot_eventCount (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (swapCircuit physical oracles left right hleftRight).eventCost =
      3 * width := by
  change
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (GateSpec.programList physical oracles (swapGates left right hleftRight)).eventCost =
      3 * width
  rw [cnotList_eventCount physical oracles (swapGates left right hleftRight)
    (swapGates_isCnot left right hleftRight)]
  exact swapGates_length left right hleftRight



/-- Exact unit-weight strict event depth of the sequential circuit. -/
lemma swapCircuit_unit_eventDepth (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    (swapCircuit physical oracles left right hleftRight).evaluatedEventDepth (fun _ => 1) =
      3 * width := by
  change
    (GateSpec.programList physical oracles
        (swapGates left right hleftRight)).evaluatedEventDepth (fun _ => 1) =
      3 * width
  rw [cnotList_unitEventDepth physical oracles (swapGates left right hleftRight)
    (swapGates_isCnot left right hleftRight)]
  exact swapGates_length left right hleftRight



/-- Exact CNOT-event query depth of the sequential circuit. -/
lemma swapCircuit_cnot_eventQueryDepth (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    (swapCircuit physical oracles left right hleftRight).eventQueryDepth
        (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .cnot) =
      3 * width := by
  change
    (GateSpec.programList physical oracles
        (swapGates left right hleftRight)).eventQueryDepth
          (Resource.Event.gate (model := .quantum AlgorithmGate.model oracles) .cnot) = 3 * width
  rw [cnotList_eventQueryDepth physical oracles (swapGates left right hleftRight)
    (swapGates_isCnot left right hleftRight)]
  exact swapGates_length left right hleftRight



/-- Strict event linearization and the event pool agree for word swap. -/
lemma swapCircuit_resourcesFromEventDepth_eq_eventCost
    (left right : Word encoding width)
    (hleftRight : ∀ i, (left.bit i).wire ≠ (right.bit i).wire) :
    (swapCircuit physical oracles left right hleftRight).resourcesFromEventDepth =
      (swapCircuit physical oracles left right hleftRight).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost
    (swapCircuit physical oracles left right hleftRight)

end Word
end EncodedBit

end

end QuantumAlg

end

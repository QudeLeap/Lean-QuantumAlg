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

/-!
# Encoded-word xor

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- A fixed-width semantic word represented by encoded bit lenses over one
shared binary label encoding.  This records only the bit-level accessors; word
arithmetic semantics are supplied by the arithmetic modules that instantiate
the lenses. -/
structure Word (encoding : BinaryLabelEncoding Data) (width : Nat) where
  /-- Semantic bit lens for one word position. -/
  bit : Fin width → EncodedBit encoding

namespace Word

variable {width : Nat}

/-- The lower endpoint of an adjacent pair inside a word. -/
def adjacentLeftIndex (width : Nat) (i : Fin (width - 1)) : Fin width :=
  ⟨i.val, by omega⟩

/-- The upper endpoint of an adjacent pair inside a word. -/
def adjacentRightIndex (width : Nat) (i : Fin (width - 1)) : Fin width :=
  ⟨i.val + 1, by omega⟩

/-- Adjacent endpoints are distinct. -/
theorem adjacentLeftIndex_ne_adjacentRightIndex
    (width : Nat) (i : Fin (width - 1)) :
    adjacentLeftIndex width i ≠ adjacentRightIndex width i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [adjacentLeftIndex, adjacentRightIndex] at hv
  omega

/-- CNOT gates that xor each source word bit into the corresponding target
word bit. -/
def xorIntoGates (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    List (GateSpec encoding) :=
  List.ofFn fun i => GateSpec.cnot (source.bit i) (target.bit i) (hdisjoint i)

/-- A literal word xor contains one CNOT per word bit. -/
@[simp] theorem xorIntoGates_length (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    (xorIntoGates source target hdisjoint).length = width := by
  simp [xorIntoGates]

/-- A literal word xor contains exactly one CNOT per word bit. -/
@[simp] theorem xorIntoGates_cnotMultiplicity_sum
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    ((xorIntoGates source target hdisjoint).map
        GateSpec.cnotMultiplicity).sum = width := by
  simp [xorIntoGates, List.sum_ofFn]

/-- A literal word xor contains no Toffoli gate. -/
theorem xorIntoGates_toffoliMultiplicity_sum
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    ((xorIntoGates source target hdisjoint).map
        GateSpec.toffoliMultiplicity).sum = 0 := by
  apply List.sum_eq_zero
  intro count hcount
  rcases List.mem_map.mp hcount with ⟨gate, hgate, rfl⟩
  rw [xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨_bit, rfl⟩
  rfl

/-- Base-gate program for bitwise xor from one encoded word into another. -/
def xorIntoProgram (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles (xorIntoGates source target hdisjoint)

/-- Semantic action of the bitwise xor-into program. -/
def xorIntoStep (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    Data → Data :=
  GateSpec.stepList (xorIntoGates source target hdisjoint)

/-- A word-xor fold preserves every projection preserved by each target-bit
flip. -/
theorem xorIntoStep_preserves_projection
    {Projection : Type} (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (project : Data → Projection)
    (hpreserve : ∀ i x, project ((target.bit i).flip x) = project x)
    (x : Data) :
    project (xorIntoStep source target hdisjoint x) = project x := by
  apply GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact hpreserve bit

/-- The bitwise xor-into program realizes its folded semantic action. -/
theorem xorInto_realizes (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    UnitaryCircuit.Realizes encoding
      (xorIntoProgram physical oracles source target hdisjoint)
      (xorIntoStep source target hdisjoint) :=
  GateSpec.realizesList physical oracles (xorIntoGates source target hdisjoint)

/-- Direct realization proof for bitwise xor into another encoded word. -/
theorem xorIntoWitness (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    UnitaryCircuit.Realizes encoding (xorIntoProgram physical oracles source target hdisjoint)
      (xorIntoStep source target hdisjoint) :=
  xorInto_realizes physical oracles source target hdisjoint

/-- Folded semantic action for word xor over an explicit list of indices. -/
def xorIntoIndicesStep (source target : Word encoding width)
    (indices : List (Fin width)) : Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i => cnotStep (source.bit i) (target.bit i) y) x

/-- The concrete `List.ofFn` word-xor gate list agrees with the indexed fold
semantics. -/
theorem xorIntoStep_eq_indicesStep (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    xorIntoStep source target hdisjoint =
      xorIntoIndicesStep source target (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [xorIntoStep, xorIntoGates, xorIntoIndicesStep,
    GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.cnot (source.bit i) (target.bit i) (hdisjoint i)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin width => i)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin width => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin width => i) gateOfIndex)]
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

/-- A word-xor fold preserves any observed readout whose wire is distinct from
every folded target bit. -/
theorem xorIntoIndicesStep_get_observed_of_target_ne
    (source target : Word encoding width) (indices : List (Fin width))
    (observed : EncodedBit encoding)
    (hne : ∀ i, i ∈ indices -> (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorIntoIndicesStep source target indices x) =
      observed.get x := by
  unfold xorIntoIndicesStep
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i => cnotStep (source.bit i) (target.bit i) y)
              (cnotStep (source.bit i) (target.bit i) x)) =
          observed.get x
      rw [ih]
      · exact cnotStep_get_of_target_ne (source.bit i) (target.bit i)
          observed (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

/-- A word-xor fold toggles a target bit exactly when its index is present in
the folded index list. -/
theorem xorIntoIndicesStep_get_target
    (source target : Word encoding width) (indices : List (Fin width))
    (hnodup : indices.Nodup) (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get (xorIntoIndicesStep source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [xorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold xorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => cnotStep (source.bit j) (target.bit j) y)
              (cnotStep (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then (source.bit i).get x else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j => cnotStep (source.bit j) (target.bit j) y)
                  (cnotStep (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (cnotStep (source.bit i) (target.bit i) x) := by
          simpa [xorIntoIndicesStep] using
            xorIntoIndicesStep_get_observed_of_target_ne
              source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (cnotStep (source.bit i) (target.bit i) x)
        rw [hpreserve, cnotStep_get_target]
        simp [hjNotMem]
      · have htail := ih hrestNodup (cnotStep
            (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (cnotStep (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          cnotStep_get_of_target_ne (source.bit j) (target.bit j)
            (target.bit i) (htargetTarget j hji) x
        have hsource :
            (source.bit i).get
                (cnotStep (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          cnotStep_get_of_target_ne (source.bit j) (target.bit j)
            (source.bit i) (htargetSource j) x
        rw [htarget, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- The complete word-xor fold preserves an observed readout whose wire is
distinct from every target bit. -/
theorem xorIntoStep_get_observed_of_target_ne
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get (xorIntoStep source target hdisjoint x) =
      observed.get x := by
  rw [xorIntoStep_eq_indicesStep]
  exact
    xorIntoIndicesStep_get_observed_of_target_ne
      source target (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hne i) x

/-- The complete word-xor fold toggles each target bit by the corresponding
source bit. -/
theorem xorIntoStep_get_target
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get (xorIntoStep source target hdisjoint x) =
      ((target.bit i).get x ^^ (source.bit i).get x) := by
  rw [xorIntoStep_eq_indicesStep]
  have hnodup : (List.ofFn fun i : Fin width => i).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    xorIntoIndicesStep_get_target source target
      (List.ofFn fun j : Fin width => j) hnodup i htargetTarget
      htargetSource x

end Word

end EncodedBit

end

end QuantumAlg

end

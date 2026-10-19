/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Controlled encoded-word xor

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- Toffoli gates that xor each source word bit into the corresponding target
word bit when the shared control bit is set. -/
def controlledXorIntoGates (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    List (GateSpec encoding) :=
  List.ofFn fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)

/-- A literal controlled word xor contains one Toffoli per word bit. -/
@[simp] lemma controlledXorIntoGates_length (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    (controlledXorIntoGates control source target hcontrolSource
      hcontrolTarget hsourceTarget).length = width := by
  simp [controlledXorIntoGates]

/-- The exact Toffoli coordinate of a literal controlled word xor is its
word width. -/
lemma controlledXorIntoGates_toffoliMultiplicity_sum
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    ((controlledXorIntoGates control source target hcontrolSource
        hcontrolTarget hsourceTarget).map
      GateSpec.toffoliMultiplicity).sum = width := by
  have hones :
      (controlledXorIntoGates control source target hcontrolSource
          hcontrolTarget hsourceTarget).map GateSpec.toffoliMultiplicity =
        (controlledXorIntoGates control source target hcontrolSource
          hcontrolTarget hsourceTarget).map (fun _ => 1) := by
    apply List.map_congr_left
    intro gate hgate
    rw [controlledXorIntoGates] at hgate
    rcases List.mem_ofFn.mp hgate with ⟨_bit, rfl⟩
    rfl
  calc
    _ = ((controlledXorIntoGates control source target hcontrolSource
          hcontrolTarget hsourceTarget).map (fun _ => 1)).sum :=
      congrArg List.sum hones
    _ = (controlledXorIntoGates control source target hcontrolSource
          hcontrolTarget hsourceTarget).length := by simp
    _ = width := controlledXorIntoGates_length control source target
      hcontrolSource hcontrolTarget hsourceTarget

/-- Base-gate program for controlled bitwise xor from one encoded word into
another. -/
def controlledXorIntoProgram (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  GateSpec.programList physical oracles
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Semantic action of controlled bitwise xor from one encoded word into
another. -/
def controlledXorIntoStep (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    Data → Data :=
  GateSpec.stepList
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Folded semantic action for controlled word xor over an explicit list of
indices. -/
def controlledXorIntoIndicesStep (control : EncodedBit encoding)
    (source target : Word encoding width) (indices : List (Fin width)) :
    Data -> Data :=
  fun x =>
    indices.foldl
      (fun y i => toffoliStep control (source.bit i) (target.bit i) y) x

/-- The concrete `List.ofFn` controlled-xor gate list agrees with the indexed
fold semantics. -/
lemma controlledXorIntoStep_eq_indicesStep (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget =
      controlledXorIntoIndicesStep control source target
        (List.ofFn fun i : Fin width => i) := by
  funext x
  rw [controlledXorIntoStep, controlledXorIntoGates,
    controlledXorIntoIndicesStep, GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)
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

/-- A false shared control makes the complete physical controlled-word xor
act as the identity. -/
lemma controlledXorIntoStep_of_control_false
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (state : Data) (hcontrol : control.get state = false) :
    controlledXorIntoStep control source target
      hcontrolSource hcontrolTarget hsourceTarget state = state := by
  rw [controlledXorIntoStep_eq_indicesStep]
  unfold controlledXorIntoIndicesStep
  generalize List.ofFn (fun i : Fin width => i) = indices
  induction indices generalizing state with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.foldl_cons]
      have hstep :
          toffoliStep control (source.bit bit) (target.bit bit) state = state := by
        unfold toffoliStep
        rw [hcontrol]
        rfl
      rw [hstep]
      exact ih state hcontrol

/-- A controlled word-xor fold preserves any observed readout whose wire is
distinct from every folded target bit. -/
lemma controlledXorIntoIndicesStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (observed : EncodedBit encoding)
    (hne : ∀ i, i ∈ indices -> (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorIntoIndicesStep control source target indices x) =
      observed.get x := by
  unfold controlledXorIntoIndicesStep
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      change
        observed.get
            (rest.foldl
              (fun y i => toffoliStep control (source.bit i) (target.bit i) y)
              (toffoliStep control (source.bit i) (target.bit i) x)) =
          observed.get x
      rw [ih]
      · exact toffoliStep_get_of_target_ne control (source.bit i)
          (target.bit i) observed (hne i (by simp)) x
      · intro j hj
        exact hne j (by simp [hj])

/-- A controlled word-xor fold toggles a target bit exactly when its index is
present in the folded index list.  The extra hypotheses state that target wires
are independent of this observed target, the shared control, and the matching
source bit throughout the fold. -/
lemma controlledXorIntoIndicesStep_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoIndicesStep control source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then control.get x && (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [controlledXorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledXorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => toffoliStep control (source.bit j) (target.bit j) y)
              (toffoliStep control (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then
              control.get x && (source.bit i).get x
            else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j =>
                    toffoliStep control (source.bit j) (target.bit j) y)
                  (toffoliStep control (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (toffoliStep control (source.bit i) (target.bit i) x) := by
          simpa [controlledXorIntoIndicesStep] using
            controlledXorIntoIndicesStep_get_observed_of_target_ne
              control source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (toffoliStep control (source.bit i) (target.bit i) x)
        rw [hpreserve, toffoliStep_get_target]
        simp [hjNotMem]
      · have htail := ih hrestNodup
            (toffoliStep control (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (target.bit i) (htargetTarget j hji) x
        have hcontrol :
            control.get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              control.get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) control (htargetControl j) x
        have hsource :
            (source.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (source.bit i) (htargetSource j) x
        rw [htarget, hcontrol, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- A controlled word-xor fold toggles a target bit exactly when its index is
present in the folded index list.  This variant only requires the target-wire
separation hypotheses for indices actually present in the folded list, which
is useful for filtered arithmetic networks whose target word is only injective
on the selected index set. -/
lemma controlledXorIntoIndicesStep_get_target_of_mem
    (control : EncodedBit encoding) (source target : Word encoding width)
    (indices : List (Fin width)) (hnodup : indices.Nodup)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ∈ indices → j ≠ i → (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl :
      ∀ j, j ∈ indices → (target.bit j).wire ≠ control.wire)
    (htargetSource :
      ∀ j, j ∈ indices → (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoIndicesStep control source target indices x) =
      ((target.bit i).get x ^^
        (if i ∈ indices then control.get x && (source.bit i).get x else false)) := by
  induction indices generalizing x with
  | nil =>
      simp [controlledXorIntoIndicesStep]
  | cons j rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hjNotMem : j ∉ rest := hnodup.notMem
      unfold controlledXorIntoIndicesStep at *
      change
        (target.bit i).get
            (rest.foldl
              (fun y j => toffoliStep control (source.bit j) (target.bit j) y)
              (toffoliStep control (source.bit j) (target.bit j) x)) =
          ((target.bit i).get x ^^
            (if i ∈ j :: rest then
              control.get x && (source.bit i).get x
            else false))
      by_cases hji : j = i
      · subst j
        have hpreserve :
            (target.bit i).get
                (rest.foldl
                  (fun y j =>
                    toffoliStep control (source.bit j) (target.bit j) y)
                  (toffoliStep control (source.bit i) (target.bit i) x)) =
              (target.bit i).get
                (toffoliStep control (source.bit i) (target.bit i) x) := by
          simpa [controlledXorIntoIndicesStep] using
            controlledXorIntoIndicesStep_get_observed_of_target_ne
              control source target rest (target.bit i)
              (fun k hk =>
                htargetTarget k (by simp [hk])
                  (by
                    intro hki
                    subst k
                    exact hjNotMem hk))
              (toffoliStep control (source.bit i) (target.bit i) x)
        rw [hpreserve, toffoliStep_get_target]
        simp [hjNotMem]
      · have htail :=
          ih hrestNodup
            (fun k hk hki => htargetTarget k (by simp [hk]) hki)
            (fun k hk => htargetControl k (by simp [hk]))
            (fun k hk => htargetSource k (by simp [hk]))
            (toffoliStep control (source.bit j) (target.bit j) x)
        rw [htail]
        have htarget :
            (target.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (target.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (target.bit i)
            (htargetTarget j (by simp) hji) x
        have hcontrol :
            control.get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              control.get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) control (htargetControl j (by simp)) x
        have hsource :
            (source.bit i).get
                (toffoliStep control (source.bit j) (target.bit j) x) =
              (source.bit i).get x :=
          toffoliStep_get_of_target_ne control (source.bit j)
            (target.bit j) (source.bit i) (htargetSource j (by simp)) x
        rw [htarget, hcontrol, hsource]
        have hji' : i ≠ j := Ne.symm hji
        by_cases himem : i ∈ rest
        · simp [hji', himem]
        · simp [hji', himem]

/-- The complete controlled word-xor fold preserves an observed readout whose
wire is distinct from every target bit. -/
lemma controlledXorIntoStep_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (controlledXorIntoStep control source target
          hcontrolSource hcontrolTarget hsourceTarget x) =
      observed.get x := by
  rw [controlledXorIntoStep_eq_indicesStep]
  exact
    controlledXorIntoIndicesStep_get_observed_of_target_ne
      control source target (List.ofFn fun i : Fin width => i) observed
      (fun i _ => hne i) x

/-- The complete controlled word-xor fold toggles each target bit by the
corresponding controlled source bit. -/
lemma controlledXorIntoStep_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (controlledXorIntoStep control source target
          hcontrolSource hcontrolTarget hsourceTarget x) =
      ((target.bit i).get x ^^
        (control.get x && (source.bit i).get x)) := by
  rw [controlledXorIntoStep_eq_indicesStep]
  have hnodup : (List.ofFn fun i : Fin width => i).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : i ∈ (List.ofFn fun j : Fin width => j) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  simpa [hmem] using
    controlledXorIntoIndicesStep_get_target control source target
      (List.ofFn fun j : Fin width => j) hnodup i
      htargetTarget htargetControl htargetSource x

/-- The reversed controlled word-xor gate list agrees with the indexed fold
over the reversed index list. -/
lemma controlledXorIntoGates_reverse_stepList_eq_indicesStep
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire) :
    GateSpec.stepList
        (controlledXorIntoGates control source target
          hcontrolSource hcontrolTarget hsourceTarget).reverse =
      controlledXorIntoIndicesStep control source target
        (List.ofFn fun i : Fin width => i).reverse := by
  funext x
  rw [controlledXorIntoGates, controlledXorIntoIndicesStep,
    GateSpec.stepList_eq_foldl]
  let gateOfIndex : Fin width -> GateSpec encoding := fun i =>
    GateSpec.toffoli control (source.bit i) (target.bit i)
      (hcontrolSource i) (hcontrolTarget i) (hsourceTarget i)
  change
    List.foldl (fun y gate => gate.step y) x
        (List.ofFn gateOfIndex).reverse =
      List.foldl (fun y i => (gateOfIndex i).step y) x
        (List.ofFn fun i : Fin width => i).reverse
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun i : Fin width => i).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun i : Fin width => i) gateOfIndex)]
  rw [← List.map_reverse]
  generalize (List.ofFn fun i : Fin width => i).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons i rest ih =>
      simp [ih]

/-- The reversed controlled word-xor gate list preserves any observed readout
whose wire is distinct from every target bit. -/
lemma controlledXorIntoGates_reverse_get_observed_of_target_ne
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (observed : EncodedBit encoding)
    (hne : ∀ i, (target.bit i).wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (GateSpec.stepList
          (controlledXorIntoGates control source target
            hcontrolSource hcontrolTarget hsourceTarget).reverse x) =
      observed.get x := by
  rw [controlledXorIntoGates_reverse_stepList_eq_indicesStep]
  exact
    controlledXorIntoIndicesStep_get_observed_of_target_ne
      control source target (List.ofFn fun i : Fin width => i).reverse
      observed
      (fun i _ => hne i)
      x

/-- The reversed controlled word-xor gate list toggles each target bit by the
corresponding controlled source bit. -/
lemma controlledXorIntoGates_reverse_get_target
    (control : EncodedBit encoding) (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (i : Fin width)
    (htargetTarget :
      ∀ j, j ≠ i -> (target.bit j).wire ≠ (target.bit i).wire)
    (htargetControl : ∀ j, (target.bit j).wire ≠ control.wire)
    (htargetSource : ∀ j, (target.bit j).wire ≠ (source.bit i).wire)
    (x : Data) :
    (target.bit i).get
        (GateSpec.stepList
          (controlledXorIntoGates control source target
            hcontrolSource hcontrolTarget hsourceTarget).reverse x) =
      ((target.bit i).get x ^^
        (control.get x && (source.bit i).get x)) := by
  rw [controlledXorIntoGates_reverse_stepList_eq_indicesStep]
  have hnodup :
      ((List.ofFn fun j : Fin width => j).reverse).Nodup := by
    exact List.nodup_reverse.mpr
      (List.nodup_ofFn_ofInjective (fun _ _ h => h))
  have hmem : i ∈ (List.ofFn fun j : Fin width => j).reverse := by
    simp
  simpa [hmem] using
    controlledXorIntoIndicesStep_get_target control source target
      (List.ofFn fun j : Fin width => j).reverse hnodup i
      htargetTarget htargetControl htargetSource x

/-- The controlled bitwise xor program realizes its folded semantic action. -/
lemma controlledXorInto_realizes (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
      (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (controlledXorIntoProgram physical oracles control source target
        hcontrolSource hcontrolTarget hsourceTarget) environment
      (controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget) :=
  GateSpec.realizesList (environment := environment) physical oracles
    (controlledXorIntoGates control source target
      hcontrolSource hcontrolTarget hsourceTarget)

/-- Direct realization proof for controlled bitwise xor into another word. -/
lemma controlledXorIntoWitness (control : EncodedBit encoding)
    (source target : Word encoding width)
    (hcontrolSource : ∀ i, control.wire ≠ (source.bit i).wire)
    (hcontrolTarget : ∀ i, control.wire ≠ (target.bit i).wire)
    (hsourceTarget : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
      (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (controlledXorIntoProgram physical oracles control source target
        hcontrolSource hcontrolTarget hsourceTarget) environment
      (controlledXorIntoStep control source target
        hcontrolSource hcontrolTarget hsourceTarget) :=
  controlledXorInto_realizes (environment := environment) physical oracles control source target
    hcontrolSource hcontrolTarget hsourceTarget

end Word

end EncodedBit

end

end QuantumAlg

end

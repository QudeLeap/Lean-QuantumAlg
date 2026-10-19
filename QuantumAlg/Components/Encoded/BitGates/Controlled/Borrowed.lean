/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-!
# Coherent control using existing gate-local borrowed wires

An elementary source instruction touches at most three wires. On a carrier
of at least five wires, one wire is outside that instruction and its added
control. The least such wire supplies arbitrary dirty work and is restored
inside the emitted instruction block. Different source instructions may
therefore borrow different existing wires, without allocating an ancilla or
requiring one wire to be unused by the complete source program.
-/

namespace QuantumAlg.EncodedBit.GateSpec

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private def usedWires : GateSpec encoding → Finset (Fin encoding.width)
  | .x target => {target.wire}
  | .cnot source target _ => {source.wire, target.wire}
  | .toffoli first second target _ _ _ => {first.wire, second.wire, target.wire}

private lemma usedWires_card (gate : GateSpec encoding) : (usedWires gate).card ≤ 3 := by
  cases gate with
  | x => simp [usedWires]
  | cnot => exact Finset.card_le_two.trans (by decide)
  | toffoli => exact Finset.card_le_three

private def availableWires (control : EncodedBit encoding) (gate : GateSpec encoding) :
    Finset (Fin encoding.width) := Finset.univ \ insert control.wire (usedWires gate)

private lemma availableWires_nonempty (capacity : 5 ≤ encoding.width)
    (control : EncodedBit encoding) (gate : GateSpec encoding) :
    (availableWires control gate).Nonempty := by
  apply Finset.sdiff_nonempty_of_card_lt_card
  have occupied := Finset.card_insert_le control.wire (usedWires gate)
  have source := usedWires_card gate
  rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- Least existing wire outside the added control and all source-gate operands. -/
def borrowedWire (capacity : 5 ≤ encoding.width)
    (control : EncodedBit encoding) (gate : GateSpec encoding) : Fin encoding.width :=
  (availableWires control gate).min' (availableWires_nonempty capacity control gate)

private lemma borrowedWire_available (capacity : 5 ≤ encoding.width)
    (control : EncodedBit encoding) (gate : GateSpec encoding) :
    borrowedWire capacity control gate ≠ control.wire ∧
      borrowedWire capacity control gate ∉ usedWires gate := by
  have present := Finset.min'_mem (availableWires control gate)
    (availableWires_nonempty capacity control gate)
  simpa only [borrowedWire, availableWires, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, not_or] using present

/-- Build one actual dirty-control plan from a complete family of physical bit lenses. -/
def internalControlPlan (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gate : GateSpec encoding) (separated : bitDisjoint control gate) :
    DirtyControlPlan control where
  gate := gate
  work := bitAt (borrowedWire capacity control gate)
  controlDisjoint := separated
  workDisjoint := by
    have available := (borrowedWire_available capacity control gate).2
    cases gate <;> simpa [usedWires, bitDisjoint, bitAt_wire, ne_comm] using available
  controlWork := by
    rw [bitAt_wire]
    exact (borrowedWire_available capacity control gate).1.symm

/-- Choose and restore borrowed work separately for each source instruction. -/
def internalControlPlans (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding) :
    (gates : List (GateSpec encoding)) →
    (∀ gate, gate ∈ gates → bitDisjoint control gate) → List (DirtyControlPlan control)
  | [], _ => []
  | gate :: rest, separated =>
      internalControlPlan bitAt bitAt_wire capacity control gate (separated gate (by simp)) ::
        internalControlPlans bitAt bitAt_wire capacity control rest
          (fun next present => separated next (by simp [present]))

/-- Work selection keeps every original instruction in its original position. -/
lemma internalControlPlans_source (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    plannedSourceGates control
        (internalControlPlans bitAt bitAt_wire capacity control gates separated) = gates := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change gate :: plannedSourceGates control
        (internalControlPlans bitAt bitAt_wire capacity control rest _) = gate :: rest
      rw [ih]

/-- Lower the whole list into native gates on the same complete physical carrier. -/
def controlWithin (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) : List (GateSpec encoding) :=
  listWithDirtyControlBy control
    (internalControlPlans bitAt bitAt_wire capacity control gates separated)

/-- Exact all-input action restores every borrowed wire inside its instruction block. -/
lemma controlWithin_step (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) (state : Data) :
    stepList (controlWithin bitAt bitAt_wire capacity control gates separated) state =
      if control.get state then stepList gates state else state := by
  rw [controlWithin, listWithDirtyControlBy_step, internalControlPlans_source]

/-- The emitted CNOT/Toffoli program realizes coherent selection with exact phase. -/
lemma controlWithin_realizes (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles (controlWithin bitAt bitAt_wire capacity control gates separated))
      environment
      (fun state => if control.get state then stepList gates state else state) :=
  realizesList_congrStep layout oracles _
    (controlWithin_step bitAt bitAt_wire capacity control gates separated) environment

/-- Exact emitted length counts one gate per source X/CNOT and four per source Toffoli. -/
lemma controlWithin_length (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    (controlWithin bitAt bitAt_wire capacity control gates separated).length =
      (gates.map dirtyControlCount).sum := by
  rw [controlWithin, listWithDirtyControlBy_length, internalControlPlans_source]

/-- Exact default native coordinates include the full four-Toffoli expansion. -/
lemma controlWithin_native_counts (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    ((controlWithin bitAt bitAt_wire capacity control gates separated).map xMultiplicity).sum = 0 ∧
      ((controlWithin bitAt bitAt_wire capacity control gates separated).map
        cnotMultiplicity).sum = (gates.map xMultiplicity).sum ∧
      ((controlWithin bitAt bitAt_wire capacity control gates separated).map
        toffoliMultiplicity).sum =
        (gates.map cnotMultiplicity).sum + 4 * (gates.map toffoliMultiplicity).sum := by
  simp only [controlWithin, listWithDirtyControlBy_xMultiplicity_sum,
    listWithDirtyControlBy_cnotMultiplicity_sum, listWithDirtyControlBy_toffoliMultiplicity_sum,
    internalControlPlans_source, and_self]

/-- A parameter-only envelope bounds the real expansion, including all borrowed-bit restoration. -/
lemma controlWithin_length_bound (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    (controlWithin bitAt bitAt_wire capacity control gates separated).length ≤
      4 * gates.length := by
  rw [controlWithin_length]
  induction gates with
  | nil => simp
  | cons gate rest ih =>
      have tail := ih (fun next present => separated next (by simp [present]))
      cases gate <;> simp only [List.map_cons, List.sum_cons, List.length_cons, dirtyControlCount]
        <;> omega

/-- The actual sequential native program obeys the same gate-count and depth envelope. -/
lemma controlWithin_resources (bitAt : Fin encoding.width → EncodedBit encoding)
    (bitAt_wire : ∀ position, (bitAt position).wire = position)
    (capacity : 5 ≤ encoding.width) (control : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel)
    (gates : List (GateSpec encoding))
    (separated : ∀ gate, gate ∈ gates → bitDisjoint control gate) :
    (programList layout oracles
        (controlWithin bitAt bitAt_wire capacity control gates separated)).eventCost.card ≤
        4 * gates.length ∧
      (programList layout oracles
        (controlWithin bitAt bitAt_wire capacity control gates separated)).evaluatedEventDepth
        (fun _ => 1) ≤ 4 * gates.length := by
  rw [programList_eventCost_card, programList_evaluatedEventDepth_unit]
  exact ⟨controlWithin_length_bound bitAt bitAt_wire capacity control gates separated,
    controlWithin_length_bound bitAt bitAt_wire capacity control gates separated⟩

end

end QuantumAlg.EncodedBit.GateSpec

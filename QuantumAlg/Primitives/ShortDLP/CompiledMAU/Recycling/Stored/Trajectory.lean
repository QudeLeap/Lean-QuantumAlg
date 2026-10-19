/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Outputs
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import Mathlib.Data.List.OfFn

/-!
# Actual stored branches as chronological common-reference trajectories

The segment below merely selects coordinates
of an existing Fourier bit tuple. The actual suffix writes are proved equal to
the existing Store.writePrefix. Distinct physical keys then identify every
Store-selected phase with the chronological record, and hence the native clean
instrument's source product and complete unnormalized posterior with Trajectory.
No classical packing is executed or replaced by this mathematical comparison.
No external cleanliness, phase identity or instrument certificate is assumed.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredTrajectory

noncomputable section

open Execution

variable {environment : model.Environment}
open QuantumFourierTransform.Semiclassical (Bits tupleCoordinates)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- An internal segment of the existing outcome tuple, without a new runtime representation. -/
def recordTail {bits : Nat} (record : Fin bits → Fin 2) :
    (remaining position : Nat) → position + remaining ≤ bits → Bits remaining
  | 0, _, _ => ()
  | remaining + 1, position, bounded =>
      (record ⟨position, by omega⟩,
        recordTail record remaining (position + 1) (by omega))

/-- Every segment coordinate is the original chronological coordinate at its true offset. -/
lemma recordTail_coordinates {bits : Nat} (record : Fin bits → Fin 2)
    (remaining position : Nat) (bounded : position + remaining ≤ bits)
    (index : Fin remaining) :
    tupleCoordinates remaining (recordTail record remaining position bounded) index =
      record ⟨position + index.val, by have bound := index.isLt; omega⟩ := by
  induction remaining generalizing position with
  | zero => exact Fin.elim0 index
  | succ remaining induction =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · simp only [recordTail, QuantumFourierTransform.Semiclassical.tupleCoordinates_head]
        congr 1
      · rw [recordTail, QuantumFourierTransform.Semiclassical.tupleCoordinates_tail, induction]
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega

/-- Selecting every chronological coordinate reconstructs the identical existing tuple. -/
lemma recordTail_all {bits : Nat} (outcome : Bits bits) :
    recordTail (tupleCoordinates bits outcome) bits 0 (by omega) = outcome := by
  apply QuantumFourierTransform.Semiclassical.tupleCoordinates_injective bits
  funext index
  rw [recordTail_coordinates]
  congr 1
  exact Fin.ext (by simp)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The next actual binary write extends precisely the existing chronological prefix. -/
private lemma prefix_next {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (position : Fin bits) :
    (StoredOutputs.outcomeStore base noQuantum m ell width outputs record original position.val
      (Nat.le_of_lt position.isLt)).write (outputs position) (.finite (record position)) =
      StoredOutputs.outcomeStore base noQuantum m ell width outputs record original
        (position.val + 1) (Nat.succ_le_of_lt position.isLt) := by
  rfl

/-- Real suffix writes extend the same real prefix, including all unrelated original cells. -/
lemma suffixStore_record (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (remaining position : Nat) (bounded : position + remaining ≤ bits) :
    NativeInstrument.suffixStore base noQuantum m ell width inverse outputs remaining position
        bounded
        (StoredOutputs.outcomeStore base noQuantum m ell width outputs record original position
          (by omega))
        (recordTail record remaining position bounded) =
      StoredOutputs.outcomeStore base noQuantum m ell width outputs record original
        (position + remaining) bounded := by
  induction remaining generalizing position with
  | zero => rfl
  | succ remaining induction =>
      rw [recordTail, NativeInstrument.suffixStore,
        prefix_next base noQuantum m ell width outputs record original ⟨position, by omega⟩]
      have next := induction (position + 1) (by omega)
      have offset : (position + 1) + remaining = position + (remaining + 1) := by omega
      simpa only [offset] using next

/-- The full actual output Store is the same retained n-cell prefix, not an integer packing. -/
lemma suffixStore_all (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (original : Store (Context base noQuantum m ell width)) (outcome : Bits bits) :
    NativeInstrument.suffixStore base noQuantum m ell width inverse outputs bits 0 (by omega)
        original outcome =
      StoredOutputs.outcomeStore base noQuantum m ell width outputs
        (tupleCoordinates bits outcome) original bits le_rfl := by
  have whole := suffixStore_record base noQuantum m ell width inverse outputs
    (tupleCoordinates bits outcome) original bits 0 (by omega)
  simpa only [recordTail_all, Nat.zero_add, StoredOutputs.outcomeStore, Store.writePrefix]
    using whole

/-- All physical output cells read the corresponding branch coordinate after actual execution. -/
lemma suffixStore_all_read (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (original : Store (Context base noQuantum m ell width)) (outcome : Bits bits)
    (index : Fin bits) :
    (NativeInstrument.suffixStore base noQuantum m ell width inverse outputs bits 0 (by omega)
      original outcome).read (.storage (outputs index).toCStorageRef) =
        .finite (tupleCoordinates bits outcome index) := by
  rw [suffixStore_all]
  exact StoredOutputs.outcomeStore_all_read base noQuantum m ell width outputs separate _ _ index

lemma firstCell_key_injective :
    Function.Injective (fun index => (firstCell base noQuantum m ell width index).key) := by
  intro first second same
  have indices := cells_distinct base noQuantum m ell width same
  apply Fin.ext
  exact congrArg (fun index : Fin (resultBits m ell) => index.val) indices

lemma secondCell_key_injective :
    Function.Injective (fun index => (secondCell base noQuantum m ell width index).key) := by
  intro first second same
  have indices := cells_distinct base noQuantum m ell width same
  have values := congrArg Fin.val indices
  change ell + m + first.val = ell + m + second.val at values
  apply Fin.ext
  omega

/-- Output writes preserve every differently keyed original cell, including the other stream. -/
private lemma prefix_preserves {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (output : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (different : ∀ index, (outputs index).key ≠ output.key)
    (count : Nat) (bounded : count ≤ bits) :
    (StoredOutputs.outcomeStore base noQuantum m ell width outputs record original
      count bounded).read (.storage output.toCStorageRef) =
        original.read (.storage output.toCStorageRef) := by
  change (Store.writePrefix outputs (fun index => .finite (record index)) original
    count bounded).read (.storage output.toCStorageRef) = _
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [Store.writePrefix, Store.read_write_other _ _ _ _
        (different ⟨count, Nat.lt_of_succ_le bounded⟩)]
      exact induction (Nat.le_of_succ_le bounded)

/-- The second exponent's real writes cannot erase any first-exponent output bit. -/
lemma memberStore_first_read (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) (index : Fin (ell + m)) :
    (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (.storage (firstCell base noQuantum m ell width index).toCStorageRef) =
      .finite (tupleCoordinates (ell + m) outcome.1 index) := by
  rw [MemberInstrument.memberStore, suffixStore_all]
  rw [prefix_preserves base noQuantum m ell width _ _ _ _
    (fun second => (first_second_distinct base noQuantum m ell width index second).symm)]
  exact suffixStore_all_read base noQuantum m ell width true
    (firstCell base noQuantum m ell width) (firstCell_key_injective base noQuantum m ell width)
    original outcome.1 index

lemma memberStore_second_read (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) (index : Fin ell) :
    (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (.storage (secondCell base noQuantum m ell width index).toCStorageRef) =
      .finite (tupleCoordinates ell outcome.2 index) := by
  unfold MemberInstrument.memberStore
  exact suffixStore_all_read base noQuantum m ell width true
    (secondCell base noQuantum m ell width) (secondCell_key_injective base noQuantum m ell width)
    _ outcome.2 index

/-- Every canonical physical cell survives both streams in its original chronological slot. -/
lemma memberStore_all_read (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) (index : Fin (resultBits m ell)) :
    (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (.storage (cells base noQuantum m ell width index).toCStorageRef) =
      .finite (Fin.addCases (tupleCoordinates (ell + m) outcome.1)
        (tupleCoordinates ell outcome.2) index) := by
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · change (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (.storage (firstCell base noQuantum m ell width first).toCStorageRef) =
      .finite (Fin.addCases (tupleCoordinates (ell + m) outcome.1)
        (tupleCoordinates ell outcome.2) (Fin.castAdd ell first))
    have coordinate : Fin.addCases (motive := fun _ : Fin ((ell + m) + ell) => Fin 2)
        (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2)
        (Fin.castAdd ell first) =
          tupleCoordinates (ell + m) outcome.1 first :=
      Fin.addCases_left first
    refine (memberStore_first_read base noQuantum m ell width original outcome first).trans ?_
    exact congrArg (fun bit : Fin 2 =>
      (CShape.Value.finite bit : CShape.Value (.finite 2))) coordinate.symm
  · change (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (.storage (secondCell base noQuantum m ell width second).toCStorageRef) =
      .finite (Fin.addCases (tupleCoordinates (ell + m) outcome.1)
        (tupleCoordinates ell outcome.2) (Fin.natAdd (ell + m) second))
    have coordinate : Fin.addCases (motive := fun _ : Fin ((ell + m) + ell) => Fin 2)
        (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2)
        (Fin.natAdd (ell + m) second) =
          tupleCoordinates ell outcome.2 second :=
      Fin.addCases_right second
    refine (memberStore_second_read base noQuantum m ell width original outcome second).trans ?_
    exact congrArg (fun bit : Fin 2 =>
      (CShape.Value.finite bit : CShape.Value (.finite 2))) coordinate.symm

/-- The real input of the later charged pack reads the two independently reversed streams. -/
lemma memberStore_frequencyInput (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) :
    (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (frequencyInput base noQuantum m ell width) =
      .fixedVector (fun index => .finite (Fin.addCases
        (fun first => tupleCoordinates (ell + m) outcome.1 first.rev)
        (fun second => tupleCoordinates ell outcome.2 second.rev) index)) := by
  change CShape.Value.fixedVector _ = CShape.Value.fixedVector _
  congr 1
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · change (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (Fin.addCases
          (fun position =>
            .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
          (fun position =>
            .storage (secondCell base noQuantum m ell width position.rev).toCStorageRef)
          (Fin.castAdd ell first)) =
      .finite (Fin.addCases
        (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
        (fun position => tupleCoordinates ell outcome.2 position.rev) (Fin.castAdd ell first))
    rw [Fin.addCases_left]
    have coordinate :
        Fin.addCases (motive := fun _ : Fin ((ell + m) + ell) => Fin 2)
          (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
          (fun position => tupleCoordinates ell outcome.2 position.rev)
          (Fin.castAdd ell first) =
            tupleCoordinates (ell + m) outcome.1 first.rev :=
      Fin.addCases_left first
    refine (memberStore_first_read base noQuantum m ell width original outcome first.rev).trans ?_
    exact congrArg (fun bit : Fin 2 =>
      (CShape.Value.finite bit : CShape.Value (.finite 2))) coordinate.symm
  · change (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
        (Fin.addCases
          (fun position =>
            .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
          (fun position =>
            .storage (secondCell base noQuantum m ell width position.rev).toCStorageRef)
          (Fin.natAdd (ell + m) second)) =
      .finite (Fin.addCases
        (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
        (fun position => tupleCoordinates ell outcome.2 position.rev) (Fin.natAdd (ell + m) second))
    rw [Fin.addCases_right]
    have coordinate :
        Fin.addCases (motive := fun _ : Fin ((ell + m) + ell) => Fin 2)
          (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
          (fun position => tupleCoordinates ell outcome.2 position.rev)
          (Fin.natAdd (ell + m) second) =
            tupleCoordinates ell outcome.2 second.rev :=
      Fin.addCases_right second
    refine (memberStore_second_read base noQuantum m ell width original outcome second.rev).trans ?_
    exact congrArg (fun bit : Fin 2 =>
      (CShape.Value.finite bit : CShape.Value (.finite 2))) coordinate.symm

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- Exact source choice, keeping the power's original MSB address and the output's LSB order. -/
def recordChoice (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (record : Fin bits → Fin 2) (position : Fin bits) : Trajectory.Choice modulus :=
  ⟨unit ^ (2 ^ position.rev.val),
    Trajectory.feedbackAngle inverse record position position.val le_rfl, record position⟩

/-- A suffix of the original choices never renumbers its arithmetic powers or feedback bits. -/
def choiceTail (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (record : Fin bits → Fin 2) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) : List (Trajectory.Choice modulus) :=
  List.ofFn fun index : Fin remaining => recordChoice width modulus inverse unit record
    ⟨position + index.val, by have bound := index.isLt; omega⟩

omit [NeZero modulus.val] in
private lemma choiceTail_succ (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (record : Fin bits → Fin 2) (remaining position : Nat)
    (bounded : position + (remaining + 1) ≤ bits) :
    choiceTail width modulus inverse unit record (remaining + 1) position bounded =
      recordChoice width modulus inverse unit record ⟨position, by omega⟩ ::
        choiceTail width modulus inverse unit record remaining (position + 1) (by omega) := by
  rw [choiceTail, List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext index
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

omit [NeZero modulus.val] in
lemma choiceTail_all (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (record : Fin bits → Fin 2) :
    choiceTail width modulus inverse unit record bits 0 (by omega) =
      Trajectory.exponentChoices modulus inverse unit record := by
  unfold choiceTail Trajectory.exponentChoices
  apply congrArg List.ofFn
  funext index
  simp only [recordChoice, Nat.zero_add]

/-- Every actual feedback scalar is the derived record phase before that exact physical write. -/
private lemma sourceBranch_prefix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (unit : (ZMod modulus.val)ˣ) (record : Fin bits → Fin 2)
    (original : Store (Context base noQuantum m ell width)) (position : Fin bits)
    (Reference : Register) :
    CleanStage.sourceBranch base noQuantum m ell width modulus inverse outputs unit position
        Reference
        (StoredOutputs.outcomeStore base noQuantum m ell width outputs record original
          position.val (Nat.le_of_lt position.isLt)) (record position) =
      Trajectory.sourceFactor modulus Reference
        (recordChoice width modulus inverse unit record position) := by
  rw [CleanStage.sourceBranch,
    StoredOutputs.scalar_after_prefix base noQuantum m ell width inverse outputs separate]
  rfl

/-- Actual Store-selected half sums are exactly the chronological common-reference product. -/
lemma sourceSuffix_record (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (record : Fin bits → Fin 2)
    (original : Store (Context base noQuantum m ell width)) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    CleanInstrument.sourceSuffix base noQuantum m ell width modulus inverse outputs unit Reference
        remaining position bounded
        (StoredOutputs.outcomeStore base noQuantum m ell width outputs record original position
          (by omega))
        (recordTail record remaining position bounded) =
      Trajectory.sourceProduct modulus Reference
        (choiceTail width modulus inverse unit record remaining position bounded) := by
  induction remaining generalizing position with
  | zero => simp only [CleanInstrument.sourceSuffix, choiceTail, List.ofFn_zero,
      Trajectory.sourceProduct]
  | succ remaining induction =>
      rw [recordTail, CleanInstrument.sourceSuffix,
        prefix_next base noQuantum m ell width outputs record original ⟨position, by omega⟩,
        induction, choiceTail_succ, Trajectory.sourceProduct,
        sourceBranch_prefix base noQuantum m ell width modulus inverse outputs separate]

/-- The full product is independent of unrelated old cell values; no Store premise is added. -/
lemma sourceSuffix_all (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width)) (outcome : Bits bits) :
    CleanInstrument.sourceSuffix base noQuantum m ell width modulus inverse outputs unit Reference
        bits 0 (by omega) original outcome =
      Trajectory.sourceProduct modulus Reference
        (Trajectory.exponentChoices modulus inverse unit (tupleCoordinates bits outcome)) := by
  have whole := sourceSuffix_record base noQuantum m ell width modulus inverse outputs separate
    unit Reference (tupleCoordinates bits outcome) original bits 0 (by omega)
  simpa only [recordTail_all, choiceTail_all, StoredOutputs.outcomeStore, Store.writePrefix]
    using whole

/-- The entire actual posterior equals sigma_y, with every mixed/reference coherence retained. -/
lemma sigmaSuffix_all (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width)) (outcome : Bits bits)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    CleanInstrument.sigmaSuffix base noQuantum m ell width modulus inverse outputs unit Reference
        bits 0 (by omega) original outcome density =
      Trajectory.σ modulus Reference
        (Trajectory.exponentChoices modulus inverse unit (tupleCoordinates bits outcome)) density :=
    by
  rw [CleanInstrument.sigmaSuffix_eq_product, sourceSuffix_all base noQuantum m ell width modulus
    inverse outputs separate, Trajectory.sigma_eq_product]

/-- Both actual streams pass one full sigma_y forward without a new accumulator or reference. -/
lemma memberSigma_trajectory (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    MemberInstrument.memberSigma base noQuantum m ell width modulus generator target Reference
        original outcome density =
      Trajectory.σ modulus Reference
        (Trajectory.memberChoices modulus true m ell generator target
          (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2)) density := by
  rw [MemberInstrument.memberSigma,
    sigmaSuffix_all base noQuantum m ell width modulus true (secondCell base noQuantum m ell width)
      (secondCell_key_injective base noQuantum m ell width),
    sigmaSuffix_all base noQuantum m ell width modulus true (firstCell base noQuantum m ell width)
      (firstCell_key_injective base noQuantum m ell width)]
  exact (Trajectory.sigma_append modulus Reference _ _ density).symm

variable (positive : 0 < modulus.val)

/-- Full actual stored/reference instrument with internally derived chronological sigma_y. -/
lemma member_trajectory_store_matrix (generator target : (ZMod modulus.val)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference))
    (stored : Store (Context base noQuantum m ell width)) :
    ((member base noQuantum m ell width modulus.val generator target).execute environment Reference
      (CleanStage.encodeState base noQuantum m ell width modulus positive state)
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
            let embedding := BasisEmbedding.matrix
              (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
            embedding *
              Trajectory.σ modulus Reference
                (Trajectory.memberChoices modulus true m ell generator target
                  (tupleCoordinates (ell + m) outcome.1) (tupleCoordinates ell outcome.2))
                ((state.mapClassical (fun entry => entry.1)).block original).matrix *
              embedding.conjTranspose
          else 0 := by
  rw [MemberInstrument.member_clean_store_matrix]
  simp_rw [memberSigma_trajectory base noQuantum m ell width modulus]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredTrajectory

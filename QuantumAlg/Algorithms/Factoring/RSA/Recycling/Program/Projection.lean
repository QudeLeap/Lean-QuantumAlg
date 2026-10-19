/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Native.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Outputs
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Trajectory
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Reference
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Frequency
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Seeded.Born
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Store.WritePrefix

/-!
# Store projections of the actual recycled RSA member

The real measured member writes only its allocated binary cells, and the
existing paid packing operation writes only its designated packed cell.
Physical key separation therefore preserves every other preallocated frame
cell. The designated result is the original source terminal outcome at the
two independently decoded frequencies. These laws allow arbitrary incoming
Store values and all natural widths, including empty exponent streams.
They assert no independent distribution and introduce no executor.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution
open EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling
open QuantumFourierTransform.Semiclassical (Bits frequencyBits)

local instance {A : Type} : DecidableEq A := Classical.decEq A

private lemma prefix_read_other {ctx : RuntimeCtx .quantum} {bits : Nat}
    (outputs : Fin bits → CWriteRef ctx (.finite 2)) (record : Fin bits → Fin 2)
    (original : Store ctx) {shape : CShape} (observed : CStorageRef ctx shape)
    (different : ∀ index, (outputs index).key ≠ observed.key)
    (count : Nat) (bounded : count ≤ bits) :
    (Store.writePrefix outputs (fun index => .finite (record index))
      original count bounded).read (.storage observed) = original.read (.storage observed) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Store.writePrefix, Store.read_write_other _ _ _ _
        (different ⟨count, Nat.lt_of_succ_le bounded⟩)]
      exact ih (Nat.le_of_succ_le bounded)

private lemma lifted_cell_separate {ctx : RuntimeCtx .quantum} {shape : CShape}
    (observed : CWriteRef ctx shape) (count : Nat) (index : Fin count) :
    (MeasurementCells.reference ctx 2 count index).key ≠
      (MeasurementCells.liftWrite 2 observed count).key := by
  have separated := MeasurementCells.reference_not_mem_liftInput 2
    (.storage observed.toCStorageRef) count index
  rw [MeasurementCells.liftInput_storage] at separated
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separated

private lemma suffix_read_other (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (m ell width : Nat) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (context base noQuantum m ell width) (.finite 2))
    (original : Store (context base noQuantum m ell width)) (outcome : Bits bits)
    {shape : CShape} (observed : CStorageRef (context base noQuantum m ell width) shape)
    (different : ∀ index, (outputs index).key ≠ observed.key) :
    (NativeInstrument.suffixStore base noQuantum m ell width inverse outputs bits 0 (by omega)
      original outcome).read (.storage observed) = original.read (.storage observed) := by
  rw [StoredTrajectory.suffixStore_all]
  exact prefix_read_other outputs _ original observed different bits le_rfl

private lemma memberStore_read_other (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (m ell width : Nat)
    (original : Store (context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) {shape : CShape}
    (observed : CStorageRef (context base noQuantum m ell width) shape)
    (different : ∀ index, (cells base noQuantum m ell width index).key ≠ observed.key) :
    (MemberInstrument.memberStore base noQuantum m ell width original outcome).read
      (.storage observed) = original.read (.storage observed) := by
  have firstSeparate (index : Fin (ell + m)) :
      (firstCell base noQuantum m ell width index).key ≠ observed.key := by
    unfold firstCell
    exact different _
  have secondSeparate (index : Fin ell) :
      (secondCell base noQuantum m ell width index).key ≠ observed.key := by
    unfold secondCell
    exact different _
  unfold MemberInstrument.memberStore
  exact (suffix_read_other base noQuantum m ell width true
    (secondCell base noQuantum m ell width) _ outcome.2 observed secondSeparate).trans
      (suffix_read_other base noQuantum m ell width true
        (firstCell base noQuantum m ell width) original outcome.1 observed firstSeparate)

private lemma packedStore_read_other (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (m ell width : Nat)
    (result : CWriteRef (context base noQuantum m ell width) (.bits (resultBits m ell)))
    (original : Store (context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) {shape : CShape}
    (observed : CStorageRef (context base noQuantum m ell width) shape)
    (cellsSeparate : ∀ index, (cells base noQuantum m ell width index).key ≠ observed.key)
    (resultSeparate : result.key ≠ observed.key) :
    (PackedReference.packedStore base noQuantum m ell width result original outcome).read
      (.storage observed) = original.read (.storage observed) := by
  unfold PackedReference.packedStore
  exact (Packing.recyclingPacking_preserves_cell base noQuantum m ell width result
    (MemberInstrument.memberStore base noQuantum m ell width original outcome)
    observed resultSeparate).trans
      (memberStore_read_other base noQuantum m ell width original outcome observed cellsSeparate)

private lemma packedStore_output (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (m ell width : Nat)
    (result : CWriteRef (context base noQuantum m ell width) (.bits (resultBits m ell)))
    (original : Store (context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) :
    (PackedReference.packedStore base noQuantum m ell width result original outcome).read
        (.storage result.toCStorageRef) =
      .bits (SeededBorn.sourceOutcome m ell width (PackedReference.frequencies m ell outcome).1
        (PackedReference.frequencies m ell outcome).2) := by
  unfold PackedReference.packedStore
  have decoded :
      (frequencyBits (ell + m) (PackedReference.frequencies m ell outcome).1,
        frequencyBits ell (PackedReference.frequencies m ell outcome).2) = outcome :=
    Prod.ext (QuantumFourierTransform.Semiclassical.Partner.qftPartner_frequencyBits_decode
      (ell + m) outcome.1)
      (QuantumFourierTransform.Semiclassical.Partner.qftPartner_frequencyBits_decode ell outcome.2)
  have packed := PackedFrequency.member_packed_output base noQuantum m ell width result original
    (PackedReference.frequencies m ell outcome).1 (PackedReference.frequencies m ell outcome).2
  rw [decoded] at packed
  exact packed.trans (congrArg CShape.Value.bits
    (PackedFrequency.canonicalReadout_eq_source m ell width
      (PackedReference.frequencies m ell outcome).1 (PackedReference.frequencies m ell outcome).2))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual member and paid pack preserve any other cell of the preallocated frame. -/
lemma rsaRecyclingParent_packedStore_read_frame (count : Nat) (batch : Fin count)
    (index : Fin 16) {shape : CShape}
    (observed : CWriteRef (ClassicalFrame.context base N count) shape)
    (different : (ClassicalFrame.packedRef base N count batch index).key ≠ observed.key)
    (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count observed).toCStorageRef) =
      original.read
        (.storage (ClassicalFrame.bankWrite noQuantum N count observed).toCStorageRef) := by
  apply packedStore_read_other
  · intro cell
    unfold cells ClassicalFrame.bankWrite
    exact lifted_cell_separate _ _ cell
  · intro same
    exact different
      ((ClassicalFrame.rsaRecyclingFrame_bankWrite_key noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)).symm.trans
          (same.trans (ClassicalFrame.rsaRecyclingFrame_bankWrite_key
            noQuantum N count observed)))

/-- Every complete sampled parameter survives every real member, including other batches. -/
lemma rsaRecyclingParent_packedStore_parameter (count : Nat) (batch previous : Fin count)
    (index : Fin 16) (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.parameterRef base N count previous)).toCStorageRef) =
      original.read (.storage (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.parameterRef base N count previous)).toCStorageRef) :=
  rsaRecyclingParent_packedStore_read_frame base noQuantum N count batch index
    (ClassicalFrame.parameterRef base N count previous)
    (ClassicalFrame.rsaRecyclingFrame_packed_parameter_separate base N count batch previous index)
    original outcome

/-- Each batch's retained random source remains unchanged by all actual measured members. -/
lemma rsaRecyclingParent_packedStore_sample (count : Nat) (batch previous : Fin count)
    (index : Fin 16) (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.sampleRef base N count previous)).toCStorageRef) =
      original.read (.storage (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.sampleRef base N count previous)).toCStorageRef) :=
  rsaRecyclingParent_packedStore_read_frame base noQuantum N count batch index
    (ClassicalFrame.sampleRef base N count previous)
    (ClassicalFrame.rsaRecyclingFrame_packed_sample_separate base N count batch previous index)
    original outcome

/-- Member execution cannot overwrite any already recovered or future optional-factor cell. -/
lemma rsaRecyclingParent_packedStore_factor (count : Nat) (batch previous : Fin count)
    (index : Fin 16) (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.factorRef base N count previous)).toCStorageRef) =
      original.read (.storage (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.factorRef base N count previous)).toCStorageRef) :=
  rsaRecyclingParent_packedStore_read_frame base noQuantum N count batch index
    (ClassicalFrame.factorRef base N count previous)
    (ClassicalFrame.rsaRecyclingFrame_packed_factor_separate base N count batch previous index)
    original outcome

/-- A real packed write preserves every distinct chronological packed-result destination. -/
lemma rsaRecyclingParent_packedStore_otherPacked (count : Nat) (batch previous : Fin count)
    (index other : Fin 16) (different : (batch, index) ≠ (previous, other))
    (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.packedRef base N count previous other)).toCStorageRef) =
      original.read (.storage (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count previous other)).toCStorageRef) :=
  rsaRecyclingParent_packedStore_read_frame base noQuantum N count batch index
    (ClassicalFrame.packedRef base N count previous other)
    (fun same => different (ClassicalFrame.rsaRecyclingFrame_packedRef_distinct base N count same))
    original outcome

/-- The actual paid destination is the source terminal at the independently reversed streams. -/
lemma rsaRecyclingParent_packedStore_output (count : Nat) (batch : Fin count)
    (index : Fin 16) (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    (PackedReference.packedStore (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index)) original outcome).read
        (.storage (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.packedRef base N count batch index)).toCStorageRef) =
      .bits (SeededBorn.sourceOutcome (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
        (PackedReference.frequencies (shortLogBits N) (tradeoffBits N) outcome).1
        (PackedReference.frequencies (shortLogBits N) (tradeoffBits N) outcome).2) :=
  packedStore_output (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.packedRef base N count batch index)) original outcome

end

end QuantumAlg.Factoring.RSA.Recycling.Program

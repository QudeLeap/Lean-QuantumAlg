/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Row
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Remaining
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Seed
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor.Action
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Ket

/-!
# Complete physical point coordinates under mathematical source feeding

The current source digit changes only its physical bank. The complete point
workspace and unused source coordinates are retained; no instruction is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

private lemma sourceFedRaw_remaining {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (branch : Sampling.SourceRegister.Index) (raw : Raw) :
    Sampling.sourceFedRaw parameters index
        (Sampling.remainingSource index.sourceStart branch) raw =
      Sampling.sourceFedRaw parameters index branch raw := by
  exact congrArg
    (fun current : (Qubits (index.lowerWidth + 1)).Index =>
      EncodedBit.WindowLookup.resultSetConstant
        (Sampling.digitWord index.stream index.lowerWidth index.lowerWidth_bound) current raw)
    (parameters.remainingSource_current index branch)

private lemma sourceFeed_original_column {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (Reference : Register) (raw : Raw) (branch : Sampling.SourceRegister.Index)
    (reference : Reference.Index)
    (zero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits (parameters.physicalLabel raw)).1 =
        Partner.zeroBits (index.lowerWidth + 1)) :
    selectedFeedBasis (parameters.ports index) (parameters.sourcePartition index) Reference
        (parameters.physicalLabel raw,
          Sampling.remainingSource index.sourceStart branch, reference) =
      (parameters.physicalLabel (Sampling.sourceFedRaw parameters index branch raw),
        Sampling.remainingSource index.sourceEnd branch, reference) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · exact (parameters.sourceFeed_physicalLabel index Reference raw
      (Sampling.remainingSource index.sourceStart branch) reference).trans
        (congrArg parameters.physicalLabel
          (sourceFedRaw_remaining parameters index branch raw))
  · exact parameters.sourceFeed_remaining index Reference (parameters.physicalLabel raw)
      branch reference zero

attribute [local irreducible] PrimeFieldShortWeierstrass.Arithmetic.P256.modulus
  sourceBlank Sampling.sourceFedRaw Inversion.Seed.blank

private lemma digitFlip_retains_core (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : Fin (width + 1)) (raw : Raw) :
    (((Enable.digitBit stream width bounded bit).flip raw).1.1,
        ((Enable.digitBit stream width bounded bit).flip raw).1.2.2.1) =
      (raw.1.1, raw.1.2.2.1) := by
  refine Fin.cases ?_ (fun index => ?_) bit
  · dsimp only [Enable.digitBit, Fin.cases_zero, streamBit]
    split <;> rfl
  · rfl

private lemma digitXor_retains_core (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (value : Fin (2 ^ (width + 1))) (raw : Raw) :
    ((EncodedBit.Word.xorConstantStep (Sampling.digitWord stream width bounded) value raw).1.1,
        (EncodedBit.Word.xorConstantStep (Sampling.digitWord stream width bounded)
          value raw).1.2.2.1) = (raw.1.1, raw.1.2.2.1) := by
  unfold EncodedBit.Word.xorConstantStep
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
    (project := fun state : Raw => (state.1.1, state.1.2.2.1))
  intro gate member
  rw [EncodedBit.Word.xorConstantGates] at member
  obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
  intro state
  exact digitFlip_retains_core stream width bounded bit.rev state

private lemma sourceFedRaw_retains_core {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index) (raw : Raw) :
    ((Sampling.sourceFedRaw parameters index source raw).1.1,
        (Sampling.sourceFedRaw parameters index source raw).1.2.2.1) =
      (raw.1.1, raw.1.2.2.1) := by
  unfold Sampling.sourceFedRaw EncodedBit.WindowLookup.resultSetConstant
  exact digitXor_retains_core index.stream index.lowerWidth index.lowerWidth_bound _ raw

private lemma transport_retains_core {width : Nat} (same : width = 256)
    (first last : MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.Data width)
    (core : first.1 = last.1) :
    (Inversion.Transport.state same first).1 = (Inversion.Transport.state same last).1 := by
  cases same
  simpa only [Inversion.Transport.state_refl] using core

private lemma residentBlank_flags (width : Nat) (input : BitVec (width + 3))
    (pool : MAU.Inversion.SharedEEA.Scanned.Pool width) (flags : Frame.Controls)
    (numerator : Fin (2 ^ width)) :
    (MAU.Inversion.SharedEEA.Scanned.ControlledResidentSeed.blank width input pool flags
      numerator).2 = flags := by
  unfold MAU.Inversion.SharedEEA.Scanned.ControlledResidentSeed.blank
  rw [MAU.Inversion.SharedEEA.Scanned.ControlledResidentFrame.reassemble_flags]

private lemma sourceBlank_core_flags
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (first last : Frame.Controls) (firstAddress lastAddress : Address) :
    (sourceBlank input numerator first firstAddress).1.1 =
      (sourceBlank input numerator last lastAddress).1.1 := by
  unfold sourceBlank Inversion.Seed.blank
  exact transport_retains_core Inversion.modulus_size _ _ rfl

private lemma sourceBlank_flags
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (sourceBlank input numerator flags address).1.2 = flags := by
  unfold sourceBlank Inversion.Seed.blank
  exact (Inversion.Transport.state_flags Inversion.modulus_size _).trans
    (residentBlank_flags _ _ _ _ _)

private lemma sourceBlank_address
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (sourceBlank input numerator flags address).2 = address := by
  unfold sourceBlank
  rfl

private lemma sourceFedRaw_blank {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (branch : Sampling.SourceRegister.Index)
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    let fed := Sampling.sourceFedRaw parameters index branch
      (sourceBlank input numerator flags address)
    fed = sourceBlank input numerator fed.1.2 fed.2 := by
  dsimp only
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact (congrArg Prod.fst (sourceFedRaw_retains_core parameters index branch
      (sourceBlank input numerator flags address))).trans
      (sourceBlank_core_flags input numerator flags _ address _)
  · exact (sourceBlank_flags input numerator _ _).symm
  · exact (sourceBlank_address input numerator _ _).symm

private lemma sourceFedRaw_normal {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (branch : Sampling.SourceRegister.Index)
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (Sampling.sourceFedRaw parameters index branch
      (sourceBlank input numerator flags address)).1.2.2.1 = flags.2.1 :=
  (congrArg Prod.snd (sourceFedRaw_retains_core parameters index branch
    (sourceBlank input numerator flags address))).trans
    (congrArg (fun controls : Frame.Controls => controls.2.1)
      (sourceBlank_flags input numerator flags address))

private def replaceCore
    (core : MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data 256) (raw : Raw) : Raw :=
  ((core, raw.1.2), raw.2)

private lemma digitBit_replaceCore (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : Fin (width + 1))
    (core : MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data 256) (raw : Raw) :
    (Enable.digitBit stream width bounded bit).get (replaceCore core raw) =
      (Enable.digitBit stream width bounded bit).get raw := by
  refine Fin.cases ?_ (fun index => ?_) bit
  · dsimp only [Enable.digitBit, Fin.cases_zero, streamBit, replaceCore]
    split <;> rfl
  · rfl

private lemma digitFlip_replaceCore (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : Fin (width + 1))
    (core : MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data 256) (raw : Raw) :
    replaceCore core ((Enable.digitBit stream width bounded bit).flip raw) =
      (Enable.digitBit stream width bounded bit).flip (replaceCore core raw) := by
  refine Fin.cases ?_ (fun index => ?_) bit
  · dsimp only [Enable.digitBit, Fin.cases_zero, streamBit, replaceCore]
    split <;> rfl
  · rfl

private lemma setter_action_comm {Data : Type} {encoding : BinaryLabelEncoding Data}
    {width : Nat} (word : EncodedBit.Word encoding width)
    (action : Data → Data)
    (reads : ∀ bit state, (word.bit bit).get (action state) = (word.bit bit).get state)
    (flips : ∀ bit state, action ((word.bit bit).flip state) =
      (word.bit bit).flip (action state)) (value : Fin (2 ^ width)) (state : Data) :
    action (EncodedBit.WindowLookup.resultSetConstant word value state) =
      EncodedBit.WindowLookup.resultSetConstant word value (action state) := by
  have mask : (fun bit => (word.bit bit).get (action state) ^^ value.val.testBit bit.val) =
      (fun bit => (word.bit bit).get state ^^ value.val.testBit bit.val) := by
    funext bit
    rw [reads]
  have masks :
      (⟨Nat.ofBits (fun bit => (word.bit bit).get (action state) ^^
        value.val.testBit bit.val), Nat.ofBits_lt_two_pow _⟩ : Fin (2 ^ width)) =
      ⟨Nat.ofBits (fun bit => (word.bit bit).get state ^^ value.val.testBit bit.val),
        Nat.ofBits_lt_two_pow _⟩ := by
    apply Fin.ext
    exact congrArg Nat.ofBits mask
  unfold EncodedBit.WindowLookup.resultSetConstant
  rw [masks]
  exact EncodedBit.Word.action_xorConstantStep_comm action word _ flips state

private lemma sourceFedRaw_replaceCore {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (core : MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data 256) (raw : Raw) :
    replaceCore core (Sampling.sourceFedRaw parameters index source raw) =
      Sampling.sourceFedRaw parameters index source (replaceCore core raw) := by
  unfold Sampling.sourceFedRaw
  exact setter_action_comm (Sampling.digitWord index.stream index.lowerWidth index.lowerWidth_bound)
    (replaceCore core)
    (fun bit state => digitBit_replaceCore index.stream index.lowerWidth
      index.lowerWidth_bound bit.rev core state)
    (fun bit state => digitFlip_replaceCore index.stream index.lowerWidth
      index.lowerWidth_bound bit.rev core state) _ raw

private lemma sourceBlank_replaceCore
    (firstInput firstNumerator lastInput lastNumerator :
      Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    sourceBlank lastInput lastNumerator flags address =
      replaceCore (sourceBlank lastInput lastNumerator flags address).1.1
        (sourceBlank firstInput firstNumerator flags address) := by
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · exact (sourceBlank_flags lastInput lastNumerator flags address).trans
      (sourceBlank_flags firstInput firstNumerator flags address).symm
  · exact (sourceBlank_address lastInput lastNumerator flags address).trans
      (sourceBlank_address firstInput firstNumerator flags address).symm

private lemma sourceFedRaw_same_flags_address {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (firstInput firstNumerator lastInput lastNumerator :
      Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    let first := Sampling.sourceFedRaw parameters index source
      (sourceBlank firstInput firstNumerator flags address)
    let last := Sampling.sourceFedRaw parameters index source
      (sourceBlank lastInput lastNumerator flags address)
    (last.1.2, last.2) = (first.1.2, first.2) := by
  dsimp only
  have actual := congrArg (fun raw : Raw => (raw.1.2, raw.2))
    (sourceFedRaw_replaceCore parameters index source
      (sourceBlank lastInput lastNumerator flags address).1.1
      (sourceBlank firstInput firstNumerator flags address))
  rw [← sourceBlank_replaceCore] at actual
  exact actual.symm

private lemma sourceFedRaw_changePoint {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index)
    (firstInput firstNumerator lastInput lastNumerator :
      Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    let first := Sampling.sourceFedRaw parameters index source
      (sourceBlank firstInput firstNumerator flags address)
    Sampling.sourceFedRaw parameters index source
        (sourceBlank lastInput lastNumerator flags address) =
      sourceBlank lastInput lastNumerator first.1.2 first.2 := by
  dsimp only
  have suffix := sourceFedRaw_same_flags_address parameters index source
    firstInput firstNumerator lastInput lastNumerator flags address
  exact (sourceFedRaw_blank parameters index source lastInput lastNumerator flags address).trans
    (congrArg (fun pair : Frame.Controls × Address =>
      sourceBlank lastInput lastNumerator pair.1 pair.2) suffix)

private lemma sourceBlank_digit_same (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : Fin (width + 1))
    (firstInput firstNumerator lastInput lastNumerator :
      Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (Enable.digitBit stream width bounded bit).get
        (sourceBlank firstInput firstNumerator flags address) =
      (Enable.digitBit stream width bounded bit).get
        (sourceBlank lastInput lastNumerator flags address) := by
  rw [sourceBlank_replaceCore firstInput firstNumerator lastInput lastNumerator flags address,
    digitBit_replaceCore]

private lemma physicalBank_same_of_readouts {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex) (first last : Raw)
    (reads : ∀ bit, (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).get
      first = (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).get last) :
    (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel first)).1 =
      (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
        (parameters.physicalLabel last)).1 := by
  apply tupleCoordinates_injective (index.lowerWidth + 1)
  funext bit
  rw [congrFun (bankCoordinates_values _ _ _) bit,
    congrFun (bankCoordinates_values _ _ _) bit]
  apply Fin.ext
  change (parameters.physicalLabel first (parameters.wire index bit)).val =
    (parameters.physicalLabel last (parameters.wire index bit)).val
  exact (Sampling.placedLabel_bit encoding (QubitLayout.canonical encoding.width)
    parameters.sameWires (Enable.digitBit index.stream index.lowerWidth
      index.lowerWidth_bound bit) first).trans
    ((congrArg (fun value : Bool => (finTwoEquiv.symm value).val) (reads bit)).trans
      (Sampling.placedLabel_bit encoding (QubitLayout.canonical encoding.width)
        parameters.sameWires (Enable.digitBit index.stream index.lowerWidth
          index.lowerWidth_bound bit) last).symm)

private lemma sourceBlank_bank_same {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (firstInput firstNumerator lastInput lastNumerator :
      Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (flags : Frame.Controls) (address : Address) :
    (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel (sourceBlank firstInput firstNumerator flags address))).1 =
      (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
        (parameters.physicalLabel (sourceBlank lastInput lastNumerator flags address))).1 :=
  physicalBank_same_of_readouts parameters index _ _
    (fun bit => sourceBlank_digit_same _ _ _ bit _ _ _ _ flags address)

private lemma sourceFedRaw_bank {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index) (raw : Raw) :
    bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
        (parameters.physicalLabel (Sampling.sourceFedRaw parameters index source raw)) =
      ((binaryEquiv (index.lowerWidth + 1)).symm
          (parameters.sourcePartition index source).1,
        (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
          (parameters.physicalLabel raw)).2) := by
  unfold Sampling.sourceFedRaw
  exact Sampling.placedLabel_set_bank encoding (QubitLayout.canonical encoding.width)
    parameters.sameWires (Sampling.digitWord index.stream index.lowerWidth index.lowerWidth_bound)
    (Sampling.digitWord_distinct _ _ _) (parameters.ports index)
    (fun bit => by
      change parameters.wire index bit = parameters.wire index bit.rev.rev
      exact congrArg (parameters.wire index) (Fin.rev_rev bit).symm)
    (parameters.sourcePartition index source).1 raw

private lemma zeroBank_fedRaw {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex) (Reference : Register)
    (source : Sampling.SourceRegister.Index) (raw : Raw)
    (remaining : Sampling.SourceRegister.Index) (reference : Reference.Index)
    (zero : (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel raw)).1 = Partner.zeroBits (index.lowerWidth + 1)) :
    windowZeroBankColumn (parameters.ports index) (Sampling.SourceRegister.prod Reference)
        (parameters.physicalLabel (Sampling.sourceFedRaw parameters index source raw),
          remaining, reference) =
      (parameters.physicalLabel raw, remaining, reference) := by
  apply (referenceBankCoordinates (parameters.ports index).wires
    (parameters.ports index).qubits (Sampling.SourceRegister.prod Reference)).injective
  rw [windowZeroBankColumn, Equiv.apply_symm_apply,
    referenceBankCoordinates_apply, referenceBankCoordinates_apply,
    sourceFedRaw_bank, zero]

private lemma fedRaw_frequency {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex) (Reference : Register)
    (source : Sampling.SourceRegister.Index) (raw : Raw)
    (remaining : Sampling.SourceRegister.Index) (reference : Reference.Index) :
    binaryEquiv (index.lowerWidth + 1)
        (referenceBankCoordinates (parameters.ports index).wires
          (parameters.ports index).qubits (Sampling.SourceRegister.prod Reference)
          (parameters.physicalLabel (Sampling.sourceFedRaw parameters index source raw),
            remaining, reference)).1 =
      (parameters.sourcePartition index source).1 := by
  rw [referenceBankCoordinates_apply, sourceFedRaw_bank, Equiv.apply_symm_apply]

private lemma reversed_bits_zero_iff (width : Nat) (value : Fin (2 ^ width)) :
    (∀ bit : Fin width, value.val.testBit bit.rev.val = false) ↔ value.val = 0 := by
  constructor
  · intro zeros
    have same : value = 0 := by
      apply Nat.FixedWidth.word_eq_of_testBit_eq
      intro bit
      simpa only [Fin.rev_rev, Fin.val_zero, Nat.zero_testBit] using zeros bit.rev
    simpa only [Fin.val_zero] using congrArg Fin.val same
  · intro zero bit
    rw [zero, Nat.zero_testBit]

private lemma nonzero_of_reversed_readouts {width : Nat} (value : Fin (2 ^ width))
    (reads : Fin width → Bool)
    (same : ∀ bit, reads bit = value.val.testBit bit.rev.val) :
    (!decide (∀ bit, reads bit = false)) = decide (value.val ≠ 0) := by
  classical
  have zeros : (∀ bit, reads bit = false) ↔ value.val = 0 := by
    simpa only [same] using reversed_bits_zero_iff width value
  rw [← decide_not, decide_eq_decide]
  exact not_congr zeros

private lemma sourceFedRaw_enabled {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (source : Sampling.SourceRegister.Index) (raw : Raw) :
    Chain.Control.digitEnabled index.stream index.lowerWidth index.lowerWidth_bound
        (Sampling.sourceFedRaw parameters index source raw) =
      decide ((parameters.sourcePartition index source).1.val ≠ 0) :=
  nonzero_of_reversed_readouts (parameters.sourcePartition index source).1
    (fun bit => (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit).get
      (Sampling.sourceFedRaw parameters index source raw))
    (Sampling.sourceFedRaw_digit parameters index source raw)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

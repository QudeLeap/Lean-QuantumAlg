/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CopyValue
/-!
# Homogeneous arithmetic-block banks

This module supplies the structural product combinators used by the
width-parameterized ECADD assembly.  A bank is a right-nested product of a
fixed number of identical physical arithmetic carriers.  Encoded gates and
word views can be lifted to one selected block on the common physical layout.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace Arithmetic

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- A right-nested bank of `count` identical arithmetic carriers. -/
inductive BlockBank (Block : Type) : Nat → Type
  | nil : BlockBank Block 0
  | cons {count : Nat} : Block → BlockBank Block count → BlockBank Block count.succ
deriving DecidableEq

namespace BlockBank

variable {Block : Type}

/-- Structural head/tail view of a nonempty bank. -/
def consEquiv (count : Nat) :
    BlockBank Block count.succ ≃ Block × BlockBank Block count where
  toFun := fun state => by
    cases state with
    | cons head tail => exact (head, tail)
  invFun := fun state => BlockBank.cons state.1 state.2
  left_inv := by
    intro state
    cases state
    rfl
  right_inv := by
    intro state
    rcases state with ⟨head, tail⟩
    rfl

/-- Zero-width encoding of the empty bank. -/
def emptyEncoding : BinaryLabelEncoding (BlockBank Block 0) where
  width := 0
  encode := fun _ => 0
  encode_injective := by
    intro left right _
    cases left
    cases right
    rfl

/-- Product encoding of a homogeneous block bank. -/
@[implicit_reducible]
def encoding (blockEncoding : BinaryLabelEncoding Block) :
    (count : Nat) → BinaryLabelEncoding (BlockBank Block count)
  | 0 => emptyEncoding
  | Nat.succ count =>
      (BinaryLabelEncoding.prod blockEncoding (encoding blockEncoding count)).relabel
        (consEquiv count)

@[simp] lemma encoding_width (blockEncoding : BinaryLabelEncoding Block) :
    ∀ count, (encoding blockEncoding count).width = count * blockEncoding.width
  | 0 => by simp [encoding, emptyEncoding]
  | Nat.succ count => by
      change blockEncoding.width + (encoding blockEncoding count).width = _
      rw [encoding_width blockEncoding count]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Read one selected bank entry. -/
def get : {count : Nat} → BlockBank Block count → Fin count → Block
  | Nat.succ _, .cons head tail, index =>
      Fin.cases head (fun later => get tail later) index

/-- Pointwise equality of selected blocks determines a fixed-size bank. -/
lemma ext_get {count : Nat} (left right : BlockBank Block count)
    (hget : ∀ index, get left index = get right index) : left = right := by
  induction count with
  | zero =>
      cases left
      cases right
      rfl
  | succ count ih =>
      cases left with
      | cons leftHead leftTail =>
          cases right with
          | cons rightHead rightTail =>
              have hhead : leftHead = rightHead := hget 0
              have htail : leftTail = rightTail :=
                ih leftTail rightTail (fun index => hget index.succ)
              cases hhead
              cases htail
              rfl

/-- Replace one selected bank entry. -/
def set : {count : Nat} → BlockBank Block count → Fin count → Block →
    BlockBank Block count
  | Nat.succ _, .cons head tail, index, value =>
      Fin.cases (.cons value tail)
        (fun later => .cons head (set tail later value)) index

@[simp] lemma get_set_same {count : Nat} (state : BlockBank Block count)
    (index : Fin count) (value : Block) :
    get (set state index value) index = value := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · rfl
          · simpa [get, set] using ih tail later

@[simp] lemma get_set_of_ne {count : Nat} (state : BlockBank Block count)
    (updated observed : Fin count) (value : Block) (hne : observed ≠ updated) :
    get (set state updated value) observed = get state observed := by
  induction count with
  | zero => exact Fin.elim0 observed
  | succ count ih =>
      cases state with
      | cons head tail =>
          rcases updated with ⟨_ | updated, hupdated⟩ <;>
            rcases observed with ⟨_ | observed, hobserved⟩
          · exact (hne (Fin.ext rfl)).elim
          · rfl
          · rfl
          · simpa [get, set] using
              ih tail ⟨updated, by omega⟩ ⟨observed, by omega⟩ (by
                intro h
                apply hne
                apply Fin.ext
                exact congrArg Nat.succ (congrArg Fin.val h))

@[simp] lemma set_get_same {count : Nat} (state : BlockBank Block count)
    (index : Fin count) :
    set state index (get state index) = state := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · rfl
          · simpa [get, set] using
              congrArg (fun updated => BlockBank.cons head updated)
                (ih tail later)

/-- Lift an encoded bit from one selected block into the whole bank. -/
def bitAt (blockEncoding : BinaryLabelEncoding Block) :
    {count : Nat} → Fin count → EncodedBit blockEncoding →
      EncodedBit (encoding blockEncoding count)
  | _ + 1, ⟨0, _⟩, bit =>
      (BinaryLabelEncoding.prodLeftBit blockEncoding
        (encoding blockEncoding _) bit).relabel (consEquiv _)
  | _ + 1, ⟨index + 1, h⟩, bit =>
      (BinaryLabelEncoding.prodRightBit blockEncoding
        (encoding blockEncoding _)
        (bitAt blockEncoding ⟨index, by omega⟩ bit)).relabel (consEquiv _)

/-- Lift an encoded word from one selected block into the whole bank. -/
def wordAt (blockEncoding : BinaryLabelEncoding Block) {width count : Nat}
    (index : Fin count) (word : EncodedBit.Word blockEncoding width) :
    EncodedBit.Word (encoding blockEncoding count) width where
  bit := fun bit => bitAt blockEncoding index (word.bit bit)

@[simp] lemma bitAt_get (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count) (bit : EncodedBit blockEncoding)
    (state : BlockBank Block count) :
    (bitAt blockEncoding index bit).get state = bit.get (get state index) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · rfl
          · change (bitAt blockEncoding later bit).get tail =
              bit.get (get tail later)
            exact ih later tail

@[simp] lemma bitAt_flip (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count) (bit : EncodedBit blockEncoding)
    (state : BlockBank Block count) :
    (bitAt blockEncoding index bit).flip state =
      set state index (bit.flip (get state index)) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · rfl
          · change BlockBank.cons head ((bitAt blockEncoding later bit).flip tail) =
              BlockBank.cons head (set tail later (bit.flip (get tail later)))
            exact congrArg (fun updated => BlockBank.cons head updated)
              (ih later tail)

@[simp] lemma set_set_same {count : Nat} (state : BlockBank Block count)
    (index : Fin count) (first second : Block) :
    set (set state index first) index second = set state index second := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · rfl
          · change BlockBank.cons head (set (set tail later first) later second) =
              BlockBank.cons head (set tail later second)
            exact congrArg (fun updated => BlockBank.cons head updated)
              (ih tail later)

/-- Bits lifted from different bank blocks are physically disjoint. -/
lemma bitAt_wire_ne_of_index_ne (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (left right : Fin count) (hne : left ≠ right)
    (leftBit rightBit : EncodedBit blockEncoding) :
    (bitAt blockEncoding left leftBit).wire ≠
      (bitAt blockEncoding right rightBit).wire := by
  induction count with
  | zero => exact Fin.elim0 left
  | succ count ih =>
      rcases left with ⟨_left | left, hl⟩ <;>
        rcases right with ⟨_right | right, hr⟩
      · exact (hne rfl).elim
      · intro hwire
        have hbase :=
          (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
          blockEncoding (encoding blockEncoding count)
          (bitAt blockEncoding ⟨right, by omega⟩ rightBit) leftBit).symm
        apply hbase
        apply Fin.ext
        exact congrArg Fin.val hwire
      · intro hwire
        have hbase := EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
          blockEncoding (encoding blockEncoding count)
          (bitAt blockEncoding ⟨left, by omega⟩ leftBit) rightBit
        apply hbase
        apply Fin.ext
        exact congrArg Fin.val hwire
      · simp only [bitAt, encoding, EncodedBit.relabel]
        apply EncodedBit.GateSpec.prodRightWire_ne blockEncoding
        exact ih ⟨left, by omega⟩ ⟨right, by omega⟩
          (by
            intro h
            apply hne
            apply Fin.ext
            simpa using congrArg Fin.val h)

/-- A complete encoded-word port with a structural setter. -/
structure WordPort (blockEncoding : BinaryLabelEncoding Block) (width : Nat) where
  /-- Encoded bit lenses selecting the word's physical wires. -/
  word : EncodedBit.Word blockEncoding width
  /-- Read the fixed-width word from one carrier value. -/
  read : Block → Nat.FixedWidth.Word width
  /-- Replace the selected word while preserving the surrounding carrier. -/
  set : Block → Nat.FixedWidth.Word width → Block
  set_read : ∀ state, set state (read state) = state
  read_set : ∀ state value, read (set state value) = value
  set_set : ∀ state first second, set (set state first) second = set state second
  get_bit : ∀ bit state,
    (word.bit bit).get state = (read state).val.testBit bit.val
  pairwise_ne : ∀ left right, left ≠ right →
    (word.bit left).wire ≠ (word.bit right).wire
  clear_flip : ∀ bit state,
    set ((word.bit bit).flip state) 0 = set state 0

namespace WordPort

variable {blockEncoding : BinaryLabelEncoding Block} {width count : Nat}

/-- Lift a word port through an untouched right product factor. -/
def prodLeft {Right : Type} (port : WordPort blockEncoding width)
    (right : BinaryLabelEncoding Right) :
    WordPort (BinaryLabelEncoding.prod blockEncoding right) width where
  word := { bit := fun bit =>
    BinaryLabelEncoding.prodLeftBit blockEncoding right (port.word.bit bit) }
  read := fun state => port.read state.1
  set := fun state value => (port.set state.1 value, state.2)
  set_read := by intro state; simp [port.set_read]
  read_set := by intro state value; simp [port.read_set]
  set_set := by intro state first second; simp [port.set_set]
  get_bit := by intro bit state; exact port.get_bit bit state.1
  pairwise_ne := by
    intro left rightBit hne
    exact EncodedBit.GateSpec.prodLeftWire_ne right
      (port.pairwise_ne left rightBit hne)
  clear_flip := by
    intro bit state
    change (port.set ((port.word.bit bit).flip state.1) 0, state.2) =
      (port.set state.1 0, state.2)
    rw [port.clear_flip]

/-- Lift a word port through an untouched left product factor. -/
def prodRight {Left : Type} (left : BinaryLabelEncoding Left)
    (port : WordPort blockEncoding width) :
    WordPort (BinaryLabelEncoding.prod left blockEncoding) width where
  word := { bit := fun bit =>
    BinaryLabelEncoding.prodRightBit left blockEncoding (port.word.bit bit) }
  read := fun state => port.read state.2
  set := fun state value => (state.1, port.set state.2 value)
  set_read := by intro state; simp [port.set_read]
  read_set := by intro state value; simp [port.read_set]
  set_set := by intro state first second; simp [port.set_set]
  get_bit := by intro bit state; exact port.get_bit bit state.2
  pairwise_ne := by
    intro leftBit right hne
    exact EncodedBit.GateSpec.prodRightWire_ne left
      (port.pairwise_ne leftBit right hne)
  clear_flip := by
    intro bit state
    change (state.1, port.set ((port.word.bit bit).flip state.2) 0) =
      (state.1, port.set state.2 0)
    rw [port.clear_flip]

/-- Literal CNOT routing gates between two ports of one encoded carrier. -/
def directCopyGates (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) : List (EncodedBit.GateSpec blockEncoding) :=
  EncodedBit.Word.xorIntoGates source.word target.word hdisjoint

/-- A direct word-port copy contains one CNOT per word bit. -/
@[simp] lemma directCopyGates_length (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) :
    (directCopyGates source target hdisjoint).length = width := by
  exact EncodedBit.Word.xorIntoGates_length source.word target.word hdisjoint

/-- A direct word-port copy contains exactly one CNOT per word bit. -/
lemma directCopyGates_cnotMultiplicity_sum
    (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) :
    ((directCopyGates source target hdisjoint).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = width := by
  exact EncodedBit.Word.xorIntoGates_cnotMultiplicity_sum
    source.word target.word hdisjoint

/-- A direct word-port copy contains no Toffoli gate. -/
lemma directCopyGates_toffoliMultiplicity_sum
    (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) :
    ((directCopyGates source target hdisjoint).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  exact EncodedBit.Word.xorIntoGates_toffoliMultiplicity_sum
    source.word target.word hdisjoint

/-- Literal CNOT routing between two ports of one encoded carrier. -/
def directCopyProgram (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (blockEncoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (directCopyGates source target hdisjoint)

/-- Classical basis-state action of the literal direct-copy gate list. -/
def directCopyStep (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) : Block → Block :=
  EncodedBit.GateSpec.stepList (directCopyGates source target hdisjoint)

lemma directCopy_realizes (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire) :
    UnitaryCircuit.Realizes blockEncoding
      (directCopyProgram source target hdisjoint) environment
      (directCopyStep source target hdisjoint) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

/-- A direct CNOT copy installs the source word in a clean target port. -/
lemma directCopyStep_eq_set_of_clean
    (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠ (source.word.bit sourceBit).wire)
    (state : Block) (value : Nat.FixedWidth.Word width)
    (hsource : source.read state = value) (htarget : target.read state = 0) :
    directCopyStep source target hdisjoint state = target.set state value := by
  have hcopy := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    source.word target.word hdisjoint target.read
    (fun current => target.set current 0) target.set
    (fun current => by rw [target.set_set, target.set_read])
    target.get_bit target.pairwise_ne hcross target.clear_flip
    state value htarget (fun bit => by rw [source.get_bit, hsource])
  rw [target.set_set] at hcopy
  exact hcopy

/-- A direct CNOT copy clears the target when source and target initially hold
the same word. -/
lemma directCopyStep_eq_set_zero_of_equal
    (source target : WordPort blockEncoding width)
    (hdisjoint : ∀ bit, (source.word.bit bit).wire ≠
      (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠ (source.word.bit sourceBit).wire)
    (state : Block) (hequal : source.read state = target.read state) :
    directCopyStep source target hdisjoint state = target.set state 0 := by
  let result := directCopyStep source target hdisjoint state
  have hresultFrame : target.set result 0 = target.set state 0 := by
    exact EncodedBit.Word.xorIntoStep_preserves_projection
      source.word target.word hdisjoint (fun current => target.set current 0)
      target.clear_flip state
  have hresultWord : target.read result = 0 := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro bit
    rw [← target.get_bit]
    unfold result directCopyStep directCopyGates
    change (target.word.bit bit).get
        (EncodedBit.Word.xorIntoStep source.word target.word hdisjoint state) = _
    rw [EncodedBit.Word.xorIntoStep_get_target source.word target.word
      hdisjoint bit
      (fun other hne => target.pairwise_ne other bit hne)
      (fun other => hcross bit other)]
    rw [target.get_bit, source.get_bit, hequal]
    simp
  calc
    result = target.set (target.set result 0) (target.read result) := by
      rw [target.set_set, target.set_read]
    _ = target.set (target.set state 0) 0 :=
      congrArg₂ target.set hresultFrame hresultWord
    _ = target.set state 0 := by rw [target.set_set]

/-- Lift one block-local word lens to a selected position in a block bank. -/
def bankWord (port : WordPort blockEncoding width) (index : Fin count) :
    EncodedBit.Word (encoding blockEncoding count) width :=
  wordAt blockEncoding index port.word

/-- Read one port value from the selected block-bank position. -/
def bankRead (port : WordPort blockEncoding width)
    (index : Fin count) (state : BlockBank Block count) :
    Nat.FixedWidth.Word width :=
  port.read (get state index)

/-- Replace one port value at the selected block-bank position. -/
def bankSet (port : WordPort blockEncoding width)
    (index : Fin count) (state : BlockBank Block count)
    (value : Nat.FixedWidth.Word width) : BlockBank Block count :=
  BlockBank.set state index (port.set (get state index) value)

@[simp] lemma bankRead_bankSet (port : WordPort blockEncoding width)
    (index : Fin count) (state : BlockBank Block count)
    (value : Nat.FixedWidth.Word width) :
    port.bankRead index (port.bankSet index state value) = value := by
  unfold bankRead bankSet
  rw [get_set_same, port.read_set]

@[simp] lemma bankSet_bankRead (port : WordPort blockEncoding width)
    (index : Fin count) (state : BlockBank Block count) :
    port.bankSet index state (port.bankRead index state) = state := by
  unfold bankRead bankSet
  rw [port.set_read, set_get_same]

@[simp] lemma bankSet_bankSet (port : WordPort blockEncoding width)
    (index : Fin count) (state : BlockBank Block count)
    (first second : Nat.FixedWidth.Word width) :
    port.bankSet index (port.bankSet index state first) second =
      port.bankSet index state second := by
  unfold bankSet
  rw [get_set_same, port.set_set, set_set_same]

lemma bankWord_get (port : WordPort blockEncoding width)
    (index : Fin count) (bit : Fin width) (state : BlockBank Block count) :
    ((port.bankWord index).bit bit).get state =
      (port.bankRead index state).val.testBit bit.val := by
  simp [bankWord, bankRead, wordAt, port.get_bit]

lemma bankWord_pairwise_ne (port : WordPort blockEncoding width)
    (index : Fin count) (left right : Fin width) (hne : left ≠ right) :
    ((port.bankWord index).bit left).wire ≠
      ((port.bankWord index).bit right).wire := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun later => ?_) index
      · intro hwire
        apply port.pairwise_ne left right hne
        apply Fin.ext
        have hv := congrArg Fin.val hwire
        change ((port.word.bit left).wire).val =
          ((port.word.bit right).wire).val at hv
        exact hv
      · simp only [bankWord, wordAt]
        apply EncodedBit.GateSpec.prodRightWire_ne blockEncoding
        exact ih later

lemma bankSet_clear_flip (port : WordPort blockEncoding width)
    (index : Fin count) (bit : Fin width) (state : BlockBank Block count) :
    port.bankSet index (((port.bankWord index).bit bit).flip state) 0 =
      port.bankSet index state 0 := by
  change port.bankSet index
      ((bitAt blockEncoding index (port.word.bit bit)).flip state) 0 = _
  unfold bankSet
  rw [bitAt_flip, get_set_same, port.clear_flip, set_set_same]

/-- A selected bank word as a complete port over the bank carrier. -/
def bankPort (port : WordPort blockEncoding width) (index : Fin count) :
    WordPort (encoding blockEncoding count) width where
  word := port.bankWord index
  read := port.bankRead index
  set := port.bankSet index
  set_read := port.bankSet_bankRead index
  read_set := port.bankRead_bankSet index
  set_set := port.bankSet_bankSet index
  get_bit := port.bankWord_get index
  pairwise_ne := port.bankWord_pairwise_ne index
  clear_flip := port.bankSet_clear_flip index

/-- Literal CNOT routing between two different bank blocks. -/
def copyProgram (source target : WordPort blockEncoding width)
    (sourceIndex targetIndex : Fin count) (hne : sourceIndex ≠ targetIndex) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding blockEncoding count).width).toQuantum :=
  EncodedBit.Word.xorIntoProgram (QubitLayout.canonical _) .empty
    (source.bankWord sourceIndex)
    (target.bankWord targetIndex)
    (fun bit => bitAt_wire_ne_of_index_ne blockEncoding sourceIndex targetIndex
      hne (source.word.bit bit) (target.word.bit bit))

/-- Folded action of literal inter-block CNOT routing. -/
def copyStep (source target : WordPort blockEncoding width)
    (sourceIndex targetIndex : Fin count) (hne : sourceIndex ≠ targetIndex) :
    BlockBank Block count → BlockBank Block count :=
  EncodedBit.Word.xorIntoStep (source.bankWord sourceIndex)
    (target.bankWord targetIndex)
    (fun bit => bitAt_wire_ne_of_index_ne blockEncoding sourceIndex targetIndex
      hne (source.word.bit bit) (target.word.bit bit))

lemma copy_realizes (source target : WordPort blockEncoding width)
    (sourceIndex targetIndex : Fin count) (hne : sourceIndex ≠ targetIndex) :
    UnitaryCircuit.Realizes (encoding blockEncoding count)
      (copyProgram source target sourceIndex targetIndex hne) environment
      (copyStep source target sourceIndex targetIndex hne) :=
  EncodedBit.Word.xorInto_realizes (environment := environment) (QubitLayout.canonical _) .empty _
    _ _

/-- Copying a source port into a clean target port installs the source word. -/
lemma copyStep_eq_bankSet_of_clean
    (source target : WordPort blockEncoding width)
    (sourceIndex targetIndex : Fin count) (hne : sourceIndex ≠ targetIndex)
    (state : BlockBank Block count) (value : Nat.FixedWidth.Word width)
    (hsource : source.bankRead sourceIndex state = value)
    (htarget : target.bankRead targetIndex state = 0) :
    copyStep source target sourceIndex targetIndex hne state =
      target.bankSet targetIndex state value := by
  have hcopy := EncodedBit.Word.xorIntoStep_eq_set_of_clean
    (source.bankWord sourceIndex) (target.bankWord targetIndex)
    (fun bit => bitAt_wire_ne_of_index_ne blockEncoding sourceIndex targetIndex
      hne (source.word.bit bit) (target.word.bit bit))
    (target.bankRead targetIndex)
    (fun current => target.bankSet targetIndex current 0)
    (fun frame routed => target.bankSet targetIndex frame routed)
    (fun current => by
      rw [target.bankSet_bankSet, target.bankSet_bankRead])
    (target.bankWord_get targetIndex)
    (target.bankWord_pairwise_ne targetIndex)
    (fun sourceBit targetBit =>
      bitAt_wire_ne_of_index_ne blockEncoding targetIndex sourceIndex
        (Ne.symm hne) (target.word.bit targetBit) (source.word.bit sourceBit))
    (target.bankSet_clear_flip targetIndex)
    state value htarget
    (fun bit => by rw [source.bankWord_get, hsource])
  rw [target.bankSet_bankSet] at hcopy
  exact hcopy

end WordPort

/-- Lift a literal block gate list to one selected bank entry. -/
def liftGates (blockEncoding : BinaryLabelEncoding Block) :
    {count : Nat} → Fin count → List (EncodedBit.GateSpec blockEncoding) →
      List (EncodedBit.GateSpec (encoding blockEncoding count))
  | _ + 1, ⟨0, _⟩, gates =>
      (gates.map (EncodedBit.GateSpec.prodLeft (encoding blockEncoding _))).map
        (EncodedBit.GateSpec.relabel (consEquiv _))
  | _ + 1, ⟨index + 1, h⟩, gates =>
      ((liftGates blockEncoding ⟨index, by omega⟩ gates).map
        (EncodedBit.GateSpec.prodRight blockEncoding)).map
        (EncodedBit.GateSpec.relabel (consEquiv _))

/-- Lifting a block schedule into one selected bank entry preserves its
complete ordered primitive-event trace. -/
lemma liftGates_map_event (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count)
    (gates : List (EncodedBit.GateSpec blockEncoding)) :
    (liftGates blockEncoding index gates).map (EncodedBit.GateSpec.event .empty) =
      gates.map (EncodedBit.GateSpec.event .empty) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases index with
      | mk index hindex =>
          cases index with
          | zero =>
              rw [liftGates]
              exact
                (EncodedBit.GateSpec.map_event_relabel .empty (consEquiv count) _).trans
                  (EncodedBit.GateSpec.map_event_prodLeft _ _)
          | succ index =>
              rw [liftGates]
              exact
                (EncodedBit.GateSpec.map_event_relabel .empty (consEquiv count) _).trans
                  ((EncodedBit.GateSpec.map_event_prodRight blockEncoding _).trans
                    (ih ⟨index, by omega⟩))

/-- Lifting a block schedule into a bank changes only wire addresses, not the
number of executed primitive gates. -/
lemma liftGates_length (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count)
    (gates : List (EncodedBit.GateSpec blockEncoding)) :
    (liftGates blockEncoding index gates).length = gates.length := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases index with
      | mk index hindex =>
          cases index with
          | zero => rw [liftGates, List.length_map, List.length_map]
          | succ index =>
              rw [liftGates, List.length_map, List.length_map]
              exact ih ⟨index, by omega⟩

/-- Selected-bank lifting preserves the exact Toffoli coordinate of the
underlying block schedule. -/
lemma liftGates_toffoliMultiplicity_sum
    (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count)
    (gates : List (EncodedBit.GateSpec blockEncoding)) :
    ((liftGates blockEncoding index gates).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum := by
  exact EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (liftGates_map_event blockEncoding index gates)

/-- Folding a lifted gate list updates exactly its selected bank entry. -/
lemma liftGates_stepList (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count)
    (gates : List (EncodedBit.GateSpec blockEncoding))
    (state : BlockBank Block count) :
    EncodedBit.GateSpec.stepList (liftGates blockEncoding index gates) state =
      set state index (EncodedBit.GateSpec.stepList gates (get state index)) := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases state with
      | cons head tail =>
          refine Fin.cases ?_ (fun later => ?_) index
          · change
              EncodedBit.GateSpec.stepList
                  ((gates.map (EncodedBit.GateSpec.prodLeft
                    (encoding blockEncoding count))).map
                    (EncodedBit.GateSpec.relabel (consEquiv count)))
                  (.cons head tail) =
                .cons (EncodedBit.GateSpec.stepList gates head) tail
            rw [EncodedBit.GateSpec.stepList_relabel,
              EncodedBit.GateSpec.stepList_prodLeft]
            rfl
          · change
              EncodedBit.GateSpec.stepList
                  (((liftGates blockEncoding later gates).map
                    (EncodedBit.GateSpec.prodRight blockEncoding)).map
                    (EncodedBit.GateSpec.relabel (consEquiv count)))
                  (.cons head tail) =
                .cons head
                  (set tail later
                    (EncodedBit.GateSpec.stepList gates (get tail later)))
            rw [EncodedBit.GateSpec.stepList_relabel,
              EncodedBit.GateSpec.stepList_prodRight]
            change
              BlockBank.cons head
                  (EncodedBit.GateSpec.stepList
                    (liftGates blockEncoding later gates) tail) = _
            rw [ih later tail]

/-- The literal selected-bank gate list realizes its folded update. -/
lemma liftGates_realizes (blockEncoding : BinaryLabelEncoding Block)
    {count : Nat} (index : Fin count)
    (gates : List (EncodedBit.GateSpec blockEncoding)) :
    UnitaryCircuit.Realizes (encoding blockEncoding count)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (liftGates blockEncoding index gates)) environment
      (fun state =>
        set state index (EncodedBit.GateSpec.stepList gates (get state index))) :=
  EncodedBit.GateSpec.realizesList_congrStep (environment := environment)
    (QubitLayout.canonical _) .empty _
    (liftGates_stepList blockEncoding index gates)

end BlockBank

end

end Arithmetic
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end

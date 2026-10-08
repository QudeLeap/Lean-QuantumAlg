/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Montgomery.Multiplication
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Montgomery.Inversion
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.RegisterRouting

/-!
# Out-of-place Montgomery operations on the in-place point carrier

The lower multiplication kernel is a modular accumulator.  The point
schedule needs an out-of-place operation which XORs a product into an
arbitrary output word [RNSL17, ECDLP.tex:659].  These ledgers realize that
interface by saving live `x1` and `t0` values in the one existing `2f` history
word, computing the Montgomery product into a clean `t0`, XOR-copying it to
the requested output, and reversing the complete computation.  Every save is erased before the
next inversion and no wire is added to the carrier.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace MontgomeryOperations

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Clean arithmetic boundary shared by inversion and the three out-of-place
Montgomery operations. -/
def cleanState (fieldWidth counterWidth : Nat)
    (control : Bool) (mutableY «λ» : Word fieldWidth)
    (p mutableX t0 : Word fieldWidth) :
    Layout.Registers fieldWidth counterWidth where
  control := control
  mutableY := mutableY
  «λ» := «λ»
  arithmetic :=
    { core := MK.initialRegisters fieldWidth counterWidth p mutableX
      shared := MK.Compact.cleanSharedWork fieldWidth counterWidth
      target := t0 }

/-- Classical modulus word used to normalize the compact inversion seed into
the multiplication boundary. -/
def modulusWord (fieldWidth p : Nat) (hp : p < 2 ^ fieldWidth) :
    Word fieldWidth :=
  ⟨p, hp⟩

/-- Bit mask changing the compact inversion seed's low coefficient from `1`
to the parked modulus `p`. -/
def coefficientNormalizationWord (fieldWidth p : Nat)
    (hp : p < 2 ^ fieldWidth) : Word fieldWidth :=
  ⟨(1 : Word fieldWidth).val ^^^ p,
    Nat.xor_lt_two_pow (1 : Word fieldWidth).isLt hp⟩

@[simp] theorem coefficientNormalizationWord_val (fieldWidth p : Nat)
    (hp : p < 2 ^ fieldWidth) :
    (coefficientNormalizationWord fieldWidth p hp).val =
      (1 : Word fieldWidth).val ^^^ p :=
  rfl

/-- Normalize the three nonzero fields of a compact inversion seed.  The
core `u=p` and `active=true` fields are cleared, while `s=1` is changed to
`s=p`, the parked-modulus boundary required by the certified multiplication
ledger.  The mutable input and coefficient are routed separately by each
operation. -/
def normalizeGates (fieldWidth counterWidth p : Nat)
    (hp : p < 2 ^ fieldWidth) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  EncodedBit.Word.xorConstantGates
      (RegisterRouting.uWord fieldWidth counterWidth)
      (modulusWord fieldWidth p hp) ++
    EncodedBit.Word.xorConstantGates
      (RegisterRouting.sCoefficientWord fieldWidth counterWidth)
      (coefficientNormalizationWord fieldWidth p hp) ++
    [.x (RegisterRouting.activeBit fieldWidth counterWidth)]

/-! ## Reusable compute--copy--uncompute semantics -/

/-- A literal constant xor updates one structural word port to the word
specified by its output bits. -/
private theorem xorConstantStep_eq_set_of_testBit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (port : Arithmetic.BlockBank.WordPort encoding width)
    (constant : Fin (2 ^ width)) (state : Data)
    (value : Word width)
    (hvalue : ∀ bit : Fin width, value.val.testBit bit.val =
      ((port.read state).val.testBit bit.val ^^
        constant.val.testBit bit.val)) :
    EncodedBit.Word.xorConstantStep port.word constant state =
      port.set state value := by
  have hframe :
      port.set (EncodedBit.Word.xorConstantStep port.word constant state) 0 =
        port.set state 0 := by
    unfold EncodedBit.Word.xorConstantStep
    apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
      (project := fun next => port.set next 0)
    intro gate hgate
    rw [EncodedBit.Word.xorConstantGates] at hgate
    rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
    exact port.clear_flip bit
  have hresult :
      port.read (EncodedBit.Word.xorConstantStep port.word constant state) =
        value := by
    apply word_eq_of_testBit_eq
    intro bit
    rw [← port.get_bit bit
      (EncodedBit.Word.xorConstantStep port.word constant state)]
    rw [EncodedBit.Word.xorConstantStep_get_target port.word constant bit
      (fun other hne => port.pairwise_ne other bit hne)]
    rw [port.get_bit bit state]
    exact (hvalue bit).symm
  calc
    EncodedBit.Word.xorConstantStep port.word constant state =
        port.set
          (port.set
            (EncodedBit.Word.xorConstantStep port.word constant state) 0)
          (port.read
            (EncodedBit.Word.xorConstantStep port.word constant state)) := by
              rw [port.set_set, port.set_read]
    _ = port.set (port.set state 0) value := by rw [hframe, hresult]
    _ = port.set state value := by rw [port.set_set]

/-- Normalization clears `u`, parks the modulus in low `s`, and toggles the
active flag; at every operation boundary that flag starts high. -/
theorem normalizeGates_stepList
    (fieldWidth counterWidth p : Nat) (hp : p < 2 ^ fieldWidth)
    (state : Layout.Registers fieldWidth counterWidth)
    (hu : (RegisterRouting.uPort fieldWidth counterWidth).read state =
      modulusWord fieldWidth p hp)
    (hs : (RegisterRouting.sCoefficientPort fieldWidth counterWidth).read
      state = 1) :
    EncodedBit.GateSpec.stepList
        (normalizeGates fieldWidth counterWidth p hp) state =
      (RegisterRouting.activeBit fieldWidth counterWidth).flip
        ((RegisterRouting.sCoefficientPort fieldWidth counterWidth).set
          ((RegisterRouting.uPort fieldWidth counterWidth).set state 0)
          (modulusWord fieldWidth p hp)) := by
  let afterU := (RegisterRouting.uPort fieldWidth counterWidth).set state 0
  let afterS := (RegisterRouting.sCoefficientPort fieldWidth counterWidth).set
    afterU (modulusWord fieldWidth p hp)
  have hclearU :
      EncodedBit.GateSpec.stepList
          (EncodedBit.Word.xorConstantGates
            (RegisterRouting.uWord fieldWidth counterWidth)
            (modulusWord fieldWidth p hp)) state = afterU := by
    change EncodedBit.Word.xorConstantStep
        (RegisterRouting.uPort fieldWidth counterWidth).word
        (modulusWord fieldWidth p hp) state = afterU
    apply xorConstantStep_eq_set_of_testBit
    intro bit
    rw [hu]
    simp [modulusWord]
  have hsAfterU :
      (RegisterRouting.sCoefficientPort fieldWidth counterWidth).read afterU =
        1 := by
    change (RegisterRouting.sCoefficientPort fieldWidth counterWidth).read
      state = 1
    exact hs
  have hloadS :
      EncodedBit.GateSpec.stepList
          (EncodedBit.Word.xorConstantGates
            (RegisterRouting.sCoefficientWord fieldWidth counterWidth)
            (coefficientNormalizationWord fieldWidth p hp)) afterU =
        afterS := by
    change EncodedBit.Word.xorConstantStep
        (RegisterRouting.sCoefficientPort fieldWidth counterWidth).word
        (coefficientNormalizationWord fieldWidth p hp) afterU = afterS
    apply xorConstantStep_eq_set_of_testBit
    intro bit
    rw [hsAfterU]
    simp [modulusWord, coefficientNormalizationWord, Nat.testBit_xor]
  simp only [normalizeGates, EncodedBit.GateSpec.stepList_append]
  rw [hclearU, hloadS]
  rfl

/-- A word-copy ledger is disjoint from an observed bit when both routed
words are. -/
private theorem copyGates_bitDisjoint_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (source target : EncodedBit.Word encoding width)
    (hsourceTarget : ∀ bit,
      (source.bit bit).wire ≠ (target.bit bit).wire)
    (observed : EncodedBit encoding)
    (hsource : ∀ bit, (source.bit bit).wire ≠ observed.wire)
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire) :
    ∀ gate, gate ∈ EncodedBit.Word.xorIntoGates source target
        hsourceTarget →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact ⟨hsource bit, htarget bit⟩

/-- A constant-xor ledger is disjoint from an observed bit when its target
word is. -/
private theorem xorConstantGates_bitDisjoint_of_word_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (target : EncodedBit.Word encoding width)
    (constant : Fin (2 ^ width)) (observed : EncodedBit encoding)
    (htarget : ∀ bit, (target.bit bit).wire ≠ observed.wire) :
    ∀ gate, gate ∈ EncodedBit.Word.xorConstantGates target constant →
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hgate
  rw [EncodedBit.Word.xorConstantGates] at hgate
  rcases List.mem_map.mp hgate with ⟨bit, _hbit, rfl⟩
  exact htarget bit

private theorem liftedArithmeticBit_wire_ne_lambdaBit
    (fieldWidth counterWidth : Nat)
    (inner : EncodedBit (MK.Compact.encoding fieldWidth counterWidth))
    (lambdaBit : Fin fieldWidth) :
    (Layout.liftArithmeticBit fieldWidth counterWidth inner).wire ≠
      (Layout.lambdaBit fieldWidth counterWidth lambdaBit).wire :=
  Ne.symm (Layout.lambdaBit_wire_ne_liftArithmeticBit fieldWidth counterWidth
    lambdaBit inner)

/-- If a computed source is copied to a word untouched by the compute ledger,
the exact reverse ledger leaves the corresponding classical xor on the
original state. -/
private theorem computeCopyUncomputeStep_eq_xorConstant
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (compute : List (EncodedBit.GateSpec encoding))
    (source target : Arithmetic.BlockBank.WordPort encoding width)
    (hsourceTarget : ∀ bit,
      (source.word.bit bit).wire ≠ (target.word.bit bit).wire)
    (hcomputeTarget : ∀ bit gate, gate ∈ compute →
      EncodedBit.GateSpec.bitDisjoint (target.word.bit bit) gate)
    (state computed : Data) (value : Word width)
    (hcomputed : EncodedBit.GateSpec.stepList compute state = computed)
    (hcopy : Arithmetic.BlockBank.WordPort.directCopyStep source target
        hsourceTarget computed =
      EncodedBit.Word.xorConstantStep target.word value computed) :
    EncodedBit.GateSpec.stepList
        (compute ++
          Arithmetic.BlockBank.WordPort.directCopyGates source target
            hsourceTarget ++ compute.reverse) state =
      EncodedBit.Word.xorConstantStep target.word value state := by
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  change EncodedBit.GateSpec.stepList compute.reverse
      (Arithmetic.BlockBank.WordPort.directCopyStep source target
        hsourceTarget
        (EncodedBit.GateSpec.stepList compute state)) = _
  rw [hcomputed, hcopy]
  rw [EncodedBit.Word.stepList_xorConstantStep_comm]
  · congr 1
    rw [← hcomputed,
      EncodedBit.GateSpec.stepList_reverse_stepList]
  · intro bit gate hgate
    exact hcomputeTarget bit gate (List.mem_reverse.mp hgate)

/-- Clean-target specialization of the compute--copy--uncompute seam. -/
private theorem computeCopyUncomputeStep_eq_set_of_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (compute : List (EncodedBit.GateSpec encoding))
    (source target : Arithmetic.BlockBank.WordPort encoding width)
    (hsourceTarget : ∀ bit,
      (source.word.bit bit).wire ≠ (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠
        (source.word.bit sourceBit).wire)
    (hcomputeTarget : ∀ bit gate, gate ∈ compute →
      EncodedBit.GateSpec.bitDisjoint (target.word.bit bit) gate)
    (state computed : Data) (value : Word width)
    (hcomputed : EncodedBit.GateSpec.stepList compute state = computed)
    (hsource : source.read computed = value)
    (htargetComputed : target.read computed = 0)
    (htargetState : target.read state = 0) :
    EncodedBit.GateSpec.stepList
        (compute ++
          Arithmetic.BlockBank.WordPort.directCopyGates source target
            hsourceTarget ++ compute.reverse) state =
      target.set state value := by
  have hcopyPort :
      Arithmetic.BlockBank.WordPort.directCopyStep source target
          hsourceTarget computed = target.set computed value :=
    Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_of_clean
      source target hsourceTarget hcross computed value hsource
        htargetComputed
  have hconstantComputed :
      EncodedBit.Word.xorConstantStep target.word value computed =
        target.set computed value := by
    apply xorConstantStep_eq_set_of_testBit
    intro bit
    rw [htargetComputed]
    simp
  have hsandwich := computeCopyUncomputeStep_eq_xorConstant compute source
    target hsourceTarget hcomputeTarget state computed value hcomputed
      (hcopyPort.trans hconstantComputed.symm)
  rw [hsandwich]
  apply xorConstantStep_eq_set_of_testBit
  intro bit
  rw [htargetState]
  simp

/-- Equal-target specialization: xor-copying the computed word clears the
target and the exact reverse compute restores every other field. -/
private theorem computeCopyUncomputeStep_eq_set_zero_of_equal
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (compute : List (EncodedBit.GateSpec encoding))
    (source target : Arithmetic.BlockBank.WordPort encoding width)
    (hsourceTarget : ∀ bit,
      (source.word.bit bit).wire ≠ (target.word.bit bit).wire)
    (hcross : ∀ sourceBit targetBit,
      (target.word.bit targetBit).wire ≠
        (source.word.bit sourceBit).wire)
    (hcomputeTarget : ∀ bit gate, gate ∈ compute →
      EncodedBit.GateSpec.bitDisjoint (target.word.bit bit) gate)
    (state computed : Data) (value : Word width)
    (hcomputed : EncodedBit.GateSpec.stepList compute state = computed)
    (hsource : source.read computed = value)
    (htargetComputed : target.read computed = value)
    (htargetState : target.read state = value) :
    EncodedBit.GateSpec.stepList
        (compute ++
          Arithmetic.BlockBank.WordPort.directCopyGates source target
            hsourceTarget ++ compute.reverse) state =
      target.set state 0 := by
  have hcopyPort :
      Arithmetic.BlockBank.WordPort.directCopyStep source target
          hsourceTarget computed = target.set computed 0 :=
    Arithmetic.BlockBank.WordPort.directCopyStep_eq_set_zero_of_equal
      source target hsourceTarget hcross computed (hsource.trans
        htargetComputed.symm)
  have hconstantComputed :
      EncodedBit.Word.xorConstantStep target.word value computed =
        target.set computed 0 := by
    apply xorConstantStep_eq_set_of_testBit
    intro bit
    rw [htargetComputed]
    simp
  have hsandwich := computeCopyUncomputeStep_eq_xorConstant compute source
    target hsourceTarget hcomputeTarget state computed value hcomputed
      (hcopyPort.trans hconstantComputed.symm)
  rw [hsandwich]
  apply xorConstantStep_eq_set_of_testBit
  intro bit
  rw [htargetState]
  simp

/-- Save live `x1` and `t0`, clear their physical words, load saved `t0` as
the multiplicand, and normalize the compact arithmetic boundary. -/
def t0IntoLambdaRoutingGates
    (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldWidth counterWidth)) :=
  RegisterRouting.saveXHighGates fieldWidth counterWidth ++
    RegisterRouting.historyHighToXGates fieldWidth counterWidth ++
    RegisterRouting.saveT0LowGates fieldWidth counterWidth ++
    RegisterRouting.historyLowToT0Gates fieldWidth counterWidth ++
    RegisterRouting.historyLowToCoefficientGates fieldWidth counterWidth

/-- The reversible routing prefix saves both live arithmetic words, clears
their original carriers, and loads `t0` into the low coefficient word. -/
theorem t0IntoLambdaRoutingGates_stepList
    (fieldWidth counterWidth : Nat)
    (control : Bool) (mutableY «λ» : Word fieldWidth)
    (p mutableX t0 : Word fieldWidth) :
    let initial := cleanState fieldWidth counterWidth control mutableY «λ»
      p mutableX t0
    let savedX := (RegisterRouting.historyHighPort fieldWidth counterWidth).set
      initial mutableX
    let clearedX := (RegisterRouting.mutableXPort fieldWidth counterWidth).set
      savedX 0
    let savedT0 := (RegisterRouting.historyLowPort fieldWidth counterWidth).set
      clearedX t0
    let clearedT0 := (RegisterRouting.t0Port fieldWidth counterWidth).set
      savedT0 0
    EncodedBit.GateSpec.stepList
        (t0IntoLambdaRoutingGates fieldWidth counterWidth) initial =
      (RegisterRouting.rCoefficientPort fieldWidth counterWidth).set
        clearedT0 t0 := by
  let initial := cleanState fieldWidth counterWidth control mutableY «λ»
    p mutableX t0
  let savedX := (RegisterRouting.historyHighPort fieldWidth counterWidth).set
    initial mutableX
  let clearedX := (RegisterRouting.mutableXPort fieldWidth counterWidth).set
    savedX 0
  let savedT0 := (RegisterRouting.historyLowPort fieldWidth counterWidth).set
    clearedX t0
  let clearedT0 := (RegisterRouting.t0Port fieldWidth counterWidth).set
    savedT0 0
  have hsaveX :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveXHighGates fieldWidth counterWidth) initial =
        savedX := by
    simpa only [RegisterRouting.saveXHighGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldWidth counterWidth
        (RegisterRouting.mutableXPort fieldWidth counterWidth)
        (RegisterRouting.historyHighPort fieldWidth counterWidth)
        (fun bit => RegisterRouting.mutableX_history_ne fieldWidth counterWidth
          bit ⟨fieldWidth + bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.mutableX_history_ne fieldWidth counterWidth
            sourceBit ⟨fieldWidth + targetBit.val, by omega⟩))
        initial mutableX (by rfl)
        (by simp [initial, cleanState, RegisterRouting.historyHighPort])
  have hclearX :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyHighToXGates fieldWidth counterWidth) savedX =
        clearedX := by
    simpa only [RegisterRouting.historyHighToXGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldWidth counterWidth
        (RegisterRouting.historyHighPort fieldWidth counterWidth)
        (RegisterRouting.mutableXPort fieldWidth counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.mutableX_history_ne fieldWidth counterWidth bit
            ⟨fieldWidth + bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.mutableX_history_ne fieldWidth counterWidth
            targetBit ⟨fieldWidth + sourceBit.val, by omega⟩)
        savedX (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hsaveT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldWidth counterWidth) clearedX =
        savedT0 := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldWidth counterWidth
        (RegisterRouting.t0Port fieldWidth counterWidth)
        (RegisterRouting.historyLowPort fieldWidth counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldWidth counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldWidth counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        clearedX t0 (by rfl)
        (by
          change (RegisterRouting.historyLowPort fieldWidth counterWidth).read
            savedX = 0
          rw [RegisterRouting.historyLowPort_read_historyHighPort_set]
          simp [initial, cleanState, RegisterRouting.historyLowPort])
  have hclearT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyLowToT0Gates fieldWidth counterWidth) savedT0 =
        clearedT0 := by
    simpa only [RegisterRouting.historyLowToT0Gates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldWidth counterWidth
        (RegisterRouting.historyLowPort fieldWidth counterWidth)
        (RegisterRouting.t0Port fieldWidth counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.t0_history_ne fieldWidth counterWidth bit
            ⟨bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.t0_history_ne fieldWidth counterWidth targetBit
            ⟨sourceBit.val, by omega⟩)
        savedT0 (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hloadCoefficient :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyLowToCoefficientGates fieldWidth
            counterWidth) clearedT0 =
        (RegisterRouting.rCoefficientPort fieldWidth counterWidth).set
          clearedT0 t0 := by
    simpa only [RegisterRouting.historyLowToCoefficientGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldWidth counterWidth
        (RegisterRouting.historyLowPort fieldWidth counterWidth)
        (RegisterRouting.rCoefficientPort fieldWidth counterWidth)
        (fun bit => RegisterRouting.history_rCoefficient_ne fieldWidth
          counterWidth ⟨bit.val, by omega⟩ bit)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.history_rCoefficient_ne fieldWidth counterWidth
            ⟨sourceBit.val, by omega⟩ targetBit))
        clearedT0 t0
        (by
          change (RegisterRouting.historyLowPort fieldWidth counterWidth).read
            savedT0 = t0
          rw [Arithmetic.BlockBank.WordPort.read_set])
        (by
          change (RegisterRouting.rCoefficientPort fieldWidth counterWidth).read
            initial = 0
          simp [initial, cleanState, RegisterRouting.rCoefficientPort,
            MK.initialRegisters])
  simp only [t0IntoLambdaRoutingGates,
    EncodedBit.GateSpec.stepList_append]
  rw [hsaveX, hclearX, hsaveT0, hclearT0, hloadCoefficient]

def t0IntoLambdaPrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  t0IntoLambdaRoutingGates fieldTail.succ counterWidth ++
    normalizeGates fieldTail.succ counterWidth p hp

/-- The complete prefix reaches the exact certified multiplication boundary:
`mutableY` is the multiplier, saved `t0` is the coefficient, and the public
target is clean. -/
theorem t0IntoLambdaPrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» : Word fieldTail.succ)
    (mutableX t0 : Word fieldTail.succ) :
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      «λ» ⟨p, hp⟩ mutableX t0
    let savedX :=
      (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
        initial mutableX
    let clearedX :=
      (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
    let savedT0 :=
      (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
        clearedX t0
    EncodedBit.GateSpec.stepList
        (t0IntoLambdaPrefixGates fieldTail counterWidth p hp) initial =
      MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
        savedT0 (CompactCorrection.widenFixedWord fieldTail.succ t0) 0 := by
  let initial := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX t0
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      initial mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      clearedX t0
  let clearedT0 :=
    (RegisterRouting.t0Port fieldTail.succ counterWidth).set savedT0 0
  let routed :=
    (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
      clearedT0 t0
  have hrouted :
      EncodedBit.GateSpec.stepList
          (t0IntoLambdaRoutingGates fieldTail.succ counterWidth) initial =
        routed := by
    exact t0IntoLambdaRoutingGates_stepList fieldTail.succ counterWidth control
      mutableY «λ» ⟨p, hp⟩ mutableX t0
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read routed =
        modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        routed = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, cleanState, RegisterRouting.sCoefficientPort,
      MK.initialRegisters]
  have hnormalized := normalizeGates_stepList fieldTail.succ counterWidth p hp
    routed hu hs
  change EncodedBit.GateSpec.stepList
      (t0IntoLambdaRoutingGates fieldTail.succ counterWidth ++
        normalizeGates fieldTail.succ counterWidth p hp) initial = _
  rw [EncodedBit.GateSpec.stepList_append, hrouted, hnormalized]
  simp [routed, clearedT0, savedT0, clearedX, savedX, initial, cleanState,
    RegisterRouting.activeBit_flip, RegisterRouting.uPort,
    RegisterRouting.t0Port, RegisterRouting.mutableXPort,
    MontgomeryMultiplication.multiplicationState,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork, modulusWord]

/-- The seed normalization ledger is entirely inside the compact arithmetic
carrier and is therefore disjoint from every persistent-slope bit. -/
theorem normalizeGates_bitDisjoint_lambdaBit
    (fieldWidth counterWidth p : Nat) (hp : p < 2 ^ fieldWidth)
    (bit : Fin fieldWidth) :
    ∀ gate, gate ∈ normalizeGates fieldWidth counterWidth p hp →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldWidth counterWidth bit) gate := by
  intro gate hgate
  simp only [normalizeGates, List.mem_append, List.mem_singleton] at hgate
  rcases hgate with (hu | hs) | hactive
  · exact xorConstantGates_bitDisjoint_of_word_ne
      (RegisterRouting.uWord fieldWidth counterWidth)
      (modulusWord fieldWidth p hp)
      (Layout.lambdaBit fieldWidth counterWidth bit)
      (fun source => by
        simpa [RegisterRouting.uWord, Layout.liftArithmeticWord] using
          liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
            ((MK.Compact.uValueWord fieldWidth counterWidth).bit source) bit)
      gate hu
  · exact xorConstantGates_bitDisjoint_of_word_ne
      (RegisterRouting.sCoefficientWord fieldWidth counterWidth)
      (coefficientNormalizationWord fieldWidth p hp)
      (Layout.lambdaBit fieldWidth counterWidth bit)
      (fun source => by
        simpa [RegisterRouting.sCoefficientWord,
          Layout.liftArithmeticWord] using
          liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
            ((MK.Compact.sCoeffValueWord fieldWidth counterWidth).bit
              (Fin.castSucc source)) bit)
      gate hs
  · subst gate
    change (RegisterRouting.activeBit fieldWidth counterWidth).wire ≠
      (Layout.lambdaBit fieldWidth counterWidth bit).wire
    simpa [RegisterRouting.activeBit] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        (MK.Compact.activeBit fieldWidth counterWidth) bit

/-- Saving/routing the two live words never reads or writes `lambda`. -/
theorem t0IntoLambdaRoutingGates_bitDisjoint_lambdaBit
    (fieldWidth counterWidth : Nat) (bit : Fin fieldWidth) :
    ∀ gate, gate ∈ t0IntoLambdaRoutingGates fieldWidth counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldWidth counterWidth bit) gate := by
  let observed := Layout.lambdaBit fieldWidth counterWidth bit
  have hx : ∀ source,
      ((RegisterRouting.mutableXPort fieldWidth counterWidth).word.bit
        source).wire ≠ observed.wire := by
    intro source
    simpa [observed, RegisterRouting.mutableXPort, Layout.mutableXWord,
      Layout.liftArithmeticWord] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        ((MK.Compact.vValueWord fieldWidth counterWidth).bit source) bit
  have ht0 : ∀ source,
      ((RegisterRouting.t0Port fieldWidth counterWidth).word.bit source).wire ≠
        observed.wire := by
    intro source
    simpa [observed, RegisterRouting.t0Port, Layout.t0Word,
      Layout.liftArithmeticWord] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        ((MK.Compact.targetValueWord fieldWidth counterWidth).bit source) bit
  have hlow : ∀ source,
      ((RegisterRouting.historyLowPort fieldWidth counterWidth).word.bit
        source).wire ≠ observed.wire := by
    intro source
    simpa [observed, RegisterRouting.historyLowPort,
      RegisterRouting.historyLowWord, RegisterRouting.historyValueBit] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        (MK.Compact.liftCoreBit fieldWidth counterWidth
          (MK.RegisterBits.historyBit fieldWidth counterWidth
            (WireAddress.littleEndianWire
              ⟨source.val, by omega⟩))) bit
  have hhigh : ∀ source,
      ((RegisterRouting.historyHighPort fieldWidth counterWidth).word.bit
        source).wire ≠ observed.wire := by
    intro source
    simpa [observed, RegisterRouting.historyHighPort,
      RegisterRouting.historyHighWord, RegisterRouting.historyValueBit] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        (MK.Compact.liftCoreBit fieldWidth counterWidth
          (MK.RegisterBits.historyBit fieldWidth counterWidth
            (WireAddress.littleEndianWire
              ⟨fieldWidth + source.val, by omega⟩))) bit
  have hr : ∀ source,
      ((RegisterRouting.rCoefficientPort fieldWidth counterWidth).word.bit
        source).wire ≠ observed.wire := by
    intro source
    simpa [observed, RegisterRouting.rCoefficientPort,
      RegisterRouting.rCoefficientWord, Layout.liftArithmeticWord] using
      liftedArithmeticBit_wire_ne_lambdaBit fieldWidth counterWidth
        ((CompactCorrection.correctedValueWord fieldWidth counterWidth).bit
          source) bit
  intro gate hgate
  simp only [t0IntoLambdaRoutingGates,
    RegisterRouting.saveXHighGates,
    RegisterRouting.historyHighToXGates,
    RegisterRouting.saveT0LowGates,
    RegisterRouting.historyLowToT0Gates,
    RegisterRouting.historyLowToCoefficientGates,
    RegisterRouting.copyGates, List.mem_append] at hgate
  rcases hgate with (((hsaveX | hclearX) | hsaveT0) | hclearT0) | hload
  · exact copyGates_bitDisjoint_of_word_ne _ _ _ observed hx hhigh gate
      hsaveX
  · exact copyGates_bitDisjoint_of_word_ne _ _ _ observed hhigh hx gate
      hclearX
  · exact copyGates_bitDisjoint_of_word_ne _ _ _ observed ht0 hlow gate
      hsaveT0
  · exact copyGates_bitDisjoint_of_word_ne _ _ _ observed hlow ht0 gate
      hclearT0
  · exact copyGates_bitDisjoint_of_word_ne _ _ _ observed hlow hr gate
      hload

/-- The full prefix is disjoint from persistent `lambda`. -/
theorem t0IntoLambdaPrefixGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (bit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ t0IntoLambdaPrefixGates fieldTail counterWidth p hp →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth bit) gate := by
  intro gate hgate
  rcases List.mem_append.mp hgate with hrouting | hnormalize
  · exact t0IntoLambdaRoutingGates_bitDisjoint_lambdaBit fieldTail.succ
      counterWidth bit gate hrouting
  · exact normalizeGates_bitDisjoint_lambdaBit fieldTail.succ counterWidth p
      hp bit gate hnormalize

/-- Out-of-place `lambda ^= mutableY * t0 * R^-1`.  This is the physical
operation used at Algorithm 1's steps 4 and 13
[RNSL17, ECDLP.tex:517,526]. -/
def t0IntoLambdaGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := t0IntoLambdaPrefixGates fieldTail counterWidth p hp
  let product := MontgomeryMultiplication.gates fieldTail counterWidth p
  let compute := prep ++ product
  compute ++
    RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
    compute.reverse

/-- Compiled out-of-place `t0`-by-`y` multiplication program. -/
def t0IntoLambdaProgram
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Layout.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList
    (QubitLayout.canonical _) .empty
    (t0IntoLambdaGates fieldTail counterWidth p hp)

/-- Folded action of the out-of-place `t0`-by-`y` multiplication ledger. -/
def t0IntoLambdaStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (t0IntoLambdaGates fieldTail counterWidth p hp)

theorem t0IntoLambda_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (t0IntoLambdaProgram fieldTail counterWidth p hp)
      (t0IntoLambdaStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList
    (QubitLayout.canonical _) .empty
    (t0IntoLambdaGates fieldTail counterWidth p hp)

set_option maxHeartbeats 1200000 in
-- The proof specializes the complete multiplication sandwich once.
/-- Clean-target endpoint for Algorithm 1, step 4 [RNSL17, ECDLP.tex:517].
The complete physical sandwich restores every saved arithmetic field and
writes exactly one Montgomery product to `lambda`. -/
theorem t0IntoLambdaStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY mutableX t0 : Word fieldTail.succ)
    (ht0 : t0.val < p) :
    let initial := cleanState fieldTail.succ counterWidth control mutableY 0
      ⟨p, hp⟩ mutableX t0
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ t0
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      mutableY (List.finRange fieldTail.succ) residues).target
    t0IntoLambdaStep fieldTail counterWidth p hp initial =
        (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set
          initial product ∧
      (product.val : ZMod p) =
        (mutableY.val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * (t0.val : ZMod p) := by
  let initial := cleanState fieldTail.succ counterWidth control mutableY 0
    ⟨p, hp⟩ mutableX t0
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      initial mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      clearedX t0
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ t0
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    mutableY (List.finRange fieldTail.succ) residues).target
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ t0).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact ht0
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by
    change initial.arithmetic.shared.path = false
    rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (t0IntoLambdaPrefixGates fieldTail counterWidth p hp) initial =
        MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
          savedT0 coefficient 0 := by
    exact t0IntoLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY 0 mutableX t0
  have hmultiply := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiply
  rcases hmultiply with ⟨hmultiply, hproduct⟩
  have hcomputed :
      EncodedBit.GateSpec.stepList
          (t0IntoLambdaPrefixGates fieldTail counterWidth p hp ++
            MontgomeryMultiplication.gates fieldTail counterWidth p) initial =
        MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
          savedT0 coefficient product := by
    rw [EncodedBit.GateSpec.stepList_append, hprefix]
    exact hmultiply
  let compute := t0IntoLambdaPrefixGates fieldTail counterWidth p hp ++
    MontgomeryMultiplication.gates fieldTail counterWidth p
  have hcomputeLambda : ∀ bit gate, gate ∈ compute →
      EncodedBit.GateSpec.bitDisjoint
        ((RegisterRouting.lambdaPort fieldTail.succ counterWidth).word.bit bit)
        gate := by
    intro bit gate hgate
    rcases List.mem_append.mp hgate with hprep | hproductGate
    · simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
        t0IntoLambdaPrefixGates_bitDisjoint_lambdaBit fieldTail counterWidth p
          hp bit gate hprep
    · simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
        MontgomeryMultiplication.gates_bitDisjoint_lambdaBit fieldTail
          counterWidth p bit gate hproductGate
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  have hsource :
      (RegisterRouting.t0Port fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetComputed :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read computed =
        0 := by
    rfl
  have htargetInitial :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read initial =
        0 := by
    rfl
  have hsandwich := computeCopyUncomputeStep_eq_set_of_clean compute
    (RegisterRouting.t0Port fieldTail.succ counterWidth)
    (RegisterRouting.lambdaPort fieldTail.succ counterWidth)
    (fun bit => Ne.symm
      (RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth bit bit))
    (fun sourceBit targetBit =>
      RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth targetBit
        sourceBit)
    hcomputeLambda initial computed product hcomputed hsource htargetComputed
      htargetInitial
  constructor
  · simpa [t0IntoLambdaStep, t0IntoLambdaGates, compute,
      RegisterRouting.t0ToLambdaGates, RegisterRouting.copyGates,
      Arithmetic.BlockBank.WordPort.directCopyGates] using hsandwich
  · have hsavedY : savedT0.mutableY = mutableY := by rfl
    rw [hsavedY] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

set_option maxHeartbeats 1200000 in
-- The proof reuses the same multiplication sandwich with an equal xor target.
/-- Equal-target endpoint for Algorithm 1, step 13 [RNSL17, ECDLP.tex:526].
When `lambda` already holds the Montgomery product, the same physical xor
multiplication clears it while restoring every saved arithmetic field. -/
theorem t0IntoLambdaStep_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY mutableX t0 : Word fieldTail.succ)
    (ht0 : t0.val < p) :
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ t0
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      mutableY (List.finRange fieldTail.succ) residues).target
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      product ⟨p, hp⟩ mutableX t0
    t0IntoLambdaStep fieldTail counterWidth p hp initial =
        (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set initial 0 ∧
      (product.val : ZMod p) =
        (mutableY.val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * (t0.val : ZMod p) := by
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ t0
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    mutableY (List.finRange fieldTail.succ) residues).target
  let initial := cleanState fieldTail.succ counterWidth control mutableY product
    ⟨p, hp⟩ mutableX t0
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      initial mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      clearedX t0
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ t0).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact ht0
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by
    change initial.arithmetic.shared.path = false
    rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (t0IntoLambdaPrefixGates fieldTail counterWidth p hp) initial =
        MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
          savedT0 coefficient 0 := by
    exact t0IntoLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY product mutableX t0
  have hmultiply := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiply
  rcases hmultiply with ⟨hmultiply, hproduct⟩
  have hcomputed :
      EncodedBit.GateSpec.stepList
          (t0IntoLambdaPrefixGates fieldTail counterWidth p hp ++
            MontgomeryMultiplication.gates fieldTail counterWidth p) initial =
        MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
          savedT0 coefficient product := by
    rw [EncodedBit.GateSpec.stepList_append, hprefix]
    exact hmultiply
  let compute := t0IntoLambdaPrefixGates fieldTail counterWidth p hp ++
    MontgomeryMultiplication.gates fieldTail counterWidth p
  have hcomputeLambda : ∀ bit gate, gate ∈ compute →
      EncodedBit.GateSpec.bitDisjoint
        ((RegisterRouting.lambdaPort fieldTail.succ counterWidth).word.bit bit)
        gate := by
    intro bit gate hgate
    rcases List.mem_append.mp hgate with hprep | hproductGate
    · simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
        t0IntoLambdaPrefixGates_bitDisjoint_lambdaBit fieldTail counterWidth p
          hp bit gate hprep
    · simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
        MontgomeryMultiplication.gates_bitDisjoint_lambdaBit fieldTail
          counterWidth p bit gate hproductGate
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  have hsource :
      (RegisterRouting.t0Port fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetComputed :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetInitial :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read initial =
        product := by
    rfl
  have hsandwich := computeCopyUncomputeStep_eq_set_zero_of_equal compute
    (RegisterRouting.t0Port fieldTail.succ counterWidth)
    (RegisterRouting.lambdaPort fieldTail.succ counterWidth)
    (fun bit => Ne.symm
      (RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth bit bit))
    (fun sourceBit targetBit =>
      RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth targetBit
        sourceBit)
    hcomputeLambda initial computed product hcomputed hsource htargetComputed
      htargetInitial
  constructor
  · simpa [t0IntoLambdaStep, t0IntoLambdaGates, compute,
      RegisterRouting.t0ToLambdaGates, RegisterRouting.copyGates,
      Arithmetic.BlockBank.WordPort.directCopyGates] using hsandwich
  · have hsavedY : savedT0.mutableY = mutableY := by rfl
    rw [hsavedY] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

/-- Route `lambda` into the multiplier port, preserve live `t0`, move mutable
`x1` into the coefficient word, and normalize the compact boundary. -/
def xIntoYPrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  RegisterRouting.swapYLambdaGates fieldTail.succ counterWidth ++
    RegisterRouting.saveT0LowGates fieldTail.succ counterWidth ++
    RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth ++
    RegisterRouting.xToCoefficientGates fieldTail.succ counterWidth ++
    RegisterRouting.coefficientToXGates fieldTail.succ counterWidth ++
    normalizeGates fieldTail.succ counterWidth p hp

/-- The `xIntoY` prefix swaps the persistent words, saves `t0`, and reaches
the certified multiplication boundary with original `x1` as coefficient. -/
theorem xIntoYPrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      «λ» ⟨p, hp⟩ mutableX t0
    let swapped := { initial with mutableY := «λ», «λ» := mutableY }
    let savedT0 :=
      (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
        swapped t0
    EncodedBit.GateSpec.stepList
        (xIntoYPrefixGates fieldTail counterWidth p hp) initial =
      MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
        savedT0 (CompactCorrection.widenFixedWord fieldTail.succ mutableX) 0 := by
  let initial := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX t0
  let swapped := { initial with mutableY := «λ», «λ» := mutableY }
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set swapped t0
  let clearedT0 :=
    (RegisterRouting.t0Port fieldTail.succ counterWidth).set savedT0 0
  let loadedCoefficient :=
    (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
      clearedT0 mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set
      loadedCoefficient 0
  have hswap :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.swapYLambdaGates fieldTail.succ counterWidth)
          initial = swapped := by
    exact RegisterRouting.swapYLambdaGates_stepList fieldTail.succ counterWidth
      initial
  have hsaveT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldTail.succ counterWidth) swapped =
        savedT0 := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        swapped t0 (by rfl)
        (by
          simp [swapped, initial, cleanState, RegisterRouting.historyLowPort,
            MK.initialRegisters])
  have hclearT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth)
          savedT0 = clearedT0 := by
    simpa only [RegisterRouting.historyLowToT0Gates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
            ⟨bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.t0_history_ne fieldTail.succ counterWidth targetBit
            ⟨sourceBit.val, by omega⟩)
        savedT0 (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hloadCoefficient :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.xToCoefficientGates fieldTail.succ counterWidth)
          clearedT0 = loadedCoefficient := by
    simpa only [RegisterRouting.xToCoefficientGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ
          counterWidth bit bit)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            sourceBit targetBit))
        clearedT0 mutableX (by rfl)
        (by
          change (RegisterRouting.rCoefficientPort fieldTail.succ
            counterWidth).read initial = 0
          simp [initial, cleanState, RegisterRouting.rCoefficientPort,
            MK.initialRegisters])
  have hclearX :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.coefficientToXGates fieldTail.succ counterWidth)
          loadedCoefficient = clearedX := by
    simpa only [RegisterRouting.coefficientToXGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            bit bit))
        (fun sourceBit targetBit =>
          RegisterRouting.mutableX_rCoefficient_ne fieldTail.succ counterWidth
            targetBit sourceBit)
        loadedCoefficient (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read clearedX =
        modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        clearedX = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, cleanState, RegisterRouting.sCoefficientPort,
      MK.initialRegisters]
  have hnormalized := normalizeGates_stepList fieldTail.succ counterWidth p hp
    clearedX hu hs
  simp only [xIntoYPrefixGates, EncodedBit.GateSpec.stepList_append]
  rw [hswap, hsaveT0, hclearT0, hloadCoefficient, hclearX, hnormalized]
  simp [clearedX, loadedCoefficient, clearedT0, savedT0, swapped, initial,
    cleanState, RegisterRouting.activeBit_flip, RegisterRouting.uPort,
    RegisterRouting.sCoefficientPort_set, RegisterRouting.mutableXPort,
    RegisterRouting.rCoefficientPort_set, RegisterRouting.t0Port,
    MontgomeryMultiplication.multiplicationState,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork, modulusWord]

/-- Out-of-place `mutableY ^= lambda * mutableX * R^-1`.  The leading and
trailing swaps let the sole multiplier port serve `lambda` while returning
both public point words to their original positions. -/
def xIntoYGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := xIntoYPrefixGates fieldTail counterWidth p hp
  let product := MontgomeryMultiplication.gates fieldTail counterWidth p
  prep ++ product ++
    RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
    product.reverse ++ prep.reverse

def xIntoYProgram
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Layout.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList
    (QubitLayout.canonical _) .empty
    (xIntoYGates fieldTail counterWidth p hp)

def xIntoYStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (xIntoYGates fieldTail counterWidth p hp)

theorem xIntoY_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (xIntoYProgram fieldTail counterWidth p hp)
      (xIntoYStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList
    (QubitLayout.canonical _) .empty
    (xIntoYGates fieldTail counterWidth p hp)

set_option maxHeartbeats 1200000 in
-- The proof identifies the post-copy boundary with the same prefix applied
-- to the updated public input, then cancels that prefix exactly.
/-- Clean-target endpoint for Algorithm 1, step 11 [RNSL17, ECDLP.tex:524].
The complete reversible sandwich writes the Montgomery product to mutable
`y1` and restores every other field, including `lambda`, `x1`, `t0`, and the
shared history. -/
theorem xIntoYStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) («λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ mutableX
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      «λ» (List.finRange fieldTail.succ) residues).target
    let initial := cleanState fieldTail.succ counterWidth control 0 «λ»
      ⟨p, hp⟩ mutableX t0
    xIntoYStep fieldTail counterWidth p hp initial =
        (RegisterRouting.mutableYPort fieldTail.succ counterWidth).set
          initial product ∧
      (product.val : ZMod p) =
        («λ».val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * (mutableX.val : ZMod p) := by
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ mutableX
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    «λ» (List.finRange fieldTail.succ) residues).target
  let initial := cleanState fieldTail.succ counterWidth control 0 «λ»
    ⟨p, hp⟩ mutableX t0
  let swapped := { initial with mutableY := «λ», «λ» := 0 }
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set swapped t0
  let prefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient 0
  let output := cleanState fieldTail.succ counterWidth control product «λ»
    ⟨p, hp⟩ mutableX t0
  let outputSwapped :=
    { output with mutableY := «λ», «λ» := product }
  let outputSavedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      outputSwapped t0
  let outputPrefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient 0
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ mutableX).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact hx
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by
    rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (xIntoYPrefixGates fieldTail counterWidth p hp) initial =
        prefixState := by
    exact xIntoYPrefixGates_stepList fieldTail counterWidth p hp control 0
      «λ» mutableX t0
  have houtputPrefix :
      EncodedBit.GateSpec.stepList
          (xIntoYPrefixGates fieldTail counterWidth p hp) output =
        outputPrefixState := by
    exact xIntoYPrefixGates_stepList fieldTail counterWidth p hp control product
      «λ» mutableX t0
  have hmultiply := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiply
  rcases hmultiply with ⟨hmultiply, hproduct⟩
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  have hsource :
      (RegisterRouting.t0Port fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetComputed :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read computed =
        0 := by
    rfl
  have htargetPrefix :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read
        prefixState = 0 := by
    rfl
  have hcomputeLambda : ∀ bit gate,
      gate ∈ MontgomeryMultiplication.gates fieldTail counterWidth p →
        EncodedBit.GateSpec.bitDisjoint
          ((RegisterRouting.lambdaPort fieldTail.succ counterWidth).word.bit bit)
          gate := by
    intro bit gate hgate
    simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
      MontgomeryMultiplication.gates_bitDisjoint_lambdaBit fieldTail
        counterWidth p bit gate hgate
  have hinner := computeCopyUncomputeStep_eq_set_of_clean
    (MontgomeryMultiplication.gates fieldTail counterWidth p)
    (RegisterRouting.t0Port fieldTail.succ counterWidth)
    (RegisterRouting.lambdaPort fieldTail.succ counterWidth)
    (fun bit => Ne.symm
      (RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth bit bit))
    (fun sourceBit targetBit =>
      RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth targetBit
        sourceBit)
    hcomputeLambda prefixState computed product hmultiply hsource
      htargetComputed htargetPrefix
  have hboundary :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set
          prefixState product = outputPrefixState := by
    rfl
  have hinnerCombined :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p ++
            (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
              (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse))
          prefixState =
        (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set
          prefixState product := by
    simpa [List.append_assoc, RegisterRouting.t0ToLambdaGates,
      RegisterRouting.copyGates,
      Arithmetic.BlockBank.WordPort.directCopyGates] using hinner
  constructor
  · simp only [xIntoYStep, xIntoYGates,
      EncodedBit.GateSpec.stepList_append]
    rw [hprefix]
    rw [← EncodedBit.GateSpec.stepList_append
      (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth)
      (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse]
    rw [← EncodedBit.GateSpec.stepList_append
      (MontgomeryMultiplication.gates fieldTail counterWidth p)
      (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
        (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse)]
    rw [hinnerCombined]
    rw [hboundary, ← houtputPrefix,
      EncodedBit.GateSpec.stepList_reverse_stepList]
    rfl
  · have hsavedMultiplier : savedT0.mutableY = «λ» := by rfl
    rw [hsavedMultiplier] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

set_option maxHeartbeats 1200000 in
-- The equal-target proof uses the same updated-input cancellation argument.
/-- Equal-target endpoint for Algorithm 1, step 5 [RNSL17, ECDLP.tex:518].
If mutable `y1` already equals the Montgomery product, the xor multiplication
clears it and restores the complete remaining carrier. -/
theorem xIntoYStep_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) («λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ mutableX
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      «λ» (List.finRange fieldTail.succ) residues).target
    let initial := cleanState fieldTail.succ counterWidth control product «λ»
      ⟨p, hp⟩ mutableX t0
    xIntoYStep fieldTail counterWidth p hp initial =
        (RegisterRouting.mutableYPort fieldTail.succ counterWidth).set
          initial 0 ∧
      (product.val : ZMod p) =
        («λ».val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * (mutableX.val : ZMod p) := by
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ mutableX
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    «λ» (List.finRange fieldTail.succ) residues).target
  let initial := cleanState fieldTail.succ counterWidth control product «λ»
    ⟨p, hp⟩ mutableX t0
  let swapped := { initial with mutableY := «λ», «λ» := product }
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set swapped t0
  let prefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient 0
  let output := cleanState fieldTail.succ counterWidth control 0 «λ»
    ⟨p, hp⟩ mutableX t0
  let outputSwapped := { output with mutableY := «λ», «λ» := 0 }
  let outputSavedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      outputSwapped t0
  let outputPrefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient 0
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ mutableX).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact hx
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by
    rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (xIntoYPrefixGates fieldTail counterWidth p hp) initial =
        prefixState := by
    exact xIntoYPrefixGates_stepList fieldTail counterWidth p hp control product
      «λ» mutableX t0
  have houtputPrefix :
      EncodedBit.GateSpec.stepList
          (xIntoYPrefixGates fieldTail counterWidth p hp) output =
        outputPrefixState := by
    exact xIntoYPrefixGates_stepList fieldTail counterWidth p hp control 0
      «λ» mutableX t0
  have hmultiply := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiply
  rcases hmultiply with ⟨hmultiply, hproduct⟩
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  have hsource :
      (RegisterRouting.t0Port fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetComputed :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read computed =
        product := by
    rfl
  have htargetPrefix :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).read
        prefixState = product := by
    rfl
  have hcomputeLambda : ∀ bit gate,
      gate ∈ MontgomeryMultiplication.gates fieldTail counterWidth p →
        EncodedBit.GateSpec.bitDisjoint
          ((RegisterRouting.lambdaPort fieldTail.succ counterWidth).word.bit bit)
          gate := by
    intro bit gate hgate
    simpa only [RegisterRouting.lambdaPort, Layout.lambdaWord] using
      MontgomeryMultiplication.gates_bitDisjoint_lambdaBit fieldTail
        counterWidth p bit gate hgate
  have hinner := computeCopyUncomputeStep_eq_set_zero_of_equal
    (MontgomeryMultiplication.gates fieldTail counterWidth p)
    (RegisterRouting.t0Port fieldTail.succ counterWidth)
    (RegisterRouting.lambdaPort fieldTail.succ counterWidth)
    (fun bit => Ne.symm
      (RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth bit bit))
    (fun sourceBit targetBit =>
      RegisterRouting.lambda_t0_ne fieldTail.succ counterWidth targetBit
        sourceBit)
    hcomputeLambda prefixState computed product hmultiply hsource
      htargetComputed htargetPrefix
  have hboundary :
      (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set
          prefixState 0 = outputPrefixState := by
    rfl
  have hinnerCombined :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p ++
            (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
              (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse))
          prefixState =
        (RegisterRouting.lambdaPort fieldTail.succ counterWidth).set
          prefixState 0 := by
    simpa [List.append_assoc, RegisterRouting.t0ToLambdaGates,
      RegisterRouting.copyGates,
      Arithmetic.BlockBank.WordPort.directCopyGates] using hinner
  constructor
  · simp only [xIntoYStep, xIntoYGates,
      EncodedBit.GateSpec.stepList_append]
    rw [hprefix]
    rw [← EncodedBit.GateSpec.stepList_append
      (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth)
      (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse]
    rw [← EncodedBit.GateSpec.stepList_append
      (MontgomeryMultiplication.gates fieldTail counterWidth p)
      (RegisterRouting.t0ToLambdaGates fieldTail.succ counterWidth ++
        (MontgomeryMultiplication.gates fieldTail counterWidth p).reverse)]
    rw [hinnerCombined]
    rw [hboundary, ← houtputPrefix,
      EncodedBit.GateSpec.stepList_reverse_stepList]
    rfl
  · have hsavedMultiplier : savedT0.mutableY = «λ» := by rfl
    rw [hsavedMultiplier] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

/-- Route `lambda` into both multiplication inputs, preserve live `x1`, save
the previous `t0`, and normalize the compact arithmetic boundary. -/
def squareLambdaPrefixGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  RegisterRouting.swapYLambdaGates fieldTail.succ counterWidth ++
    RegisterRouting.saveXHighGates fieldTail.succ counterWidth ++
    RegisterRouting.historyHighToXGates fieldTail.succ counterWidth ++
    RegisterRouting.saveT0LowGates fieldTail.succ counterWidth ++
    RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth ++
    RegisterRouting.yToCoefficientGates fieldTail.succ counterWidth ++
    normalizeGates fieldTail.succ counterWidth p hp

/-- The squaring prefix routes `lambda` to the multiplier and coefficient,
saves the two borrowed arithmetic words in the existing history halves, and
reaches the certified multiplication boundary. -/
theorem squareLambdaPrefixGates_stepList
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ) :
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      «λ» ⟨p, hp⟩ mutableX t0
    let swapped := { initial with mutableY := «λ», «λ» := mutableY }
    let savedX :=
      (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
        swapped mutableX
    let clearedX :=
      (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
    let savedT0 :=
      (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
        clearedX t0
    EncodedBit.GateSpec.stepList
        (squareLambdaPrefixGates fieldTail counterWidth p hp) initial =
      MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
        savedT0 (CompactCorrection.widenFixedWord fieldTail.succ «λ») 0 := by
  let initial := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX t0
  let swapped := { initial with mutableY := «λ», «λ» := mutableY }
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      swapped mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      clearedX t0
  let clearedT0 :=
    (RegisterRouting.t0Port fieldTail.succ counterWidth).set savedT0 0
  let loadedCoefficient :=
    (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth).set
      clearedT0 «λ»
  have hswap :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.swapYLambdaGates fieldTail.succ counterWidth)
          initial = swapped := by
    exact RegisterRouting.swapYLambdaGates_stepList fieldTail.succ counterWidth
      initial
  have hsaveX :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveXHighGates fieldTail.succ counterWidth) swapped =
        savedX := by
    simpa only [RegisterRouting.saveXHighGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (RegisterRouting.historyHighPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.mutableX_history_ne fieldTail.succ
          counterWidth bit ⟨fieldTail.succ + bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.mutableX_history_ne fieldTail.succ counterWidth
            sourceBit ⟨fieldTail.succ + targetBit.val, by omega⟩))
        swapped mutableX (by rfl)
        (by
          simp [swapped, initial, cleanState, RegisterRouting.historyHighPort,
            MK.initialRegisters])
  have hclearX :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyHighToXGates fieldTail.succ counterWidth)
          savedX = clearedX := by
    simpa only [RegisterRouting.historyHighToXGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.historyHighPort fieldTail.succ counterWidth)
        (RegisterRouting.mutableXPort fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.mutableX_history_ne fieldTail.succ counterWidth bit
            ⟨fieldTail.succ + bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.mutableX_history_ne fieldTail.succ counterWidth
            targetBit ⟨fieldTail.succ + sourceBit.val, by omega⟩)
        savedX (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hsaveT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldTail.succ counterWidth)
          clearedX = savedT0 := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        clearedX t0 (by rfl)
        (by
          change (RegisterRouting.historyLowPort fieldTail.succ
            counterWidth).read savedX = 0
          rw [RegisterRouting.historyLowPort_read_historyHighPort_set]
          simp [swapped, initial, cleanState, RegisterRouting.historyLowPort,
            MK.initialRegisters])
  have hclearT0 :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.historyLowToT0Gates fieldTail.succ counterWidth)
          savedT0 = clearedT0 := by
    simpa only [RegisterRouting.historyLowToT0Gates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (fun bit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
            ⟨bit.val, by omega⟩))
        (fun sourceBit targetBit =>
          RegisterRouting.t0_history_ne fieldTail.succ counterWidth targetBit
            ⟨sourceBit.val, by omega⟩)
        savedT0 (by
          rw [Arithmetic.BlockBank.WordPort.read_set]
          rfl)
  have hloadCoefficient :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.yToCoefficientGates fieldTail.succ counterWidth)
          clearedT0 = loadedCoefficient := by
    simpa only [RegisterRouting.yToCoefficientGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.mutableYPort fieldTail.succ counterWidth)
        (RegisterRouting.rCoefficientPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.mutableY_rCoefficient_ne fieldTail.succ
          counterWidth bit bit)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.mutableY_rCoefficient_ne fieldTail.succ counterWidth
            sourceBit targetBit))
        clearedT0 «λ» (by rfl)
        (by
          change (RegisterRouting.rCoefficientPort fieldTail.succ
            counterWidth).read initial = 0
          simp [initial, cleanState, RegisterRouting.rCoefficientPort,
            MK.initialRegisters])
  have hu :
      (RegisterRouting.uPort fieldTail.succ counterWidth).read
          loadedCoefficient = modulusWord fieldTail.succ p hp := by
    change (RegisterRouting.uPort fieldTail.succ counterWidth).read initial =
      ⟨p, hp⟩
    rfl
  have hs :
      (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
        loadedCoefficient = 1 := by
    change (RegisterRouting.sCoefficientPort fieldTail.succ counterWidth).read
      initial = 1
    simp [initial, cleanState, RegisterRouting.sCoefficientPort,
      MK.initialRegisters]
  have hnormalized := normalizeGates_stepList fieldTail.succ counterWidth p hp
    loadedCoefficient hu hs
  simp only [squareLambdaPrefixGates,
    EncodedBit.GateSpec.stepList_append]
  rw [hswap, hsaveX, hclearX, hsaveT0, hclearT0, hloadCoefficient,
    hnormalized]
  simp [loadedCoefficient, clearedT0, savedT0, clearedX, savedX, swapped,
    initial, cleanState, RegisterRouting.activeBit_flip,
    RegisterRouting.uPort, RegisterRouting.sCoefficientPort_set,
    RegisterRouting.rCoefficientPort_set, RegisterRouting.mutableXPort,
    RegisterRouting.t0Port, MontgomeryMultiplication.multiplicationState,
    CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
    CompactCorrection.widenFixedWord, CompactCorrection.truncateFixedWord,
    MK.initialRegisters, MK.Compact.cleanSharedWork, modulusWord]

/-- Out-of-place `t0 ^= lambda^2 * R^-1`.  The product is first XORed into
the saved low-history half; reversing the prefix then materializes the new
`t0` and clears that history half. -/
def squareLambdaGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := squareLambdaPrefixGates fieldTail counterWidth p hp
  let product := MontgomeryMultiplication.gates fieldTail counterWidth p
  prep ++ product ++
    RegisterRouting.saveT0LowGates fieldTail.succ counterWidth ++
    product.reverse ++ prep.reverse

def squareLambdaProgram
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Layout.encoding fieldTail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList
    (QubitLayout.canonical _) .empty
    (squareLambdaGates fieldTail counterWidth p hp)

def squareLambdaStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (squareLambdaGates fieldTail counterWidth p hp)

theorem squareLambda_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (squareLambdaProgram fieldTail counterWidth p hp)
      (squareLambdaStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList
    (QubitLayout.canonical _) .empty
    (squareLambdaGates fieldTail counterWidth p hp)

set_option maxHeartbeats 1200000 in
-- Both the multiplication and routing prefixes are canceled against their
-- exact endpoints on the updated public input.
/-- Clean-target endpoint for Algorithm 1, step 7 [RNSL17, ECDLP.tex:520].
Squaring `lambda` into clean `t0` restores the point words, compact arithmetic
work, and both history halves exactly. -/
theorem squareLambdaStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hlambda : «λ».val < p) :
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ «λ»
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      «λ» (List.finRange fieldTail.succ) residues).target
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      «λ» ⟨p, hp⟩ mutableX 0
    squareLambdaStep fieldTail counterWidth p hp initial =
        (RegisterRouting.t0Port fieldTail.succ counterWidth).set
          initial product ∧
      (product.val : ZMod p) =
        («λ».val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * («λ».val : ZMod p) := by
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ «λ»
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    «λ» (List.finRange fieldTail.succ) residues).target
  let initial := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX 0
  let swapped := { initial with mutableY := «λ», «λ» := mutableY }
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      swapped mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set clearedX 0
  let prefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient 0
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  let output := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX product
  let outputSwapped :=
    { output with mutableY := «λ», «λ» := mutableY }
  let outputSavedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      outputSwapped mutableX
  let outputClearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set
      outputSavedX 0
  let outputSavedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      outputClearedX product
  let outputPrefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient 0
  let outputComputed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient product
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ «λ»).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact hlambda
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by rfl
  have houtputPath : outputSavedT0.arithmetic.shared.path = false := by rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (squareLambdaPrefixGates fieldTail counterWidth p hp) initial =
        prefixState := by
    exact squareLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY «λ» mutableX 0
  have houtputPrefix :
      EncodedBit.GateSpec.stepList
          (squareLambdaPrefixGates fieldTail counterWidth p hp) output =
        outputPrefixState := by
    exact squareLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY «λ» mutableX product
  have hmultiplyFull := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiplyFull
  rcases hmultiplyFull with ⟨hmultiply, hproduct⟩
  have hsavedMultiplier : savedT0.mutableY = «λ» := by rfl
  have hmultiplyExact :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p)
          prefixState = computed := by
    simpa [MontgomeryMultiplication.step, prefixState, computed, product,
      residues, hsavedMultiplier] using hmultiply
  have houtputMultiplyFull :=
    MontgomeryMultiplication.step_cleanMontgomeryEndpoint fieldTail counterWidth
      p outputSavedT0 coefficient 0 hpPos hp hpOdd hcoefficient hzero
        houtputPath
  dsimp only at houtputMultiplyFull
  rcases houtputMultiplyFull with ⟨houtputMultiply, _houtputProduct⟩
  have houtputSavedMultiplier : outputSavedT0.mutableY = «λ» := by rfl
  have houtputMultiplyExact :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p)
          outputPrefixState = outputComputed := by
    simpa [MontgomeryMultiplication.step, outputPrefixState, outputComputed,
      product, residues, houtputSavedMultiplier] using houtputMultiply
  have hcopy :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldTail.succ counterWidth)
          computed =
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
          computed product := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_of_clean
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        computed product (by rfl)
        (by
          change (RegisterRouting.historyLowPort fieldTail.succ
            counterWidth).read savedT0 = 0
          rw [Arithmetic.BlockBank.WordPort.read_set])
  have hboundary :
      (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
          computed product = outputComputed := by
    simp [computed, outputComputed, outputSavedT0, outputClearedX,
      outputSavedX, outputSwapped, output, savedT0, clearedX, savedX, swapped,
      initial, cleanState, RegisterRouting.historyLowPort_set,
      RegisterRouting.historyHighPort_set, RegisterRouting.mutableXPort,
      MontgomeryMultiplication.multiplicationState,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      MK.initialRegisters, MK.Compact.cleanSharedWork]
  constructor
  · simp only [squareLambdaStep, squareLambdaGates,
      EncodedBit.GateSpec.stepList_append]
    rw [hprefix, hmultiplyExact, hcopy, hboundary, ← houtputMultiplyExact,
      EncodedBit.GateSpec.stepList_reverse_stepList, ← houtputPrefix,
      EncodedBit.GateSpec.stepList_reverse_stepList]
    rfl
  · rw [hsavedMultiplier] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

set_option maxHeartbeats 1200000 in
-- The equal-target case follows the same two-level endpoint cancellation.
/-- Equal-target endpoint for Algorithm 1, step 10 [RNSL17, ECDLP.tex:523].
If `t0` already contains the Montgomery square of `lambda`, the second xor
squaring clears `t0` and restores all borrowed work exactly. -/
theorem squareLambdaStep_equalEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hlambda : «λ».val < p) :
    let coefficient := CompactCorrection.widenFixedWord fieldTail.succ «λ»
    let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
      { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
          hpPos hp fieldTail.succ coefficient
        target := 0 }
    let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
      «λ» (List.finRange fieldTail.succ) residues).target
    let initial := cleanState fieldTail.succ counterWidth control mutableY
      «λ» ⟨p, hp⟩ mutableX product
    squareLambdaStep fieldTail counterWidth p hp initial =
        (RegisterRouting.t0Port fieldTail.succ counterWidth).set initial 0 ∧
      (product.val : ZMod p) =
        («λ».val : ZMod p) *
          (MontgomeryMultiplication.inverseRadixUnit p hpOdd fieldTail.succ :
            ZMod p) * («λ».val : ZMod p) := by
  let coefficient := CompactCorrection.widenFixedWord fieldTail.succ «λ»
  let residues : MontgomeryMultiplication.Residues fieldTail.succ :=
    { coefficient := MontgomeryMultiplication.inverseScaleWord fieldTail p
        hpPos hp fieldTail.succ coefficient
      target := 0 }
  let product := (MontgomeryMultiplication.residueRounds fieldTail p hpPos hp
    «λ» (List.finRange fieldTail.succ) residues).target
  let initial := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX product
  let swapped := { initial with mutableY := «λ», «λ» := mutableY }
  let savedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      swapped mutableX
  let clearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set savedX 0
  let savedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      clearedX product
  let prefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient 0
  let computed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      savedT0 coefficient product
  let output := cleanState fieldTail.succ counterWidth control mutableY «λ»
    ⟨p, hp⟩ mutableX 0
  let outputSwapped :=
    { output with mutableY := «λ», «λ» := mutableY }
  let outputSavedX :=
    (RegisterRouting.historyHighPort fieldTail.succ counterWidth).set
      outputSwapped mutableX
  let outputClearedX :=
    (RegisterRouting.mutableXPort fieldTail.succ counterWidth).set
      outputSavedX 0
  let outputSavedT0 :=
    (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
      outputClearedX 0
  let outputPrefixState :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient 0
  let outputComputed :=
    MontgomeryMultiplication.multiplicationState fieldTail counterWidth p hp
      outputSavedT0 coefficient product
  have hcoefficient : coefficient.val < p := by
    change (CompactCorrection.widenFixedWord fieldTail.succ «λ»).val < p
    rw [CompactCorrection.widenFixedWord_val]
    exact hlambda
  have hzero : (0 : Word fieldTail.succ).val < p := by
    simpa using hpPos
  have hpath : savedT0.arithmetic.shared.path = false := by rfl
  have houtputPath : outputSavedT0.arithmetic.shared.path = false := by rfl
  have hprefix :
      EncodedBit.GateSpec.stepList
          (squareLambdaPrefixGates fieldTail counterWidth p hp) initial =
        prefixState := by
    exact squareLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY «λ» mutableX product
  have houtputPrefix :
      EncodedBit.GateSpec.stepList
          (squareLambdaPrefixGates fieldTail counterWidth p hp) output =
        outputPrefixState := by
    exact squareLambdaPrefixGates_stepList fieldTail counterWidth p hp control
      mutableY «λ» mutableX 0
  have hmultiplyFull := MontgomeryMultiplication.step_cleanMontgomeryEndpoint
    fieldTail counterWidth p savedT0 coefficient 0 hpPos hp hpOdd hcoefficient
      hzero hpath
  dsimp only at hmultiplyFull
  rcases hmultiplyFull with ⟨hmultiply, hproduct⟩
  have hsavedMultiplier : savedT0.mutableY = «λ» := by rfl
  have hmultiplyExact :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p)
          prefixState = computed := by
    simpa [MontgomeryMultiplication.step, prefixState, computed, product,
      residues, hsavedMultiplier] using hmultiply
  have houtputMultiplyFull :=
    MontgomeryMultiplication.step_cleanMontgomeryEndpoint fieldTail counterWidth
      p outputSavedT0 coefficient 0 hpPos hp hpOdd hcoefficient hzero
        houtputPath
  dsimp only at houtputMultiplyFull
  rcases houtputMultiplyFull with ⟨houtputMultiply, _houtputProduct⟩
  have houtputSavedMultiplier : outputSavedT0.mutableY = «λ» := by rfl
  have houtputMultiplyExact :
      EncodedBit.GateSpec.stepList
          (MontgomeryMultiplication.gates fieldTail counterWidth p)
          outputPrefixState = outputComputed := by
    simpa [MontgomeryMultiplication.step, outputPrefixState, outputComputed,
      product, residues, houtputSavedMultiplier] using houtputMultiply
  have hcopy :
      EncodedBit.GateSpec.stepList
          (RegisterRouting.saveT0LowGates fieldTail.succ counterWidth)
          computed =
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
          computed 0 := by
    simpa only [RegisterRouting.saveT0LowGates] using
      RegisterRouting.copyGates_stepList_eq_set_zero_of_equal
        fieldTail.succ counterWidth
        (RegisterRouting.t0Port fieldTail.succ counterWidth)
        (RegisterRouting.historyLowPort fieldTail.succ counterWidth)
        (fun bit => RegisterRouting.t0_history_ne fieldTail.succ counterWidth bit
          ⟨bit.val, by omega⟩)
        (fun sourceBit targetBit => Ne.symm
          (RegisterRouting.t0_history_ne fieldTail.succ counterWidth sourceBit
            ⟨targetBit.val, by omega⟩))
        computed (by
          change product =
            (RegisterRouting.historyLowPort fieldTail.succ counterWidth).read
              savedT0
          rw [Arithmetic.BlockBank.WordPort.read_set])
  have hboundary :
      (RegisterRouting.historyLowPort fieldTail.succ counterWidth).set
          computed 0 = outputComputed := by
    simp [computed, outputComputed, outputSavedT0, outputClearedX,
      outputSavedX, outputSwapped, output, savedT0, clearedX, savedX, swapped,
      initial, cleanState, RegisterRouting.historyLowPort_set,
      RegisterRouting.historyHighPort_set, RegisterRouting.mutableXPort,
      MontgomeryMultiplication.multiplicationState,
      CompactCorrection.targetUpdateState, CompactCorrection.arithmeticState,
      MK.initialRegisters, MK.Compact.cleanSharedWork]
  constructor
  · simp only [squareLambdaStep, squareLambdaGates,
      EncodedBit.GateSpec.stepList_append]
    rw [hprefix, hmultiplyExact, hcopy, hboundary, ← houtputMultiplyExact,
      EncodedBit.GateSpec.stepList_reverse_stepList, ← houtputPrefix,
      EncodedBit.GateSpec.stepList_reverse_stepList]
    rfl
  · rw [hsavedMultiplier] at hproduct
    simpa [product, residues, coefficient, CompactCorrection.widenFixedWord,
      add_eq_left] using hproduct

/-! ## Literal ledger lengths -/

@[simp] theorem t0IntoLambdaGates_length
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    (t0IntoLambdaGates fieldTail counterWidth p hp).length =
      2 * (t0IntoLambdaPrefixGates fieldTail counterWidth p hp).length +
        2 * (MontgomeryMultiplication.gates fieldTail counterWidth p).length +
          fieldTail.succ := by
  simp [t0IntoLambdaGates, RegisterRouting.t0ToLambdaGates]
  omega

@[simp] theorem xIntoYGates_length
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    (xIntoYGates fieldTail counterWidth p hp).length =
      2 * (xIntoYPrefixGates fieldTail counterWidth p hp).length +
        2 * (MontgomeryMultiplication.gates fieldTail counterWidth p).length +
          fieldTail.succ := by
  simp [xIntoYGates, RegisterRouting.t0ToLambdaGates]
  omega

@[simp] theorem squareLambdaGates_length
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    (squareLambdaGates fieldTail counterWidth p hp).length =
      2 * (squareLambdaPrefixGates fieldTail counterWidth p hp).length +
        2 * (MontgomeryMultiplication.gates fieldTail counterWidth p).length +
          fieldTail.succ := by
  simp [squareLambdaGates]
  omega

end
end MontgomeryOperations
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end

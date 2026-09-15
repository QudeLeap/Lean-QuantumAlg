/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Algebra.Group.Defs
public import QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GroupPowerRecovery
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model

/-!
# Common word encoding and omitted-MSB group-power mathematics

The original encoded square and multiply declarations share one word encoder.
The Fourier capacity margin places every recovered candidate below the lower
half of its word. The same big-endian fold therefore reconstructs its value
while omitting the leading zero bit. These value facts introduce no execution
or caller-provided candidate correctness certificate.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery

open ClassicalAlgorithms ClassicalAlgorithms.Modular

universe u

variable {G : Type u} [Group G] {width : Nat}

/-- A word-shaped realization of the shared group-power access interface.
The conversion below is deliberately definitionally tied to the same encoder,
square, and multiply functions used by the declared calls. -/
public structure Access (G : Type u) [Group G] (width : Nat) where
  /-- Encode a mathematical group element into the checked word representation. -/
  encode : G → CShape.Word width
  /-- Runtime group square on encoded words. -/
  square : CShape.Word width → CShape.Word width
  /-- Runtime group multiplication on encoded words. -/
  multiply : CShape.Word width → CShape.Word width → CShape.Word width
  /-- The declared square preserves the common encoding. -/
  square_encode : ∀ value, square (encode value) = encode (value * value)
  /-- The declared multiply preserves the common encoding. -/
  multiply_encode : ∀ left right,
    multiply (encode left) (encode right) = encode (left * right)
  /-- Fresh word workspace is the encoded group identity. -/
  encode_one : encode 1 = CShape.initialValue (.unsignedWord width)
  /-- Native coordinate of one declared square capability. -/
  squareLabel : Resource.SubroutineLabel
  /-- Native coordinate of one declared multiply capability. -/
  multiplyLabel : Resource.SubroutineLabel
  /-- The two declared capabilities remain independently accountable. -/
  square_ne_multiply : squareLabel ≠ multiplyLabel

namespace Access

/-- The exact `GroupPowerRecovery.Access` witnessed by a word realization.
All executable declared calls below are made through this value. -/
def groupPowerAccess (A : Access G width) : GroupPowerRecovery.Access G where
  Code := CShape.Word width
  encode := A.encode
  square := A.square
  multiply := A.multiply
  square_encode := A.square_encode
  multiply_encode := A.multiply_encode

@[simp] theorem groupPowerAccess_encode (A : Access G width) :
    A.groupPowerAccess.encode = A.encode :=
  rfl

@[simp] theorem groupPowerAccess_square (A : Access G width) :
    A.groupPowerAccess.square = A.square :=
  rfl

@[simp] theorem groupPowerAccess_multiply (A : Access G width) :
    A.groupPowerAccess.multiply = A.multiply :=
  rfl

end Access

namespace Access

/-- Seal multiplication by the fixed mathematical generator.  This is the
unary declared-call form used by the tail: its evaluator is obtained from the
same `GroupPowerRecovery.Access` encoder and multiplication as square calls,
without borrowing or copying a second runtime generator word. -/
def sealedMultiplyGeneratorAccess (A : Access G width) (generator : G) :
    DeclaredClassicalCall.Access (.unsignedWord width) (.unsignedWord width) :=
  DeclaredClassicalCall.Access.declare A.multiplyLabel fun accumulator =>
    A.groupPowerAccess.multiply accumulator (A.groupPowerAccess.encode generator)

/-- The generator-capturing declaration evaluates through the common group
power access. -/
theorem sealedMultiplyGeneratorAccess_eval (A : Access G width) (generator : G)
    (accumulator : CShape.Word width) :
    (A.sealedMultiplyGeneratorAccess generator).eval accumulator =
      A.multiply accumulator (A.encode generator) :=
  rfl

/-- On encoded input, the generator-capturing declaration writes the encoded
mathematical product. -/
theorem sealedMultiplyGeneratorAccess_eval_encode (A : Access G width)
    (generator value : G) :
    (A.sealedMultiplyGeneratorAccess generator).eval (A.encode value) =
      A.encode (value * generator) := by
  rw [sealedMultiplyGeneratorAccess_eval, A.multiply_encode]

end Access

/-- Public finite-cyclic parameters used by the call-counted tail.  The
capacity margin is intentionally stronger than mere word fit: it proves that
every recovered candidate has a zero leading word bit. -/
structure Parameters (G : Type u) [Group G] where
  /-- Candidate-word width. -/
  width : Nat
  /-- The one raw-recovery modulus specification; its modulus is the group
  order used everywhere in this tail. -/
  spec : ModulusSpec width
  /-- The single recovery modulus is nonzero. -/
  order_pos : 0 < spec.modulus
  /-- The public Fourier capacity margin. -/
  capacity : 12 * spec.modulus ≤ 2 ^ width
  /-- Generator whose power is compared with the borrowed target word. -/
  generator : G
  /-- Word-code group-power implementation. -/
  access : Access G width

namespace Parameters

/-- The capacity margin excludes a zero-width candidate word. -/
theorem width_pos (P : Parameters G) : 0 < P.width := by
  by_contra notPositive
  have widthZero : P.width = 0 := Nat.eq_zero_of_not_pos notPositive
  have capacityZero : 12 * P.spec.modulus ≤ 1 := by
    simpa [widthZero] using P.capacity
  have orderPositive := P.order_pos
  omega

/-- The capacity margin in particular gives the strict raw-recovery word-fit
condition required by the total lexical producer contract. -/
theorem modulus_lt_twoPow (P : Parameters G) : P.spec.modulus < 2 ^ P.width := by
  have positive := P.order_pos
  have capacity := P.capacity
  omega

/-- A raw candidate below the group order lies below the lower half of the
candidate word under the public capacity margin. -/
theorem candidate_lt_lowerHalf (P : Parameters G) {candidate : Nat}
    (candidate_lt : candidate < P.spec.modulus) :
    candidate < 2 ^ (P.width - 1) := by
  have widthPos := P.width_pos
  obtain ⟨tailWidth, widthEq⟩ : ∃ tailWidth, P.width = tailWidth + 1 := by
    exact ⟨P.width - 1, by omega⟩
  have capacity' : 12 * P.spec.modulus ≤ 2 ^ (tailWidth + 1) := by
    simpa [widthEq] using P.capacity
  rw [pow_succ] at capacity'
  have orderBound : P.spec.modulus ≤ 2 ^ tailWidth := by
    omega
  simpa [widthEq] using candidate_lt.trans_le orderBound

/-- The most-significant Core word bit of every raw-range candidate is false.
The Core accessor is MSB-first, so this establishes the exact bit omitted by
the executable scan. -/
theorem candidate_leadingBit_false (P : Parameters G)
    (candidate : CShape.Word P.width)
    (candidate_lt : candidate.toNat < P.spec.modulus) :
    (candidate.wordBitGet ⟨0, P.width_pos⟩).toBool = false := by
  cases candidate with
  | unsignedWord value =>
      change value.val.testBit (P.width - 1 - 0) = false
      have lower : (value : Nat) < 2 ^ (P.width - 1) :=
        P.candidate_lt_lowerHalf candidate_lt
      simpa only [Nat.sub_zero] using Nat.testBit_eq_false_of_lt lower

end Parameters

/-- The position below the omitted leading bit corresponding to one tail-loop
index.  It is defined even at width zero because the source `Fin` is empty. -/
def tailIndex (width : Nat) (index : Fin (width - 1)) : Fin width :=
  ⟨index.val + 1, by omega⟩

/-- The Core MSB-first word accessor reconstructs the word's natural value
under the same head-first fold used by `powerRange_writes_encode`. -/
private theorem word_accumulatorFold_eq_toNat {width : Nat}
    (word : CShape.Word width) :
    ClassicalAlgorithms.TerminalDecode.accumulatorFold width 0
        (fun index => (word.wordBitGet index).toBool) = word.toNat := by
  cases word with
  | unsignedWord value =>
      rw [ClassicalAlgorithms.TerminalDecode.accumulatorFold_zero_eq_bigEndianFold,
        ClassicalAlgorithms.TerminalDecode.bigEndianFold_eq_ofBits]
      have bits :
          (fun index : Fin width =>
            ((CShape.Value.unsignedWord value).wordBitGet index).toBool) ∘ Fin.rev =
            fun index : Fin width => value.val.testBit index.val := by
        funext index
        change value.val.testBit (width - 1 - (Fin.rev index).val) =
          value.val.testBit index.val
        congr 1
        rw [Fin.val_rev]
        omega
      rw [bits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]
      rfl

/-- Once the leading MSB is known to be false, the lower-bit machine fold is
the full candidate value. -/
private theorem word_tailAccumulatorFold_eq_toNat (tailWidth : Nat)
    (word : CShape.Word (tailWidth + 1))
    (leadingFalse : (word.wordBitGet (0 : Fin (tailWidth + 1))).toBool = false) :
    ClassicalAlgorithms.TerminalDecode.accumulatorFold tailWidth 0
        (fun index =>
          (word.wordBitGet (tailIndex (tailWidth + 1) index)).toBool) = word.toNat := by
  have whole := word_accumulatorFold_eq_toNat word
  have tailBits :
      (fun index : Fin tailWidth =>
        (word.wordBitGet (tailIndex (tailWidth + 1) index)).toBool) =
        (fun index : Fin tailWidth => (word.wordBitGet index.succ).toBool) := rfl
  change ClassicalAlgorithms.TerminalDecode.accumulatorFold (tailWidth + 1) 0
      (fun index => (word.wordBitGet index).toBool) = word.toNat at whole
  rw [ClassicalAlgorithms.TerminalDecode.accumulatorFold] at whole
  simpa only [ClassicalAlgorithms.TerminalDecode.appendBit,
    leadingFalse, Bool.toNat_false, Nat.mul_zero, Nat.zero_add, tailBits,
    Function.comp_def] using whole

/-- A raw semantic output always supplies a candidate in the sole modulus
stored by `Parameters`; this is the range premise consumed by the omitted-MSB
proof. -/
theorem rawOutput_candidate_lt_order (P : Parameters G)
    (output : ClassicalRoutines.FiniteCyclicDLP.Output P.spec) :
    output.candidate.val < P.spec.modulus :=
  output.candidate.isLt

/-- The candidate represented by a successful raw output has a false leading
word bit under the public capacity margin. -/
theorem rawOutput_leadingBit_false (P : Parameters G)
    (output : ClassicalRoutines.FiniteCyclicDLP.Output P.spec) :
    ((CShape.wordOfNat P.width output.candidate.val).wordBitGet
      ⟨0, P.width_pos⟩).toBool = false := by
  apply P.candidate_leadingBit_false
  rw [CShape.wordOfNat_val, Nat.mod_eq_of_lt]
  · exact output.candidate.isLt
  · have orderFits : P.spec.modulus < 2 ^ P.width := by
      have capacity := P.capacity
      have orderPositive := P.order_pos
      omega
    exact output.candidate.isLt.trans orderFits

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery

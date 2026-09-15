/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Combinatorics
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.RSA.FixedWidthSampling
import all QuantumAlg.Util.RSA.ResidueSampling
import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Canonical Ekerå–Håstad batch-recovery values

This module fixes the pure value semantics of a sixteen-sample short-log
batch.  It keeps prepared residues together with raw terminal bits, decodes
the full register through the canonical little-endian index, and scans every
unordered pair before retaining the first recovered factor.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace BatchRecovery

noncomputable section

/-- Raw terminal bits of the two short-log exponent registers. -/
abbrev ShortLogTerminalBits (m ell : Nat) : Type :=
  Fin ((ell + m) + ell) → Bool

/-- One sealed prepared residue together with one raw terminal measurement. -/
structure PreparedSample (modulus m ell : Nat) where
  /-- The prepared component of this typed record. -/
  prepared : RSA.PreparedResidue modulus
  /-- The terminal bits component of this typed record. -/
  terminalBits : ShortLogTerminalBits m ell

/-- Decode a finite bit function in the canonical little-endian convention. -/
def decodeLittleEndianValue {width : Nat} (bits : Fin width → Bool) : Nat :=
  Nat.ofBits bits

/-- Convert the full-register terminal convention to its finite index. -/
def decodeFullRegisterIndex (m ell : Nat)
    (bits : ShortLogTerminalBits m ell) :
    Fin (2 ^ ((ell + m) + ell)) :=
  ⟨Nat.ofBits (bits ∘ Fin.rev), Nat.ofBits_lt_two_pow _⟩

/-- The finite full-register index is the reversed little-endian decoding. -/
@[simp] theorem decodeFullRegisterIndex_val (m ell : Nat)
    (bits : ShortLogTerminalBits m ell) :
    (decodeFullRegisterIndex m ell bits).val =
      decodeLittleEndianValue (bits ∘ Fin.rev) :=
  rfl

/-- Split one full-register terminal index into its two short-log samples. -/
def decodeTerminalSample (m ell : Nat)
    (bits : ShortLogTerminalBits m ell) : RSA.ShortLogSample m ell :=
  (prodEquiv (m := ell + m) (n := ell)).symm
    (decodeFullRegisterIndex m ell bits)

/-- The high register is the quotient by the low-register cardinality. -/
theorem decodeTerminalSample_fst_val (m ell : Nat)
    (bits : ShortLogTerminalBits m ell) :
    (decodeTerminalSample m ell bits).1.val =
      (decodeFullRegisterIndex m ell bits).val / 2 ^ ell := by
  exact prodEquiv_symm_fst_val (decodeFullRegisterIndex m ell bits)

/-- The low register is the remainder modulo its cardinality. -/
theorem decodeTerminalSample_snd_val (m ell : Nat)
    (bits : ShortLogTerminalBits m ell) :
    (decodeTerminalSample m ell bits).2.val =
      (decodeFullRegisterIndex m ell bits).val % 2 ^ ell := by
  exact prodEquiv_symm_snd_val (decodeFullRegisterIndex m ell bits)

/-- Recover from one prepared pair, prioritizing either early factor before
requiring the two terminal samples to have the same prepared unit. -/
def recoverPreparedPair (modulus m ell : Nat)
    (input : PreparedSample modulus m ell × PreparedSample modulus m ell) :
    Option Nat :=
  input.1.prepared.earlyFactor.orElse (fun _ =>
    input.2.prepared.earlyFactor.orElse (fun _ =>
      if input.1.prepared.unit = input.2.prepared.unit then
        RSA.recoverFactorFromShortLogPair m ell input.1.prepared.unit
          (decodeTerminalSample m ell input.1.terminalBits,
            decodeTerminalSample m ell input.2.terminalBits)
      else none))

/-- Stable value-level bridge for the pair recovery priority. -/
theorem recoverPreparedPair_eq (modulus m ell : Nat)
    (input : PreparedSample modulus m ell × PreparedSample modulus m ell) :
    recoverPreparedPair modulus m ell input =
      input.1.prepared.earlyFactor.orElse (fun _ =>
        input.2.prepared.earlyFactor.orElse (fun _ =>
          if input.1.prepared.unit = input.2.prepared.unit then
            RSA.recoverFactorFromShortLogPair m ell input.1.prepared.unit
              (decodeTerminalSample m ell input.1.terminalBits,
                decodeTerminalSample m ell input.2.terminalBits)
          else none)) :=
  rfl

/-- With one shared prepared residue, the unit guard is discharged and its
early factor remains the pair result's highest-priority outcome. -/
theorem recoverPreparedPair_same_prepared (modulus m ell : Nat)
    (prepared : RSA.PreparedResidue modulus)
    (first second : ShortLogTerminalBits m ell) :
    recoverPreparedPair modulus m ell
        (⟨prepared, first⟩, ⟨prepared, second⟩) =
      prepared.earlyFactor.orElse (fun _ =>
        RSA.recoverFactorFromShortLogPair m ell prepared.unit
          (decodeTerminalSample m ell first, decodeTerminalSample m ell second)) := by
  cases h : prepared.earlyFactor <;> simp [recoverPreparedPair, h]

/-- A recovered pair factor is always a nontrivial divisor of the modulus. -/
theorem recoverPreparedPair_some_sound
    {modulus m ell factor : Nat}
    {input : PreparedSample modulus m ell × PreparedSample modulus m ell}
    (hresult : recoverPreparedPair modulus m ell input = some factor) :
    factor ∣ modulus ∧ 1 < factor ∧ factor < modulus := by
  unfold recoverPreparedPair at hresult
  cases hfirst : input.1.prepared.earlyFactor with
  | some early =>
      simp only [hfirst, Option.orElse_some, Option.some.injEq] at hresult
      subst early
      exact input.1.prepared.earlyFactor_sound factor hfirst
  | none =>
      simp only [hfirst, Option.orElse_none] at hresult
      cases hsecond : input.2.prepared.earlyFactor with
      | some early =>
          simp only [hsecond, Option.orElse_some, Option.some.injEq] at hresult
          subst early
          exact input.2.prepared.earlyFactor_sound factor hsecond
      | none =>
          simp only [hsecond, Option.orElse_none] at hresult
          split at hresult
          next _ => exact RSA.recoverFactorFromShortLogPair_some_sound hresult
          next _ => simp at hresult

/-- Retain an earlier success while a value-level fold visits each later slot. -/
def retainFirstSuccessful {Value : Type}
    (selected candidate : Option Value) : Option Value :=
  match selected with
  | some value => some value
  | none => candidate

/-- Value projection of a full first-success scan. -/
def firstSuccessful {Value : Type} (values : List (Option Value)) : Option Value :=
  values.foldl retainFirstSuccessful none

private theorem foldl_retainFirstSuccessful_of_some
    {Value : Type} (values : List (Option Value)) (value : Value) :
    values.foldl retainFirstSuccessful (some value) = some value := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
      simpa [retainFirstSuccessful] using ih

/-- A successful full-scan value occurs in the scanned list. -/
theorem firstSuccessful_some_mem
    {Value : Type} {values : List (Option Value)} {candidate : Value}
    (hresult : firstSuccessful values = some candidate) :
    some candidate ∈ values := by
  induction values with
  | nil => simp [firstSuccessful] at hresult
  | cons head rest ih =>
      cases head with
      | none =>
          exact List.mem_cons_of_mem none
            (ih (by simpa [firstSuccessful, retainFirstSuccessful] using hresult))
      | some value =>
          have hvalue : value = candidate := by
            apply Option.some.inj
            simpa [firstSuccessful, retainFirstSuccessful,
              foldl_retainFirstSuccessful_of_some] using hresult
          subst candidate
          exact List.mem_cons_self

/-- A list containing a success produces a success under the full scan. -/
theorem firstSuccessful_eq_some_of_exists
    {Value : Type} {values : List (Option Value)}
    (hexists : ∃ candidate, some candidate ∈ values) :
    ∃ candidate, firstSuccessful values = some candidate := by
  induction values with
  | nil => simp at hexists
  | cons head rest ih =>
      cases head with
      | none =>
          rcases hexists with ⟨candidate, hcandidate⟩
          have hrest : some candidate ∈ rest := by simpa using hcandidate
          simpa [firstSuccessful, retainFirstSuccessful] using ih ⟨candidate, hrest⟩
      | some value =>
          exact ⟨value, by
            simp [firstSuccessful, retainFirstSuccessful,
              foldl_retainFirstSuccessful_of_some]⟩

/-- The complete list of recovery values for all unordered pairs in a fixed
sixteen-sample batch. -/
def batchPairValues (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16) :
    List (Option Nat) :=
  inputs.unorderedPairs.toList.map (recoverPreparedPair modulus m ell)

/-- The fixed sixteen-sample batch result is the first success across all of
its unordered pairs. -/
def batchValue (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16) : Option Nat :=
  firstSuccessful (batchPairValues modulus m ell inputs)

/-- Forgetting vector lengths exposes the canonical list pair enumeration. -/
theorem batchPairValues_eq_list (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16) :
    batchPairValues modulus m ell inputs =
      inputs.toList.unorderedPairs.map (recoverPreparedPair modulus m ell) := by
  simp only [batchPairValues, List.Vector.toList_unorderedPairs]

/-- The fixed batch scans exactly all `choose 16 2 = 120` pair values. -/
theorem batchPairValues_length (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16) :
    (batchPairValues modulus m ell inputs).length = 120 := by
  rw [batchPairValues_eq_list, List.length_map, List.length_unorderedPairs]
  rw [List.Vector.toList_length]
  norm_num [Nat.choose]

/-- List-level bridge for the fixed batch value. -/
theorem batchValue_eq_list (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16) :
    batchValue modulus m ell inputs =
      firstSuccessful
        (inputs.toList.unorderedPairs.map (recoverPreparedPair modulus m ell)) := by
  simp only [batchValue, batchPairValues, List.Vector.toList_unorderedPairs]

/-- Any successful pair value makes the fixed batch return some pair value. -/
theorem batchValue_eq_some_of_exists (modulus m ell : Nat)
    (inputs : List.Vector (PreparedSample modulus m ell) 16)
    (hexists : ∃ factor, some factor ∈ batchPairValues modulus m ell inputs) :
    ∃ factor, batchValue modulus m ell inputs = some factor := by
  unfold batchValue
  exact firstSuccessful_eq_some_of_exists hexists

/-- A successful batch result is always a nontrivial divisor of the modulus. -/
theorem batchValue_some_sound
    {modulus m ell factor : Nat}
    {inputs : List.Vector (PreparedSample modulus m ell) 16}
    (hresult : batchValue modulus m ell inputs = some factor) :
    factor ∣ modulus ∧ 1 < factor ∧ factor < modulus := by
  unfold batchValue at hresult
  have hmem := firstSuccessful_some_mem hresult
  unfold batchPairValues at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨input, _hinput, hpairResult⟩
  exact recoverPreparedPair_some_sound hpairResult

end

end BatchRecovery
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end

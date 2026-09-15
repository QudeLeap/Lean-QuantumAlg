/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scan

/-!
# Actual allocated scan returns the original RSA residue choice

The enclosing real workspace pushes establish zero and an empty latch. The
literal loader writes the public modulus while preserving those cells and
the packed sample. The subsequent real proposal fold therefore returns the
source's exact first eligible residue. No scratch initialization or key
separation is requested from the algorithm caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual initialized layout and literal loader establish the original scan specification. -/
theorem samplerScan_from_scope (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N))) (store : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N))
    (sampled : store.read sample = .bits (PackedSample.storedBits value)) :
    Proposal.selection (Layout.shared ctx (modulusBits N))
        (step N sample (Layout.pushStore (modulusBits N) store)).1 =
      RSA.firstValidResidue (RSA.classifyResidueProposals N
        (RSA.decodeFixedWidthWords (modulusBits N) residueProposalCount value)) := by
  let entered := Layout.pushStore (modulusBits N) store
  let loaded := (loaderStep N entered).1
  let target := Layout.modulusCell ctx (modulusBits N)
  let bits := List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)
  have sampleFree : target.key ∉ (Layout.underRead sample (modulusBits N)).storageKeys :=
    Layout.samplerLayout_original_free (width := modulusBits N) sample 10
  have loadedSample : loaded.read (Layout.underRead sample (modulusBits N)) =
      .bits (PackedSample.storedBits value) :=
    (ConstantWord.constantWord_fold_read_other target bits
      (Layout.underRead sample (modulusBits N)) sampleFree entered).trans
        ((Layout.samplerLayout_push_read sample (modulusBits N) store).trans sampled)
  have zeroFree : target.key ∉
      (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N))).storageKeys :=
    Layout.samplerLayout_cellRead_free (Layout.gcdResultCell ctx (modulusBits N)) _
      (Layout.samplerLayout_cellKey_ne ctx (modulusBits N) 10 9 (by decide))
  have zeroRead : loaded.read (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N))) =
      CShape.wordOfNat (modulusBits N + 1) 0 :=
    (ConstantWord.constantWord_fold_read_other target bits _ zeroFree entered).trans
      (Layout.samplerLayout_push_zero (modulusBits N) store)
  have loadedZero : (loaded.read ((Layout.shared ctx (modulusBits N)).zero)).toNat = 0 := by
    change (loaded.read
      (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N)))).toNat = 0
    exact (congrArg CShape.Value.toNat zeroRead).trans
      (by simp only [CShape.wordOfNat_val, Nat.zero_mod])
  have acceptedFree : target.key ∉
      (FirstAccepted.cellRead (Layout.acceptedCell ctx (modulusBits N))).storageKeys :=
    Layout.samplerLayout_cellRead_free (Layout.acceptedCell ctx (modulusBits N)) _
      (Layout.samplerLayout_cellKey_ne ctx (modulusBits N) 10 3 (by decide))
  have acceptedRead : loaded.read
      (FirstAccepted.cellRead (Layout.acceptedCell ctx (modulusBits N))) = .bit false :=
    (ConstantWord.constantWord_fold_read_other target bits _ acceptedFree entered).trans
      (Layout.samplerLayout_push_unaccepted (modulusBits N) store)
  have loadedUnaccepted : (loaded.read
      (FirstAccepted.cellRead ((Layout.shared ctx (modulusBits N)).selector.accepted))).toBool =
        false := congrArg CShape.Value.toBool acceptedRead
  have fits : N < 2 ^ (modulusBits N + 1) := by
    have bounded := input.register_fits
    have positive := Nat.two_pow_pos (modulusBits N)
    rw [pow_succ]
    omega
  have loadedModulus : (loaded.read ((Layout.shared ctx (modulusBits N)).modulus)).toNat = N :=
    (ConstantWord.constantWord_read target N entered).trans (Nat.mod_eq_of_lt fits)
  exact Proposal.proposalScan_firstValidResidue (Layout.underRead sample (modulusBits N))
    (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
    (Layout.samplerLayout_scan_separated (width := modulusBits N)
      (count := residueProposalCount) sample) loaded value N
    loadedSample loadedZero loadedModulus loadedUnaccepted

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan

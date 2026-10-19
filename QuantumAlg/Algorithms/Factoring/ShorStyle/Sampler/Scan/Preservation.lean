/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scan

/-!
# Stored modulus and zero-result invariants of the actual proposal scan

The literal public-modulus loader and all sixteen real proposal slots keep
the GCD result untouched. The slots also preserve the loaded modulus. These
complete-store facts establish the initialized inputs subsequently consumed
by the actual Euclidean decision arm.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan

open Execution
open ClassicalRoutines

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Loading and scanning preserve the complete GCD result cell on arbitrary inner storage. -/
lemma samplerScan_gcdResult (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    (step (model := model) N sample store).1.read
        (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N))) =
      store.read (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N))) := by
  let target := Layout.modulusCell ctx (modulusBits N)
  let loaded := (loaderStep (model := model) N store).1
  let shared := Layout.shared ctx (modulusBits N)
  let scratch := Layout.scratch ctx (modulusBits N)
  let zero := FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N))
  have separated := Layout.samplerLayout_scan_separated (width := modulusBits N)
    (count := residueProposalCount) sample
  have scanned : (Proposal.foldSteps (model := model) (Layout.underRead sample (modulusBits N))
      shared scratch (List.ofFn (fun proposal : Fin residueProposalCount => proposal))
      loaded).1.read zero = loaded.read zero :=
    Proposal.proposalFold_read_other (model := model) (Layout.underRead sample (modulusBits N))
      shared scratch _ zero separated.zeroFree loaded
  have loaderFree : target.key ∉ zero.storageKeys :=
    Layout.samplerLayout_cellRead_free (Layout.gcdResultCell ctx (modulusBits N)) _
      (Layout.samplerLayout_cellKey_ne ctx (modulusBits N) 10 9 (by decide))
  exact scanned.trans (ConstantWord.constantWord_fold_read_other (model := model) target
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) zero loaderFree store)

/-- The actual scan retains the exact public modulus written by its literal loader. -/
lemma samplerScan_modulus (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    ((step (model := model) N sample store).1.read
      (FirstAccepted.cellRead (Layout.modulusCell ctx (modulusBits N)))).toNat = N := by
  let target := Layout.modulusCell ctx (modulusBits N)
  let loaded := (loaderStep (model := model) N store).1
  let shared := Layout.shared ctx (modulusBits N)
  let scratch := Layout.scratch ctx (modulusBits N)
  have separated := Layout.samplerLayout_scan_separated (width := modulusBits N)
    (count := residueProposalCount) sample
  have scanned : (Proposal.foldSteps (model := model) (Layout.underRead sample (modulusBits N))
      shared scratch (List.ofFn (fun proposal : Fin residueProposalCount => proposal))
      loaded).1.read (FirstAccepted.cellRead target) =
        loaded.read (FirstAccepted.cellRead target) :=
    Proposal.proposalFold_read_other (model := model) (Layout.underRead sample (modulusBits N))
      shared scratch _ (FirstAccepted.cellRead target) separated.modulusFree loaded
  have fits : N < 2 ^ (modulusBits N + 1) := by
    have bounded := input.register_fits
    have positive := Nat.two_pow_pos (modulusBits N)
    rw [pow_succ]
    omega
  exact (congrArg CShape.Value.toNat scanned).trans
    ((ConstantWord.constantWord_read (model := model) target N store).trans (Nat.mod_eq_of_lt fits))

/-- The actual zero allocation remains zero until the GCD arm consumes it. -/
lemma samplerScan_from_scope_zero (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (store : Store ctx) :
    ((step (model := model) N sample (Layout.pushStore (modulusBits N) store)).1.read
      (FirstAccepted.cellRead (Layout.gcdResultCell ctx (modulusBits N)))).toNat = 0 := by
  have actual := (samplerScan_gcdResult (model := model)
    sample (Layout.pushStore (modulusBits N) store)).trans
    (Layout.samplerLayout_push_zero (modulusBits N) store)
  simpa only [CShape.wordOfNat_val, Nat.zero_mod] using congrArg CShape.Value.toNat actual

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan

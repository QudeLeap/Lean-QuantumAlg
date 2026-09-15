/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Fold
import Mathlib.Data.List.Nodup

/-!
# Scan separation derived from the actual eleven lexical cells

Every local read-separation fact follows from the final context's intrinsic
global key uniqueness. The only supplied input is an already present packed
sample; all eleven new keys are disjoint from its actual structural support.
No caller nonaliasing or initialization hypothesis is introduced.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width count : Nat}

/-- Actual internal key at one of the eleven intrinsic final-stack positions. -/
def samplerCellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 11) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 11; exact index.isLt⟩

/-- Distinct actual stack positions have distinct storage keys. -/
theorem samplerLayout_cellKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 11) (different : left ≠ right) :
    samplerCellKey ctx width left ≠ samplerCellKey ctx width right := by
  intro same
  have positions := (samplerLayout_keys_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- A cell read excludes every different real storage identity. -/
theorem samplerLayout_cellRead_free {shape : CShape}
    (other : CWriteRef (context ctx width) shape) (key : StorageKey)
    (different : key ≠ other.key) :
    key ∉ (FirstAccepted.cellRead other).storageKeys := by
  simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using different

/-- Every internal key is outside every original caller structural read. -/
theorem samplerLayout_original_free {shape : CShape}
    (input : CInputRef ctx shape) (index : Fin 11) :
    samplerCellKey ctx width index ∉ (underRead input width).storageKeys := by
  rw [samplerLayout_underRead_keys]
  intro present
  have internal : samplerCellKey ctx width index ∈ internalKeys ctx width :=
    List.get_mem (internalKeys ctx width) _
  exact List.disjoint_left.mp (samplerLayout_keys_disjoint ctx width)
    internal (input.storageKeys_subset_context present)

/-- The actual eleven-cell layout satisfies every comparison and selector read contract. -/
theorem samplerLayout_scan_separated (sample : CInputRef ctx (.bits (count * width))) :
    Proposal.ScanSeparated (underRead sample width) (shared ctx width) (scratch ctx width) := by
  refine
    { slot :=
        { comparison := ?_
          selector := ?_
          candidateSample := samplerLayout_original_free sample 8
          candidateZero := samplerLayout_cellRead_free (gcdResultCell ctx width) _
            (samplerLayout_cellKey_ne ctx width 8 9 (by decide))
          candidateModulus := samplerLayout_cellRead_free (modulusCell ctx width) _
            (samplerLayout_cellKey_ne ctx width 8 10 (by decide))
          prefixAccepted := ?_
          prefixSelected := ?_ }
      sampleFree := ?_
      zeroFree := ?_
      modulusFree := ?_ }
  · exact
      { extendedCandidate := samplerLayout_cellKey_ne ctx width 7 8 (by decide)
        positiveCandidate := samplerLayout_cellKey_ne ctx width 6 8 (by decide)
        belowCandidate := samplerLayout_cellKey_ne ctx width 5 8 (by decide)
        eligibleCandidate := samplerLayout_cellKey_ne ctx width 4 8 (by decide)
        positiveExtended := samplerLayout_cellKey_ne ctx width 6 7 (by decide)
        belowExtended := samplerLayout_cellKey_ne ctx width 5 7 (by decide)
        eligibleExtended := samplerLayout_cellKey_ne ctx width 4 7 (by decide)
        belowPositive := samplerLayout_cellKey_ne ctx width 5 6 (by decide)
        extendedZero := samplerLayout_cellRead_free (gcdResultCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 7 9 (by decide))
        extendedModulus := samplerLayout_cellRead_free (modulusCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 7 10 (by decide))
        positiveModulus := samplerLayout_cellRead_free (modulusCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 6 10 (by decide)) }
  · exact
      { availableEligible := samplerLayout_cellRead_free (eligibleCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 1 4 (by decide))
        availableCandidate := samplerLayout_cellRead_free (candidateCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 1 8 (by decide))
        takeCandidate := samplerLayout_cellRead_free (candidateCell ctx width) _
          (samplerLayout_cellKey_ne ctx width 0 8 (by decide))
        availableAccepted := samplerLayout_cellKey_ne ctx width 1 3 (by decide)
        takeAccepted := samplerLayout_cellKey_ne ctx width 0 3 (by decide)
        availableSelected := samplerLayout_cellKey_ne ctx width 1 2 (by decide)
        takeSelected := samplerLayout_cellKey_ne ctx width 0 2 (by decide)
        acceptedSelected := samplerLayout_cellKey_ne ctx width 3 2 (by decide) }
  · intro key present
    change key ∈ [(candidateCell ctx width).key,
      (extendedCell ctx width).key,
      (positiveCell ctx width).key,
      (belowModulusCell ctx width).key,
      (eligibleCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · exact samplerLayout_cellKey_ne ctx width 8 3 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 7 3 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 6 3 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 5 3 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 4 3 (by decide)
  · intro key present
    change key ∈ [(candidateCell ctx width).key,
      (extendedCell ctx width).key,
      (positiveCell ctx width).key,
      (belowModulusCell ctx width).key,
      (eligibleCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl
    · exact samplerLayout_cellKey_ne ctx width 8 2 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 7 2 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 6 2 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 5 2 (by decide)
    · exact samplerLayout_cellKey_ne ctx width 4 2 (by decide)
  · intro key present
    change key ∈ [(candidateCell ctx width).key,
      (extendedCell ctx width).key,
      (positiveCell ctx width).key,
      (belowModulusCell ctx width).key,
      (eligibleCell ctx width).key,
      (availableCell ctx width).key,
      (takeCell ctx width).key,
      (acceptedCell ctx width).key,
      (selectedCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact samplerLayout_original_free sample 8
    · exact samplerLayout_original_free sample 7
    · exact samplerLayout_original_free sample 6
    · exact samplerLayout_original_free sample 5
    · exact samplerLayout_original_free sample 4
    · exact samplerLayout_original_free sample 1
    · exact samplerLayout_original_free sample 0
    · exact samplerLayout_original_free sample 3
    · exact samplerLayout_original_free sample 2
  · intro key present
    change key ∈ [(candidateCell ctx width).key,
      (extendedCell ctx width).key,
      (positiveCell ctx width).key,
      (belowModulusCell ctx width).key,
      (eligibleCell ctx width).key,
      (availableCell ctx width).key,
      (takeCell ctx width).key,
      (acceptedCell ctx width).key,
      (selectedCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 8 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 7 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 6 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 5 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 4 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 1 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 0 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 3 9 (by decide))
    · exact samplerLayout_cellRead_free (gcdResultCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 2 9 (by decide))
  · intro key present
    change key ∈ [(candidateCell ctx width).key,
      (extendedCell ctx width).key,
      (positiveCell ctx width).key,
      (belowModulusCell ctx width).key,
      (eligibleCell ctx width).key,
      (availableCell ctx width).key,
      (takeCell ctx width).key,
      (acceptedCell ctx width).key,
      (selectedCell ctx width).key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 8 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 7 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 6 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 5 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 4 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 1 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 0 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 3 10 (by decide))
    · exact samplerLayout_cellRead_free (modulusCell ctx width) _
        (samplerLayout_cellKey_ne ctx width 2 10 (by decide))

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# The actual eleven lexical sampler cells

Every cell is added by the existing workspace operation at its parent's
canonical fresh key. References are the intrinsic positions of those real
entries. Three extended words, two proposal-width words and six bits occupy
the original eleven cells; later GCD execution adds only its own temporary
scopes. All initial caller entries and all physical quantum wires persist.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

open ClassicalRoutines

variable {kind : ProblemKind}

/-- Add the actual modulus cell beneath the preceding sampler entries. -/
def modulusCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh

/-- Add the actual gcdResult cell beneath the preceding sampler entries. -/
def gcdCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (modulusCtx ctx width).addWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1))
    (modulusCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual candidate cell beneath the preceding sampler entries. -/
def candidateCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (gcdCtx ctx width).addWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (gcdCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual extended cell beneath the preceding sampler entries. -/
def extendedCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (candidateCtx ctx width).addWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1))
    (candidateCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual positive cell beneath the preceding sampler entries. -/
def positiveCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (extendedCtx ctx width).addWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
    (extendedCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual belowModulus cell beneath the preceding sampler entries. -/
def belowCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (positiveCtx ctx width).addWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
    (positiveCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual eligible cell beneath the preceding sampler entries. -/
def eligibleCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (belowCtx ctx width).addWorkspace (belowCtx ctx width).canonicalFreshKey .bit
    (belowCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual accepted cell beneath the preceding sampler entries. -/
def acceptedCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (eligibleCtx ctx width).addWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
    (eligibleCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual selected cell beneath the preceding sampler entries. -/
def selectedCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (acceptedCtx ctx width).addWorkspace (acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width)
    (acceptedCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual available cell beneath the preceding sampler entries. -/
def availableCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (selectedCtx ctx width).addWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
    (selectedCtx ctx width).canonicalFreshKey_fresh

/-- Add the actual take cell beneath the preceding sampler entries. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (availableCtx ctx width).addWorkspace (availableCtx ctx width).canonicalFreshKey .bit
    (availableCtx ctx width).canonicalFreshKey_fresh

/-- Intrinsic final-context position of the actual modulus cell. -/
def modulusCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (width + 1)) where
  key := ctx.canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there
    (.there (.there (.there (.there (.there (.here))))))))))
  writable := by decide

/-- Intrinsic final-context position of the actual gcdResult cell. -/
def gcdResultCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (width + 1)) where
  key := (modulusCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there (.there (.there (.there (.there (.here)))))))))
  writable := by decide

/-- Intrinsic final-context position of the actual candidate cell. -/
def candidateCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) where
  key := (gcdCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there (.there (.there (.there (.here))))))))
  writable := by decide

/-- Intrinsic final-context position of the actual extended cell. -/
def extendedCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord (width + 1)) where
  key := (candidateCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there (.there (.there (.here)))))))
  writable := by decide

/-- Intrinsic final-context position of the actual positive cell. -/
def positiveCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (extendedCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there (.there (.here))))))
  writable := by decide

/-- Intrinsic final-context position of the actual belowModulus cell. -/
def belowModulusCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (positiveCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.there (.here)))))
  writable := by decide

/-- Intrinsic final-context position of the actual eligible cell. -/
def eligibleCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (belowCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.there (.here))))
  writable := by decide

/-- Intrinsic final-context position of the actual accepted cell. -/
def acceptedCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (eligibleCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.there (.here)))
  writable := by decide

/-- Intrinsic final-context position of the actual selected cell. -/
def selectedCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) where
  key := (acceptedCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.there (.here))
  writable := by decide

/-- Intrinsic final-context position of the actual available cell. -/
def availableCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (selectedCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .there (.here)
  writable := by decide

/-- Intrinsic final-context position of the actual take cell. -/
def takeCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) .bit where
  key := (availableCtx ctx width).canonicalFreshKey
  role := .workspace
  slot := .here
  writable := by decide

/-- The proposal scanner's actual endpoint and selector references. -/
def shared (ctx : RuntimeCtx kind) (width : Nat) :
    Proposal.SharedRefs (context ctx width) width where
  modulus := FirstAccepted.cellRead (modulusCell ctx width)
  zero := FirstAccepted.cellRead (gcdResultCell ctx width)
  selector :=
    { accepted := acceptedCell ctx width
      selected := selectedCell ctx width
      available := availableCell ctx width
      take := takeCell ctx width }

/-- The actual decoder and comparison cells used by all sixteen proposals. -/
def scratch (ctx : RuntimeCtx kind) (width : Nat) :
    Proposal.ScratchRefs (context ctx width) width where
  candidate := candidateCell ctx width
  extended := extendedCell ctx width
  positive := positiveCell ctx width
  belowModulus := belowModulusCell ctx width
  eligible := eligibleCell ctx width

/-- Lift an existing structural read through exactly the eleven actual lexical entries. -/
def underRead {ctx : RuntimeCtx kind} {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) : CInputRef (context ctx width) shape :=
  let stage1 := input.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
  let stage2 := stage1.underWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh
  let stage3 := stage2.underWorkspace (gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh
  let stage4 := stage3.underWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh
  let stage5 := stage4.underWorkspace (extendedCtx ctx width).canonicalFreshKey
    .bit (extendedCtx ctx width).canonicalFreshKey_fresh
  let stage6 := stage5.underWorkspace (positiveCtx ctx width).canonicalFreshKey
    .bit (positiveCtx ctx width).canonicalFreshKey_fresh
  let stage7 := stage6.underWorkspace (belowCtx ctx width).canonicalFreshKey
    .bit (belowCtx ctx width).canonicalFreshKey_fresh
  let stage8 := stage7.underWorkspace (eligibleCtx ctx width).canonicalFreshKey
    .bit (eligibleCtx ctx width).canonicalFreshKey_fresh
  let stage9 := stage8.underWorkspace (acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh
  let stage10 := stage9.underWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  let stage11 := stage10.underWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh
  stage11

/-- Lift an existing writable output through exactly the eleven actual lexical entries. -/
def underWrite {ctx : RuntimeCtx kind} {shape : CShape} (input : CWriteRef ctx shape)
    (width : Nat) : CWriteRef (context ctx width) shape :=
  let stage1 := input.underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
  let stage2 := stage1.underWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh
  let stage3 := stage2.underWorkspace (gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh
  let stage4 := stage3.underWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh
  let stage5 := stage4.underWorkspace (extendedCtx ctx width).canonicalFreshKey
    .bit (extendedCtx ctx width).canonicalFreshKey_fresh
  let stage6 := stage5.underWorkspace (positiveCtx ctx width).canonicalFreshKey
    .bit (positiveCtx ctx width).canonicalFreshKey_fresh
  let stage7 := stage6.underWorkspace (belowCtx ctx width).canonicalFreshKey
    .bit (belowCtx ctx width).canonicalFreshKey_fresh
  let stage8 := stage7.underWorkspace (eligibleCtx ctx width).canonicalFreshKey
    .bit (eligibleCtx ctx width).canonicalFreshKey_fresh
  let stage9 := stage8.underWorkspace (acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh
  let stage10 := stage9.underWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  let stage11 := stage10.underWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh
  stage11

/-- The actual eleven internal storage identities in their final stack order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  [(takeCell ctx width).key,
    (availableCell ctx width).key,
    (selectedCell ctx width).key,
    (acceptedCell ctx width).key,
    (eligibleCell ctx width).key,
    (belowModulusCell ctx width).key,
    (positiveCell ctx width).key,
    (extendedCell ctx width).key,
    (candidateCell ctx width).key,
    (gcdResultCell ctx width).key,
    (modulusCell ctx width).key]

/-- The real final context lists exactly these eleven cells before all original entries. -/
theorem samplerLayout_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := rfl

/-- Intrinsic global context uniqueness proves that all eleven actual cell keys differ. -/
theorem samplerLayout_keys_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [samplerLayout_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Every internal cell is distinct from every original caller entry. -/
theorem samplerLayout_keys_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [samplerLayout_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- The actual classical lexical cells leave the full physical quantum bank unchanged. -/
theorem samplerLayout_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout

/-!
# Actual entry and exit of the eleven sampler scopes

The store maps are precisely the pushes and pops of the existing lexical
workspace instructions. Their head values establish the scan's real zero
word and empty acceptance latch. Every original structural input survives
entry, and exit exposes its final value without changing it.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Enter the actual eleven workspace scopes in their declared allocation order. -/
def pushStore (width : Nat) (store : Store ctx) : Store (context ctx width) :=
  let stage1 := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
  let stage2 := stage1.pushWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh
  let stage3 := stage2.pushWorkspace (gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh
  let stage4 := stage3.pushWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh
  let stage5 := stage4.pushWorkspace (extendedCtx ctx width).canonicalFreshKey
    .bit (extendedCtx ctx width).canonicalFreshKey_fresh
  let stage6 := stage5.pushWorkspace (positiveCtx ctx width).canonicalFreshKey
    .bit (positiveCtx ctx width).canonicalFreshKey_fresh
  let stage7 := stage6.pushWorkspace (belowCtx ctx width).canonicalFreshKey
    .bit (belowCtx ctx width).canonicalFreshKey_fresh
  let stage8 := stage7.pushWorkspace (eligibleCtx ctx width).canonicalFreshKey
    .bit (eligibleCtx ctx width).canonicalFreshKey_fresh
  let stage9 := stage8.pushWorkspace (acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh
  let stage10 := stage9.pushWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  let stage11 := stage10.pushWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh
  stage11

/-- Release the same eleven real lexical cells in the exact reverse order. -/
def popStore (width : Nat) (store : Store (context ctx width)) : Store ctx :=
  let stage10 := Store.popWorkspace (availableCtx ctx width).canonicalFreshKey
    .bit (availableCtx ctx width).canonicalFreshKey_fresh store
  let stage9 := Store.popWorkspace (selectedCtx ctx width).canonicalFreshKey
    .bit (selectedCtx ctx width).canonicalFreshKey_fresh stage10
  let stage8 := Store.popWorkspace (acceptedCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh stage9
  let stage7 := Store.popWorkspace (eligibleCtx ctx width).canonicalFreshKey
    .bit (eligibleCtx ctx width).canonicalFreshKey_fresh stage8
  let stage6 := Store.popWorkspace (belowCtx ctx width).canonicalFreshKey
    .bit (belowCtx ctx width).canonicalFreshKey_fresh stage7
  let stage5 := Store.popWorkspace (positiveCtx ctx width).canonicalFreshKey
    .bit (positiveCtx ctx width).canonicalFreshKey_fresh stage6
  let stage4 := Store.popWorkspace (extendedCtx ctx width).canonicalFreshKey
    .bit (extendedCtx ctx width).canonicalFreshKey_fresh stage5
  let stage3 := Store.popWorkspace (candidateCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh stage4
  let stage2 := Store.popWorkspace (gcdCtx ctx width).canonicalFreshKey
    (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh stage3
  let stage1 := Store.popWorkspace (modulusCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh stage2
  let stage0 := Store.popWorkspace ctx.canonicalFreshKey
    (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh stage1
  stage0

/-- The structural lift retains the exact original set of read keys. -/
lemma samplerLayout_underRead_keys {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys := by
  let reference1 : CInputRef (modulusCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let reference2 : CInputRef (gcdCtx ctx width) shape :=
    reference1.underWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh
  let reference3 : CInputRef (candidateCtx ctx width) shape :=
    reference2.underWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh
  let reference4 : CInputRef (extendedCtx ctx width) shape :=
    reference3.underWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh
  let reference5 : CInputRef (positiveCtx ctx width) shape :=
    reference4.underWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh
  let reference6 : CInputRef (belowCtx ctx width) shape :=
    reference5.underWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh
  let reference7 : CInputRef (eligibleCtx ctx width) shape :=
    reference6.underWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh
  let reference8 : CInputRef (acceptedCtx ctx width) shape :=
    reference7.underWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh
  let reference9 : CInputRef (selectedCtx ctx width) shape :=
    reference8.underWorkspace (acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh
  let reference10 : CInputRef (availableCtx ctx width) shape :=
    reference9.underWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh
  let reference11 : CInputRef (context ctx width) shape :=
    reference10.underWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh
  have h1 : reference1.storageKeys = input.storageKeys :=
    CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
      (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
  have h2 : reference2.storageKeys = reference1.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference1 (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh
  have h3 : reference3.storageKeys = reference2.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference2 (gcdCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh
  have h4 : reference4.storageKeys = reference3.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference3 (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh
  have h5 : reference5.storageKeys = reference4.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference4 (extendedCtx ctx width).canonicalFreshKey
      .bit (extendedCtx ctx width).canonicalFreshKey_fresh
  have h6 : reference6.storageKeys = reference5.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference5 (positiveCtx ctx width).canonicalFreshKey
      .bit (positiveCtx ctx width).canonicalFreshKey_fresh
  have h7 : reference7.storageKeys = reference6.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference6 (belowCtx ctx width).canonicalFreshKey
      .bit (belowCtx ctx width).canonicalFreshKey_fresh
  have h8 : reference8.storageKeys = reference7.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference7 (eligibleCtx ctx width).canonicalFreshKey
      .bit (eligibleCtx ctx width).canonicalFreshKey_fresh
  have h9 : reference9.storageKeys = reference8.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference8 (acceptedCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh
  have h10 : reference10.storageKeys = reference9.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference9 (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh
  have h11 : reference11.storageKeys = reference10.storageKeys :=
    CInputRef.storageKeys_underWorkspace reference10 (availableCtx ctx width).canonicalFreshKey
      .bit (availableCtx ctx width).canonicalFreshKey_fresh
  exact h11.trans (h10.trans (h9.trans (h8.trans (h7.trans (h6.trans (
    h5.trans (h4.trans (h3.trans (h2.trans (h1))))))))))

/-- Real lexical entry preserves the complete value of every original structural input. -/
lemma samplerLayout_push_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let reference1 : CInputRef (modulusCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let reference2 : CInputRef (gcdCtx ctx width) shape :=
    reference1.underWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh
  let reference3 : CInputRef (candidateCtx ctx width) shape :=
    reference2.underWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh
  let reference4 : CInputRef (extendedCtx ctx width) shape :=
    reference3.underWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh
  let reference5 : CInputRef (positiveCtx ctx width) shape :=
    reference4.underWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh
  let reference6 : CInputRef (belowCtx ctx width) shape :=
    reference5.underWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh
  let reference7 : CInputRef (eligibleCtx ctx width) shape :=
    reference6.underWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh
  let reference8 : CInputRef (acceptedCtx ctx width) shape :=
    reference7.underWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh
  let reference9 : CInputRef (selectedCtx ctx width) shape :=
    reference8.underWorkspace (acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh
  let reference10 : CInputRef (availableCtx ctx width) shape :=
    reference9.underWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh
  let reference11 : CInputRef (context ctx width) shape :=
    reference10.underWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh
  let state1 : Store (modulusCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let state2 : Store (gcdCtx ctx width) :=
    state1.pushWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh
  let state3 : Store (candidateCtx ctx width) :=
    state2.pushWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh
  let state4 : Store (extendedCtx ctx width) :=
    state3.pushWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh
  let state5 : Store (positiveCtx ctx width) :=
    state4.pushWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh
  let state6 : Store (belowCtx ctx width) :=
    state5.pushWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh
  let state7 : Store (eligibleCtx ctx width) :=
    state6.pushWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh
  let state8 : Store (acceptedCtx ctx width) :=
    state7.pushWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh
  let state9 : Store (selectedCtx ctx width) :=
    state8.pushWorkspace (acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh
  let state10 : Store (availableCtx ctx width) :=
    state9.pushWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh
  let state11 : Store (context ctx width) :=
    state10.pushWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh
  have h1 : state1.read reference1 = store.read input :=
    Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh input
  have h2 : state2.read reference2 = state1.read reference1 :=
    Store.read_pushWorkspace_underWorkspace state1 (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1)) (modulusCtx ctx width).canonicalFreshKey_fresh reference1
  have h3 : state3.read reference3 = state2.read reference2 :=
    Store.read_pushWorkspace_underWorkspace state2 (gcdCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (gcdCtx ctx width).canonicalFreshKey_fresh reference2
  have h4 : state4.read reference4 = state3.read reference3 :=
    Store.read_pushWorkspace_underWorkspace state3 (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1)) (candidateCtx ctx width).canonicalFreshKey_fresh reference3
  have h5 : state5.read reference5 = state4.read reference4 :=
    Store.read_pushWorkspace_underWorkspace state4 (extendedCtx ctx width).canonicalFreshKey
      .bit (extendedCtx ctx width).canonicalFreshKey_fresh reference4
  have h6 : state6.read reference6 = state5.read reference5 :=
    Store.read_pushWorkspace_underWorkspace state5 (positiveCtx ctx width).canonicalFreshKey
      .bit (positiveCtx ctx width).canonicalFreshKey_fresh reference5
  have h7 : state7.read reference7 = state6.read reference6 :=
    Store.read_pushWorkspace_underWorkspace state6 (belowCtx ctx width).canonicalFreshKey
      .bit (belowCtx ctx width).canonicalFreshKey_fresh reference6
  have h8 : state8.read reference8 = state7.read reference7 :=
    Store.read_pushWorkspace_underWorkspace state7 (eligibleCtx ctx width).canonicalFreshKey
      .bit (eligibleCtx ctx width).canonicalFreshKey_fresh reference7
  have h9 : state9.read reference9 = state8.read reference8 :=
    Store.read_pushWorkspace_underWorkspace state8 (acceptedCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (acceptedCtx ctx width).canonicalFreshKey_fresh reference8
  have h10 : state10.read reference10 = state9.read reference9 :=
    Store.read_pushWorkspace_underWorkspace state9 (selectedCtx ctx width).canonicalFreshKey
      .bit (selectedCtx ctx width).canonicalFreshKey_fresh reference9
  have h11 : state11.read reference11 = state10.read reference10 :=
    Store.read_pushWorkspace_underWorkspace state10 (availableCtx ctx width).canonicalFreshKey
      .bit (availableCtx ctx width).canonicalFreshKey_fresh reference10
  exact h11.trans (h10.trans (h9.trans (h8.trans (h7.trans (h6.trans (
    h5.trans (h4.trans (h3.trans (h2.trans (h1))))))))))

/-- Real lexical exit exposes precisely the final value of each original structural input. -/
lemma samplerLayout_pop_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let reference1 : CInputRef (modulusCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh
  let reference2 : CInputRef (gcdCtx ctx width) shape :=
    reference1.underWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh
  let reference3 : CInputRef (candidateCtx ctx width) shape :=
    reference2.underWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh
  let reference4 : CInputRef (extendedCtx ctx width) shape :=
    reference3.underWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh
  let reference5 : CInputRef (positiveCtx ctx width) shape :=
    reference4.underWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh
  let reference6 : CInputRef (belowCtx ctx width) shape :=
    reference5.underWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh
  let reference7 : CInputRef (eligibleCtx ctx width) shape :=
    reference6.underWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh
  let reference8 : CInputRef (acceptedCtx ctx width) shape :=
    reference7.underWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh
  let reference9 : CInputRef (selectedCtx ctx width) shape :=
    reference8.underWorkspace (acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh
  let reference10 : CInputRef (availableCtx ctx width) shape :=
    reference9.underWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh
  let reference11 : CInputRef (context ctx width) shape :=
    reference10.underWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh
  let state10 : Store (availableCtx ctx width) :=
    Store.popWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh store
  let state9 : Store (selectedCtx ctx width) :=
    Store.popWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh state10
  let state8 : Store (acceptedCtx ctx width) :=
    Store.popWorkspace (acceptedCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh state9
  let state7 : Store (eligibleCtx ctx width) :=
    Store.popWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh state8
  let state6 : Store (belowCtx ctx width) :=
    Store.popWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh state7
  let state5 : Store (positiveCtx ctx width) :=
    Store.popWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh state6
  let state4 : Store (extendedCtx ctx width) :=
    Store.popWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh state5
  let state3 : Store (candidateCtx ctx width) :=
    Store.popWorkspace (candidateCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh state4
  let state2 : Store (gcdCtx ctx width) :=
    Store.popWorkspace (gcdCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh state3
  let state1 : Store (modulusCtx ctx width) :=
    Store.popWorkspace (modulusCtx ctx width).canonicalFreshKey (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh state2
  let state0 : Store ctx :=
    Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh state1
  have h1 : state0.read input = state1.read reference1 :=
    Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
      ctx.canonicalFreshKey_fresh state1 input
  have h2 : state1.read reference1 = state2.read reference2 :=
    Store.read_popWorkspace_underWorkspace (modulusCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (modulusCtx ctx width).canonicalFreshKey_fresh state2 reference1
  have h3 : state2.read reference2 = state3.read reference3 :=
    Store.read_popWorkspace_underWorkspace (gcdCtx ctx width).canonicalFreshKey
      (.unsignedWord width)
      (gcdCtx ctx width).canonicalFreshKey_fresh state3 reference2
  have h4 : state3.read reference3 = state4.read reference4 :=
    Store.read_popWorkspace_underWorkspace (candidateCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + 1))
      (candidateCtx ctx width).canonicalFreshKey_fresh state4 reference3
  have h5 : state4.read reference4 = state5.read reference5 :=
    Store.read_popWorkspace_underWorkspace (extendedCtx ctx width).canonicalFreshKey .bit
      (extendedCtx ctx width).canonicalFreshKey_fresh state5 reference4
  have h6 : state5.read reference5 = state6.read reference6 :=
    Store.read_popWorkspace_underWorkspace (positiveCtx ctx width).canonicalFreshKey .bit
      (positiveCtx ctx width).canonicalFreshKey_fresh state6 reference5
  have h7 : state6.read reference6 = state7.read reference7 :=
    Store.read_popWorkspace_underWorkspace (belowCtx ctx width).canonicalFreshKey .bit
      (belowCtx ctx width).canonicalFreshKey_fresh state7 reference6
  have h8 : state7.read reference7 = state8.read reference8 :=
    Store.read_popWorkspace_underWorkspace (eligibleCtx ctx width).canonicalFreshKey .bit
      (eligibleCtx ctx width).canonicalFreshKey_fresh state8 reference7
  have h9 : state8.read reference8 = state9.read reference9 :=
    Store.read_popWorkspace_underWorkspace (acceptedCtx ctx width).canonicalFreshKey
      (.unsignedWord width)
      (acceptedCtx ctx width).canonicalFreshKey_fresh state9 reference8
  have h10 : state9.read reference9 = state10.read reference10 :=
    Store.read_popWorkspace_underWorkspace (selectedCtx ctx width).canonicalFreshKey .bit
      (selectedCtx ctx width).canonicalFreshKey_fresh state10 reference9
  have h11 : state10.read reference10 = store.read reference11 :=
    Store.read_popWorkspace_underWorkspace (availableCtx ctx width).canonicalFreshKey .bit
      (availableCtx ctx width).canonicalFreshKey_fresh store reference10
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (
    h7.trans (h8.trans (h9.trans (h10.trans (h11))))))))))

/-- The actual allocated GCD-result cell supplies the scan's zero endpoint. -/
lemma samplerLayout_push_zero (width : Nat) (store : Store ctx) :
    (pushStore width store).read (FirstAccepted.cellRead (gcdResultCell ctx width)) =
      CShape.wordOfNat (width + 1) 0 := rfl

/-- The actual allocated acceptance latch starts empty, independently of caller storage. -/
lemma samplerLayout_push_unaccepted (width : Nat) (store : Store ctx) :
    (pushStore width store).read (FirstAccepted.cellRead (acceptedCell ctx width)) =
      .bit false := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Layout

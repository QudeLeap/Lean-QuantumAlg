/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context

/-!
# Actual retention of the complete recycled factoring frame

These programs use only the existing retain, identity, and sequence nodes.
In particular they neither sample residues nor compute parameters, prepare
quantum systems, or pack future measurement outcomes. Subsequent execution
fills the preallocated destinations in the original chronological order.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame

noncomputable section

variable [configuration : Configuration]

open Execution ShortDLP.CompiledMAU
open EkeraHastadStyle.Canonical

/-- Retain the existing chronological packed-result layout without running its members. -/
def allocatePacked (m ell width : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Circuit ShortDLP.CompiledMAU.Recycling.model base
      (RuntimeResults.context m ell width base count)
  | base, 0 => Circuit.id (model := ShortDLP.CompiledMAU.Recycling.model) base
  | base, count + 1 =>
      (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
        base base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
        base.canonicalFreshKey_fresh).seq
          (allocatePacked m ell width (RuntimeResults.next m ell width base) count)

/-- Allocate one batch's source pair, configured packed observations, and recovery factor. -/
def allocateBatch (base : RuntimeCtx .quantum) (N : Nat) :
    Circuit ShortDLP.CompiledMAU.Recycling.model base (batch base N) :=
  (ShorStyle.Canonical.Sampler.Retained.allocation
    (model := ShortDLP.CompiledMAU.Recycling.model) base N).seq
      ((allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
        (sampled base N) membersPerBatch).seq
          (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
            (outcomes base N) (outcomes base N).canonicalFreshKey
            (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh))

/-- All batch storage exists before the parent makes the sole quantum allocation. -/
def allocateBatches (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Circuit ShortDLP.CompiledMAU.Recycling.model base (batches N base count)
  | base, 0 => Circuit.id (model := ShortDLP.CompiledMAU.Recycling.model) base
  | base, count + 1 =>
      (allocateBatch base N).seq (allocateBatches N (batch base N) count)

/-- Retain the distinct final selected-factor cell after all batch destinations. -/
def allocate (base : RuntimeCtx .quantum) (N count : Nat) :
    Circuit ShortDLP.CompiledMAU.Recycling.model base (context base N count) :=
  (allocateBatches N base count).seq
    (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
      (batches N base count) (batches N base count).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh)

omit configuration in
/-- Preallocating packed destinations emits no random, packing, or quantum event. -/
lemma rsaRecyclingFrame_allocatePacked_trace (m ell width : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocatePacked m ell width base count).Path) :
    (allocatePacked m ell width base count).eventTrace path = [] := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      change [] ++ (allocatePacked m ell width
        (RuntimeResults.next m ell width base) count).eventTrace path.2 = []
      exact ih _ path.2

/-- The complete batch allocation has no native events. -/
lemma rsaRecyclingFrame_allocateBatch_trace (base : RuntimeCtx .quantum) (N : Nat)
    (path : (allocateBatch base N).Path) :
    (allocateBatch base N).eventTrace path = [] := by
  let trace : List (Resource.Event ShortDLP.CompiledMAU.Recycling.model) :=
    (allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (sampled base N) membersPerBatch).eventTrace path.2.1
  have empty : trace = [] :=
    rsaRecyclingFrame_allocatePacked_trace (shortLogBits N) (tradeoffBits N)
      (arithmeticBits N) (sampled base N) membersPerBatch path.2.1
  change [] ++ (trace ++ []) = []
  exact (List.nil_append (trace ++ [])).trans ((List.append_nil trace).trans empty)

/-- All batches are initialized without drawing any future source sample. -/
lemma rsaRecyclingFrame_allocateBatches_trace (N : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocateBatches N base count).Path) :
    (allocateBatches N base count).eventTrace path = [] := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      change (allocateBatch base N).eventTrace path.1 ++
        (allocateBatches N (batch base N) count).eventTrace path.2 = []
      exact congrArg₂ (fun left right => left ++ right)
        (rsaRecyclingFrame_allocateBatch_trace base N path.1)
        (ih (batch base N) path.2)

/-- The complete preallocation contains no native event; its storage is still counted. -/
lemma rsaRecyclingFrame_allocate_trace (base : RuntimeCtx .quantum) (N count : Nat)
    (path : (allocate base N count).Path) :
    (allocate base N count).eventTrace path = [] := by
  change (allocateBatches N base count).eventTrace path.1 ++ [] = []
  rw [rsaRecyclingFrame_allocateBatches_trace, List.append_nil]

omit configuration in
/-- The actual packed-destination allocation has no event duration under any clock. -/
lemma rsaRecyclingFrame_allocatePacked_depth (m ell width : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (duration : Resource.Event ShortDLP.CompiledMAU.Recycling.model → Nat)
    (path : (allocatePacked m ell width base count).Path) :
    (allocatePacked m ell width base count).depth duration path = 0 := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      change 0 + (allocatePacked m ell width
        (RuntimeResults.next m ell width base) count).depth duration path.2 = 0
      exact (Nat.zero_add _).trans
        (ih (RuntimeResults.next m ell width base) path.2)

/-- Retaining the complete source pair and all result destinations has zero duration. -/
lemma rsaRecyclingFrame_allocateBatch_depth (base : RuntimeCtx .quantum) (N : Nat)
    (duration : Resource.Event ShortDLP.CompiledMAU.Recycling.model → Nat)
    (path : (allocateBatch base N).Path) :
    (allocateBatch base N).depth duration path = 0 := by
  change (0 + 0) + ((allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sampled base N) membersPerBatch).depth duration path.2.1 + 0) = 0
  exact (congrArg (fun work : Nat => (0 + 0) + (work + 0))
    (rsaRecyclingFrame_allocatePacked_depth (shortLogBits N) (tradeoffBits N)
      (arithmeticBits N) (sampled base N) membersPerBatch duration path.2.1)).trans rfl

/-- Every preallocated batch has zero event duration, including an empty batch family. -/
lemma rsaRecyclingFrame_allocateBatches_depth (N : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (duration : Resource.Event ShortDLP.CompiledMAU.Recycling.model → Nat)
    (path : (allocateBatches N base count).Path) :
    (allocateBatches N base count).depth duration path = 0 := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      change (allocateBatch base N).depth duration path.1 +
        (allocateBatches N (batch base N) count).depth duration path.2 = 0
      exact congrArg₂ (fun left right : Nat => left + right)
        (rsaRecyclingFrame_allocateBatch_depth base N duration path.1)
        (ih (batch base N) path.2)

/-- The real full preallocation uses zero quantum time and zero other event duration. -/
lemma rsaRecyclingFrame_allocate_depth (base : RuntimeCtx .quantum) (N count : Nat)
    (duration : Resource.Event ShortDLP.CompiledMAU.Recycling.model → Nat)
    (path : (allocate base N count).Path) :
    (allocate base N count).depth duration path = 0 := by
  change (allocateBatches N base count).depth duration path.1 + 0 = 0
  rw [rsaRecyclingFrame_allocateBatches_depth, Nat.add_zero]

end

end QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame

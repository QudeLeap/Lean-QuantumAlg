/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent

/-!
# Actual candidate-exponent caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- An actual mutable input avoids every differently named mutable destination. -/
theorem mutable_avoids (refs : Refs ctx width) (separation : Separation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (saved written : MutableCell)
    (sourceKey : source.key = mutableKey refs saved) (different : saved ≠ written) :
    mutableKey refs written ∉ (writeInput source).storageKeys := by
  change mutableKey refs written ∉ [source.key]
  simp only [List.mem_singleton]
  rw [sourceKey]
  intro equal
  exact different (separation.mutableKeyInjective equal.symm)

/-- One actual native write retains a distinct original mutable value. -/
theorem mutable_read_apply (refs : Refs ctx width) (separation : Separation refs)
    {inputShape outputShape shape : CShape} (op : ClassicalOp inputShape outputShape ctx ctx)
    (written : MutableCell) (outputKey : op.outputRef.key = mutableKey refs written)
    (source : CWriteRef ctx shape) (saved : MutableCell)
    (sourceKey : source.key = mutableKey refs saved) (different : saved ≠ written)
    (store : Store ctx) :
    (store.applyOp op).read (writeInput source) = store.read (writeInput source) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  rw [outputKey]
  exact mutable_avoids refs separation source saved written sourceKey different

/-- One actual native write retains each original candidate or constant source input. -/
theorem source_read_apply (refs : Refs ctx width) (separation : Separation refs)
    {inputShape outputShape : CShape} (op : ClassicalOp inputShape outputShape ctx ctx)
    (written : MutableCell) (outputKey : op.outputRef.key = mutableKey refs written)
    (source : SourceCell) (store : Store ctx) :
    (store.applyOp op).read (sourceInput refs source) = store.read (sourceInput refs source) := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  rw [outputKey]
  exact separation.sourceAvoidsMutable source written

/-- The original exponent copy and four Boolean destinations form the suffix write footprint. -/
def SuffixFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.exponent.key ∉ other.storageKeys → refs.positive.key ∉ other.storageKeys →
      refs.belowUpper.key ∉ other.storageKeys → refs.nonnegative.key ∉ other.storageKeys →
        refs.accepted.key ∉ other.storageKeys → after.read other = before.read other

/-- All seven actual suffix instructions preserve reads outside their five original destinations. -/
theorem suffixInto_callerFrame (refs : Refs ctx width) (store : Store ctx) :
    SuffixFrame refs store (suffixStore refs store) := by
  intro shape other exponent positive below nonnegative accepted
  unfold suffixStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ accepted,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ accepted,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ nonnegative,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ below,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ positive,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ positive,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ exponent]

/-- Every original source word survives actual signed normalization. -/
theorem normalize_source_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (source : SourceCell) :
    (normalizeStep refs store).1.read (sourceInput refs source) =
      store.read (sourceInput refs source) :=
  normalizeMagnitude_callerFrame (candidateInput refs) refs.negative refs.magnitude store _
    (separation.sourceAvoidsMutable source .negative)
    (separation.sourceAvoidsMutable source .magnitude)

/-- Actual suffix execution retains the selected original normalized magnitude. -/
theorem suffix_magnitude_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (suffixStore refs store).read (writeInput refs.magnitude) =
      store.read (writeInput refs.magnitude) :=
  suffixInto_callerFrame refs store (writeInput refs.magnitude)
    (mutable_avoids refs separation refs.magnitude .magnitude .exponent rfl (by decide))
    (mutable_avoids refs separation refs.magnitude .magnitude .positive rfl (by decide))
    (mutable_avoids refs separation refs.magnitude .magnitude .belowUpper rfl (by decide))
    (mutable_avoids refs separation refs.magnitude .magnitude .nonnegative rfl (by decide))
    (mutable_avoids refs separation refs.magnitude .magnitude .accepted rfl (by decide))

/-- Actual suffix execution retains the real sign produced by normalization. -/
theorem suffix_negative_frame (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (suffixStore refs store).read (writeInput refs.negative) =
      store.read (writeInput refs.negative) :=
  suffixInto_callerFrame refs store (writeInput refs.negative)
    (mutable_avoids refs separation refs.negative .negative .exponent rfl (by decide))
    (mutable_avoids refs separation refs.negative .negative .positive rfl (by decide))
    (mutable_avoids refs separation refs.negative .negative .belowUpper rfl (by decide))
    (mutable_avoids refs separation refs.negative .negative .nonnegative rfl (by decide))
    (mutable_avoids refs separation refs.negative .negative .accepted rfl (by decide))

/-- Reads outside the seven actual destinations form the complete original caller frame. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

/-- Actual direct sign extraction, magnitude selection and range tests preserve all caller reads. -/
theorem candidateExponentInto_callerFrame (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (exponentStep refs store).1 := by
  intro shape other avoids
  change (suffixStore refs (normalizeStep refs store).1).read other = _
  rw [suffixInto_callerFrame refs _ other (avoids .exponent) (avoids .positive)
    (avoids .belowUpper) (avoids .nonnegative) (avoids .accepted)]
  exact normalizeMagnitude_callerFrame (candidateInput refs) refs.negative refs.magnitude
    store other
    (avoids .negative) (avoids .magnitude)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

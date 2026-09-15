/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Util.Classical.OrderRecovery
import Mathlib.Data.Vector.Basic

/-!
# Mathematical source readout of the actual stored Shor tuples

The source's sampled index and measured phase are recovered from their exact
stored bit conventions. The existing big-endian finite-word identity proves
that this is a left inverse of the source encoding. This readout is used only
to identify probabilities and supported source inputs; the native circuit
continues to read its actual parameter and phase cells through native recovery.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeSourceReadout

noncomputable section

/-- Read the original random sample and terminal outcome in their actual stored conventions. -/
def outcome (N : Nat) (value : (NativeIteration.resultShape N).Value) : SourceOutcome N :=
  match value with
  | .product (.bits sample) (.product _parameter (.bits phase)) =>
      ⟨ClassicalAlgorithms.OrderRecovery.fullRegisterIndex sample, phase⟩

/-- The same original source outcome is recovered from its complete actual stored tuple. -/
theorem outcome_sourceValue {N : Nat} (source : Input N) (sampled : SourceOutcome N) :
    outcome N (NativeBatch.sourceValue source sampled) = sampled := by
  cases sampled with
  | mk sample phase =>
      exact congrArg (fun value => (⟨value, phase⟩ : SourceOutcome N))
        (ClassicalAlgorithms.OrderRecovery.fullRegisterIndex_terminalMeasurement
          (residueSamplingBits N) sample)

/-- The complete source vector encoded in the genuine retained tuple shape. -/
def encoding {N : Nat} (source : Input N) {count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    (CShape.fixedVector count (NativeIteration.resultShape N)).Value :=
  .fixedVector (fun index => NativeBatch.sourceValue source (samples.get index))

/-- Mathematical source readout preserves the actual original finite ordering. -/
def outcomes (N count : Nat)
    (value : (CShape.fixedVector count (NativeIteration.resultShape N)).Value) :
    List.Vector (SourceOutcome N) count :=
  List.Vector.ofFn (fun index => outcome N (value.get index))

/-- Every actual source tuple vector retains the complete original source vector without loss. -/
theorem outcomes_encoding {N : Nat} (source : Input N) {count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    outcomes N count (encoding source samples) = samples := by
  apply List.Vector.ext
  intro index
  change (List.Vector.ofFn (fun position : Fin count =>
    outcome N (NativeBatch.sourceValue source (samples.get position)))).get index = _
  rw [List.Vector.get_ofFn]
  exact outcome_sourceValue source (samples.get index)

/-- Encoding the mathematical readout again preserves every value in the source image. -/
theorem encoding_outcomes_source {N : Nat} (source : Input N) {count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    encoding source (outcomes N count (encoding source samples)) = encoding source samples :=
  congrArg (encoding source) (outcomes_encoding source samples)

/-- The actual tuple-vector encoding cannot merge two distinct source transcripts. -/
theorem encoding_injective {N : Nat} (source : Input N) (count : Nat) :
    Function.Injective (encoding source (count := count)) :=
  fun _ _ same => (outcomes_encoding source _).symm.trans
    ((congrArg (outcomes N count) same).trans (outcomes_encoding source _))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeSourceReadout

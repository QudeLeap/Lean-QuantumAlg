/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Partition
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Chronology
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Vector

/-!
# Original current digits after earlier mathematical source segments are consumed

Only the already consumed chronological prefix is cleared in the same
mathematical paired source. Its current digit and complete unconsumed
suffix are the original ones. Feeding a zero physical bank consumes that
current segment and yields the next chronological remainder. The generic
segment calculation allows all widths to be zero. No physical register,
executed overwrite, gate, input-domain restriction or new preparation is
introduced by these mathematical labels.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

private def keepLow (full remaining : Nat) (within : remaining ≤ full)
    (label : Fin (2 ^ full)) : Fin (2 ^ full) :=
  ⟨label.val % 2 ^ remaining, (Nat.mod_lt _ (Nat.two_pow_pos remaining)).trans_le
    (Nat.pow_le_pow_right Nat.zero_lt_two within)⟩

private lemma keepLow_value (full remaining : Nat) (within : remaining ≤ full)
    (label : Fin (2 ^ full)) :
    (keepLow full remaining within label).val = label.val % 2 ^ remaining := rfl

private lemma pair_value {before after : Nat}
    (pair : Fin (2 ^ before) × Fin (2 ^ after)) :
    (prodEquiv pair).val = pair.2.val + 2 ^ after * pair.1.val := rfl

private lemma pairedLabel_value (bits width : Nat) (widths : width = bits + bits)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    (pairedLabelEquiv bits width widths branch).val =
      (prodEquiv (m := bits) (n := bits) branch).val := rfl

attribute [local irreducible] keepLow prodEquiv pairedLabelEquiv

private lemma segment_current_value (before active later : Nat)
    (label : (Qubits (before + (active + later))).Index) :
    (segmentPartition before active later label).1.val =
      label.val % 2 ^ (active + later) / 2 ^ later := by
  change ((prodEquiv (m := active) (n := later)).symm
    ((prodEquiv (m := before) (n := active + later)).symm label).2).1.val = _
  rw [prodEquiv_symm_fst_val, prodEquiv_symm_snd_val]

private lemma segment_before_value (before active later : Nat)
    (label : (Qubits (before + (active + later))).Index) :
    (segmentPartition before active later label).2.1.val =
      label.val / 2 ^ (active + later) := by
  change ((prodEquiv (m := before) (n := active + later)).symm label).1.val = _
  exact prodEquiv_symm_fst_val label

private lemma segment_later_value (before active later : Nat)
    (label : (Qubits (before + (active + later))).Index) :
    (segmentPartition before active later label).2.2.val =
      (label.val % 2 ^ (active + later)) % 2 ^ later := by
  change ((prodEquiv (m := active) (n := later)).symm
    ((prodEquiv (m := before) (n := active + later)).symm label).2).2.val = _
  rw [prodEquiv_symm_snd_val, prodEquiv_symm_snd_val]

private lemma segment_zero_value (before active later : Nat)
    (saved : ((Qubits before).prod (Qubits later)).Index) :
    ((segmentPartition before active later).symm
      ((0 : (Qubits active).Index), saved)).val =
      saved.2.val + 2 ^ (active + later) * saved.1.val := by
  rcases saved with ⟨first, last⟩
  rw [segmentPartition_symm, pair_value, pair_value, Fin.val_zero,
    Nat.mul_zero, Nat.add_zero]

attribute [local irreducible] segmentPartition

private lemma keepLow_current (before active later : Nat)
    (label : (Qubits (before + (active + later))).Index) :
    (segmentPartition before active later
      (keepLow (before + (active + later)) (active + later) (by omega) label)).1 =
        (segmentPartition before active later label).1 := by
  apply Fin.ext
  rw [segment_current_value, segment_current_value, keepLow_value, Nat.mod_mod]

private lemma keepLow_consume (before active later : Nat)
    (label : (Qubits (before + (active + later))).Index) :
    (segmentPartition before active later).symm
        (0, (segmentPartition before active later
          (keepLow (before + (active + later)) (active + later) (by omega) label)).2) =
      keepLow (before + (active + later)) later (by omega) label := by
  let retained := keepLow (before + (active + later)) (active + later) (by omega) label
  have prefixZero : (segmentPartition before active later retained).2.1 = 0 := by
    apply Fin.ext
    rw [segment_before_value, keepLow_value, Fin.val_zero]
    exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
  have suffixSame : (segmentPartition before active later retained).2.2.val =
      label.val % 2 ^ later := by
    rw [segment_later_value, keepLow_value, Nat.mod_mod]
    apply Nat.mod_mod_of_dvd
    rw [pow_add]
    exact dvd_mul_left _ _
  apply Fin.ext
  rw [segment_zero_value, prefixZero, Fin.val_zero, Nat.mul_zero,
    Nat.add_zero, keepLow_value]
  exact suffixSame

private def pairedRemaining (bits consumed : Nat)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    ((Qubits bits).prod (Qubits bits)).Index :=
  (prodEquiv (m := bits) (n := bits)).symm
    (keepLow (bits + bits) (bits + bits - consumed) (Nat.sub_le _ _)
      (prodEquiv (m := bits) (n := bits) branch))

private lemma pairedRemaining_value (bits consumed : Nat)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    (prodEquiv (m := bits) (n := bits) (pairedRemaining bits consumed branch)).val =
      (prodEquiv (m := bits) (n := bits) branch).val % 2 ^ (bits + bits - consumed) := by
  rw [pairedRemaining, Equiv.apply_symm_apply, keepLow_value]

attribute [local irreducible] pairedRemaining

private lemma pairedRemaining_initial (bits : Nat)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    pairedRemaining bits 0 branch = branch := by
  apply (prodEquiv (m := bits) (n := bits)).injective
  apply Fin.ext
  rw [pairedRemaining_value, Nat.sub_zero,
    Nat.mod_eq_of_lt (prodEquiv (m := bits) (n := bits) branch).isLt]

private lemma pairedRemaining_terminal (bits : Nat)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    pairedRemaining bits (bits + bits) branch = (0, 0) := by
  apply (prodEquiv (m := bits) (n := bits)).injective
  apply Fin.ext
  rw [pairedRemaining_value, Nat.sub_self, pow_zero, Nat.mod_one, pair_value]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]

private lemma pairedRemaining_second (bits : Nat)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    pairedRemaining bits bits branch = (0, branch.2) := by
  apply (prodEquiv (m := bits) (n := bits)).injective
  apply Fin.ext
  have remainder : bits + bits - bits = bits := by omega
  rw [pairedRemaining_value, remainder, pair_value, pair_value, Fin.val_zero,
    Nat.mul_zero, Nat.add_zero, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt branch.2.isLt]

private lemma pairedRemaining_label (bits before active later : Nat)
    (widths : before + (active + later) = bits + bits)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    pairedLabelEquiv bits _ widths (pairedRemaining bits before branch) =
      keepLow (before + (active + later)) (active + later) (by omega)
        (pairedLabelEquiv bits _ widths branch) := by
  apply Fin.ext
  rw [pairedLabel_value, pairedRemaining_value, keepLow_value, pairedLabel_value]
  have remainder : bits + bits - before = active + later := by omega
  rw [remainder]

private lemma pairedRemaining_current (bits before active later : Nat)
    (widths : before + (active + later) = bits + bits)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    (segmentPartition before active later
      (pairedLabelEquiv bits _ widths (pairedRemaining bits before branch))).1 =
        (segmentPartition before active later (pairedLabelEquiv bits _ widths branch)).1 := by
  rw [pairedRemaining_label]
  exact keepLow_current before active later _

private lemma pairedRemaining_consume (bits before active later : Nat)
    (widths : before + (active + later) = bits + bits)
    (branch : ((Qubits bits).prod (Qubits bits)).Index) :
    (segmentPartition before active later).symm
        (0, (segmentPartition before active later
          (pairedLabelEquiv bits _ widths (pairedRemaining bits before branch))).2) =
      pairedLabelEquiv bits _ widths (pairedRemaining bits (before + active) branch) := by
  rw [pairedRemaining_label]
  refine (keepLow_consume before active later _).trans ?_
  apply Fin.ext
  rw [keepLow_value, pairedLabel_value, pairedLabel_value, pairedRemaining_value]
  have remainder : bits + bits - (before + active) = later := by omega
  rw [remainder]

/-- The same paired source, with only its earlier chronological segments set to zero. -/
def remainingSource (consumed : Nat) (branch : SourceRegister.Index) : SourceRegister.Index :=
  pairedRemaining 260 consumed branch

/-- Before the first high generator tail, the complete original source remains unchanged. -/
lemma remainingSource_initial (branch : SourceRegister.Index) :
    remainingSource 0 branch = branch := pairedRemaining_initial 260 branch

/-- Consuming both original streams gives their actual same-carrier zero label. -/
lemma remainingSource_terminal (branch : SourceRegister.Index) :
    remainingSource 520 branch = (0, 0) := pairedRemaining_terminal 260 branch

/-- The generator stream is consumed before the complete original target-inverse stream. -/
lemma remainingSource_between_streams (branch : SourceRegister.Index) :
    remainingSource 260 branch = (0, branch.2) := pairedRemaining_second 260 branch

/-- The actual high target-inverse tail starts at precisely the original stream boundary. -/
lemma remainingSource_target_start (branch : SourceRegister.Index) :
    remainingSource (chronologicalIndex ((0 : Fin 17).natAdd 17)).sourceStart branch =
      (0, branch.2) := by
  rw [chronologicalIndex_second]
  change remainingSource 260 branch = (0, branch.2)
  exact remainingSource_between_streams branch

variable {ctx : RuntimeCtx .quantum}

namespace Parameters

/-- Clearing the earlier source prefix leaves this same original current digit intact. -/
lemma remainingSource_current (parameters : Parameters ctx) (index : WindowIndex)
    (branch : SourceRegister.Index) :
    (parameters.sourcePartition index (remainingSource index.sourceStart branch)).1 =
      (parameters.sourcePartition index branch).1 := by
  rw [parameters.sampling_source_partition_selected,
    parameters.sampling_source_partition_selected]
  exact pairedRemaining_current 260 index.sourceStart (index.lowerWidth + 1)
    index.sourceAfter index.windowIndex_sourceWidths branch

/-- Replacing the consumed current source block by zero gives precisely the next remainder. -/
lemma remainingSource_consume (parameters : Parameters ctx) (index : WindowIndex)
    (branch : SourceRegister.Index) :
    (parameters.sourcePartition index).symm
        (0, (parameters.sourcePartition index (remainingSource index.sourceStart branch)).2) =
      remainingSource index.sourceEnd branch := by
  apply (sourceLabelEquiv index).injective
  rw [parameters.sampling_source_partition_replace]
  exact pairedRemaining_consume 260 index.sourceStart (index.lowerWidth + 1)
    index.sourceAfter index.windowIndex_sourceWidths branch

/-- The actual selected mathematical feed consumes the original current block on a zero bank. -/
lemma sourceFeed_remaining (parameters : Parameters ctx) (index : WindowIndex)
    (Reference : Register) (physical : ctx.register.Index) (branch : SourceRegister.Index)
    (reference : Reference.Index)
    (zero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits physical).1 = Partner.zeroBits (index.lowerWidth + 1)) :
    (selectedFeedBasis (parameters.ports index) (parameters.sourcePartition index) Reference
      (physical, remainingSource index.sourceStart branch, reference)).2.1 =
        remainingSource index.sourceEnd branch := by
  dsimp only [selectedFeedBasis]
  rw [zero, window_source_binary_zero]
  exact parameters.remainingSource_consume index branch

/-- The original schedule's next high-to-low window receives this same mathematical remainder. -/
lemma sourceFeed_remaining_next (parameters : Parameters ctx) (position : Fin 33)
    (Reference : Register) (physical : ctx.register.Index) (branch : SourceRegister.Index)
    (reference : Reference.Index)
    (zero : (bankCoordinates (parameters.ports (chronologicalIndex position.castSucc)).wires
      (parameters.ports (chronologicalIndex position.castSucc)).qubits physical).1 =
        Partner.zeroBits ((chronologicalIndex position.castSucc).lowerWidth + 1)) :
    (selectedFeedBasis (parameters.ports (chronologicalIndex position.castSucc))
      (parameters.sourcePartition (chronologicalIndex position.castSucc)) Reference
        (physical, remainingSource (chronologicalIndex position.castSucc).sourceStart branch,
          reference)).2.1 =
      remainingSource (chronologicalIndex position.succ).sourceStart branch := by
  rw [sampling_chronological_source_next]
  exact parameters.sourceFeed_remaining _ Reference physical branch reference zero

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

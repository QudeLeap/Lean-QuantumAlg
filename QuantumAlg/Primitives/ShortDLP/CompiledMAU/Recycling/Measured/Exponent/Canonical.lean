/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Feedback.Chronological

/-!
# Original chronological exponent sources independent of every old Store

Powers retain their original MSB addresses. The source product uses the
original earlier-bit phase scalars and transports the same complete unit and
reference matrix throughout. The actual paid feedback prefix is proved equal
to this product from its real writes [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits tupleCoordinates)

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]
  (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool) {bits : Nat}

/-- The original position's full reference-extended half-sum, with record-selected paid phase. -/
def canonicalStageSource (Reference : Register) (record : Fin bits → Fin 2)
    (position : Fin bits) :
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) :=
  sourceWithReference
    (Recycling.ControlKraus.halfSum
      (unitTranslation modulus (unit ^ (2 ^ position.rev.val)) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat))
      (recordFeedbackScalar inverse record position position.val le_rfl) (record position))
      Reference

/-- Chronological products apply the head first and preserve the complete same posterior. -/
def canonicalExponentSource (Reference : Register) (record : Fin bits → Fin 2) :
    (remaining position : Nat) → position + remaining ≤ bits →
      HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)
  | 0, _, _ => 1
  | remaining + 1, position, bounded =>
      canonicalExponentSource Reference record remaining (position + 1) (by omega) *
        canonicalStageSource modulus unit inverse Reference record ⟨position, by omega⟩

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell : Nat)

private abbrev CanonicalCtx (width : Nat) := context base noQuantum m ell width

variable (selection : Fin bits → Fin (resultBits m ell))
  (separate : Function.Injective selection)

include separate

private lemma canonical_stage_prefix (Reference : Register) (record : Fin bits → Fin 2)
    (original : Store (CanonicalCtx base noQuantum m ell width)) (position : Fin bits) :
    stageSourceKraus base noQuantum m ell width modulus inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) unit position
        Reference
        (Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
          (fun index => .finite (record index)) original position.val
          (Nat.le_of_lt position.isLt)) (record position) =
      canonicalStageSource modulus unit inverse Reference record position := by
  unfold stageSourceKraus
  rw [feedbackScalar_after_prefix base noQuantum m ell width inverse selection separate]
  rfl

/-- Every actual source suffix uses exactly its original measured-prefix phase product. -/
lemma exponentReadoutSource_prefix (Reference : Register) (record : Fin bits → Fin 2)
    (original : Store (CanonicalCtx base noQuantum m ell width))
    (remaining position : Nat) (bounded : position + remaining ≤ bits) :
    exponentReadoutSource base noQuantum m ell width modulus unit inverse selection Reference
        remaining position bounded
        (Store.writePrefix (fun index => resultCell base noQuantum m ell width (selection index))
          (fun index => .finite (record index)) original position (by omega))
        (readoutTail record remaining position bounded) =
      canonicalExponentSource modulus unit inverse Reference record remaining position bounded := by
  induction remaining generalizing position with
  | zero => rfl
  | succ remaining induction =>
      rw [exponentReadoutSource, readoutTail]
      have next := induction (position + 1) (by omega)
      change _ * _ = _ * _
      apply congrArg₂ (fun left right :
        HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) => left * right)
      · exact next
      · exact canonical_stage_prefix modulus unit inverse base noQuantum m ell selection separate
          Reference record original ⟨position, by omega⟩

/-- The full source is independent of arbitrary old output values and unrelated Store contents. -/
lemma exponentReadoutSource_canonical (Reference : Register)
    (original : Store (CanonicalCtx base noQuantum m ell width)) (outcome : Bits bits) :
    exponentReadoutSource base noQuantum m ell width modulus unit inverse selection Reference bits
        0 (by omega) original outcome =
      canonicalExponentSource modulus unit inverse Reference (tupleCoordinates bits outcome) bits
        0 (by omega) := by
  have whole := exponentReadoutSource_prefix modulus unit inverse base noQuantum m ell selection
    separate Reference (tupleCoordinates bits outcome) original bits 0 (by omega)
  simpa only [readoutTail_all, Store.writePrefix] using whole

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

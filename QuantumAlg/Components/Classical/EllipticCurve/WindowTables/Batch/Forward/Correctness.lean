/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Forward.Preservation
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Arithmetic
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant
import all QuantumAlg.Util.Classical.Modular.BatchInverse

/-!
# Actual forward batch products and saved field prefixes

An indexed invariant follows the literal chronological Store record. The
actual loaded modulus and original denominator reads are retained; each
paid scalar multiply extends the canonical field product and the preceding
paid D write saves its original prefix. The identity row is never visited.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- Original field values and actual retained cells after a declared number of prefix steps. -/
structure ForwardInvariant (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (original : Store ctx) (values : Nat → ZMod spec.modulus)
    (processed : Nat) (current : Store ctx) : Prop where
  modulus : current.read frame.modulus = .unsignedWord spec.extendedWord
  denominators : ∀ index, current.read (rowRead frame.denominators index) =
    original.read (rowRead frame.denominators index)
  product : ((current.read (wordRead frame.work.product)).toNat : ZMod spec.modulus) =
    BatchInverse.prefixProduct values processed
  productCanonical : (current.read (wordRead frame.work.product)).toNat < spec.modulus
  prefixes : ∀ index : Fin length, 1 ≤ index.val → index.val ≤ processed →
    ((current.read (rowRead frame.prefixes index)).toNat : ZMod spec.modulus) =
      BatchInverse.prefixProduct values (index.val - 1)

end

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- The real prefix write and multiply advance the complete field/store invariant. -/
lemma ForwardInvariant.advance (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (original : Store ctx) (values : Nat → ZMod spec.modulus)
    {processed : Nat} (index : Fin length) (indexAt : index.val = processed + 1)
    (prefixModulusFree : frame.prefixes.key ∉ frame.modulus.storageKeys)
    (productModulusFree : frame.work.product.key ∉ frame.modulus.storageKeys)
    (valueAt : ((original.read (rowRead frame.denominators index)).toNat :
      ZMod spec.modulus) = values processed)
    (current : Store ctx) (before : ForwardInvariant frame spec original values processed current) :
    ForwardInvariant frame spec original values (processed + 1)
      (frame.forwardRecord (model := model) index current).1 := by
  constructor
  · exact (forwardRecord_read_other frame index frame.modulus prefixModulusFree
      productModulusFree current).trans before.modulus
  · intro observed
    exact (frame.forwardRecord_read_denominator index observed current).trans
      (before.denominators observed)
  · rw [frame.forwardRecord_read_product index prefixModulusFree current, before.modulus,
      multiplyValue_cast, before.product, before.denominators index, valueAt]
    rfl
  · rw [frame.forwardRecord_read_product index prefixModulusFree current, before.modulus]
    exact multiplyValue_canonical spec _ _
  · intro observed positive within
    by_cases same : observed = index
    · subst observed
      rw [frame.forwardRecord_read_prefix index current, before.product, indexAt,
        Nat.add_sub_cancel]
    · rw [frame.forwardRecord_read_other_prefix index observed same current]
      exact before.prefixes observed positive (by
        have different : observed.val ≠ index.val := fun equal => same (Fin.ext equal)
        omega)

/-- The complete actual forward pass stores all original field prefixes and their product. -/
lemma forwardPassRecord_values (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
    [Fact spec.modulus.Prime] (count : Nat) (fits : count < length)
    (prefixModulusFree : frame.prefixes.key ∉ frame.modulus.storageKeys)
    (productModulusFree : frame.work.product.key ∉ frame.modulus.storageKeys)
    (values : Nat → ZMod spec.modulus) (store : Store ctx)
    (loaded : store.read frame.modulus = .unsignedWord spec.extendedWord)
    (one : (store.read (wordRead frame.work.product)).toNat = 1)
    (represented : ∀ index : Fin count,
      ((store.read (rowRead frame.denominators ⟨index.val + 1, by omega⟩)).toNat :
        ZMod spec.modulus) = values index.val) :
    ForwardInvariant frame spec store values count
      (frame.forwardPassRecord (model := model) count fits store).1 := by
  have initial : ForwardInvariant frame spec store values 0 store := by
    constructor
    · exact loaded
    · intro index
      rfl
    · rw [one]
      simp only [Nat.cast_one, BatchInverse.prefixProduct]
    · rw [one]
      exact modulusSpec_one_lt spec
    · intro index positive within
      omega
  exact Circuit.forRangeStoreRecord_invariant count
    (fun index => frame.forwardStep (model := model) ⟨index.val + 1, by omega⟩)
    (fun index => frame.forwardRecord (model := model) ⟨index.val + 1, by omega⟩)
    (fun processed current => ForwardInvariant frame spec store values processed current)
    (fun index current established => ForwardInvariant.advance frame spec store values
      ⟨index.val + 1, by omega⟩ rfl prefixModulusFree productModulusFree (represented index)
      current established) store initial

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

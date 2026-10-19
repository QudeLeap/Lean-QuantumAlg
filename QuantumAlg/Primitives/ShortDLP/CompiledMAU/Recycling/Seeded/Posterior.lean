/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Seeded
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Core.Execution.Basis.Reference
import Mathlib.Data.Complex.BigOperators

/-!
# Complete seeded posterior and its reference contraction

The density is derived from each complete Store of the actual supplied state.
Every partner row and both reference coordinates remain in the conditional
matrix. Only its explicitly stated partial trace contracts the partner; no
equality of different physical banks or initialization certificate is assumed.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.SeededPosterior

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution
open QuantumFourierTransform.Semiclassical (frequencyBits)
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (m ell width : Nat) (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- The exact squared norm of the actual compiled branch's unit-one column. -/
def branchWeight (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) : ℝ :=
  ∑ value : (Carrier.units modulus.val).Index,
    ‖FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
      first second value 1‖ ^ 2

/-- All entries of the full conditional partner/reference matrix use the actual Store density. -/
lemma actualSigma_seed_entry {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (left right : (Carrier.units modulus.val).Index) (leftRef rightRef : Reference.Index) :
    FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator target
      first second Reference
        (FullWordSeeded.seedDensity width modulus state original).matrix
          (left, leftRef) (right, rightRef) =
      FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
        first second left 1 *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef *
        star (FullWordCircuit.actualKraus (environment := environment) m ell width modulus
          generator target first second
          right 1) :=
  FullWordSeeded.tensor_seed_entry
    (FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
      first second)
    (1 : (Carrier.units modulus.val).Index)
    (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal
    left right leftRef rightRef

/-- The real recycled member keeps exactly that complete posterior at canonical frequencies. -/
lemma memberSigma_seed_entry
    (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum m ell width) Reference History)
    (original : Store (context base noQuantum m ell width))
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (left right : (Carrier.units modulus.val).Index) (leftRef rightRef : Reference.Index) :
    MemberInstrument.memberSigma base noQuantum m ell width modulus generator target Reference
        original (frequencyBits (ell + m) first, frequencyBits ell second)
        (FullWordSeeded.seedDensity width modulus state original).matrix
          (left, leftRef) (right, rightRef) =
      FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator target
        first second left 1 *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef *
        star (FullWordCircuit.actualKraus (environment := environment) m ell width modulus
          generator target first second
          right 1) := by
  rw [← FullWordCircuit.actualSigma_eq_memberSigma m ell width modulus nontrivial fits
    base noQuantum generator target Reference original first second]
  exact actualSigma_seed_entry m ell width modulus state original generator target
    first second left right leftRef rightRef

/-- Partial trace of the full posterior retains both Reference coordinates and its Store mass. -/
lemma actualSigma_reference_entry {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (leftRef rightRef : Reference.Index) :
    (∑ value : (Carrier.units modulus.val).Index,
      FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator target
        first second Reference
        (FullWordSeeded.seedDensity width modulus state original).matrix
          (value, leftRef) (value, rightRef)) =
      (branchWeight (environment := environment) m ell width modulus generator target first second
        : ℂ) *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef := by
  have entries :
      (∑ value : (Carrier.units modulus.val).Index,
        FullWordCircuit.actualSigma (environment := environment) m ell width modulus generator
          target first second Reference
          (FullWordSeeded.seedDensity width modulus state original).matrix
            (value, leftRef) (value, rightRef)) =
        ∑ value : (Carrier.units modulus.val).Index,
          FullWordCircuit.actualKraus (environment := environment) m ell width modulus generator
            target first second value 1 *
            (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
              leftRef rightRef *
            star (FullWordCircuit.actualKraus (environment := environment) m ell width modulus
              generator target first second
              value 1) := by
    exact Finset.sum_congr rfl fun value _ =>
      actualSigma_seed_entry m ell width modulus state original generator target
        first second value value leftRef rightRef
  refine entries.trans ?_
  simp only [branchWeight, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro value _
  let amplitude := FullWordCircuit.actualKraus (environment := environment) m ell width modulus
    generator target
    first second value 1
  have coefficient : amplitude * star amplitude = ((‖amplitude‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude
  change amplitude * _ * star amplitude = _
  rw [← coefficient]
  ring

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.SeededPosterior

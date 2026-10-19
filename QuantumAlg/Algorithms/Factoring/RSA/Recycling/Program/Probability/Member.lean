/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Reference
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Projection
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Seeded.Born
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Reference
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# The actual member kernel in the original terminal Born coordinates

The two chronological bit streams are decoded separately. Their exact finite
bijection preserves the source terminal convention, including empty streams.
The actual complete packed Store is retained in every weighted identity.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program.Probability

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open QuantumFourierTransform.Semiclassical ShortDLP.CompiledMAU.Recycling
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- The original terminal labels, with the two source widths fixed by the modulus. -/
abbrev Terminal (N : Nat) := Fin (measurementBits N) → Bool

/-- Decode the separately reversed streams into the original full-register terminal label. -/
def terminalEquiv (N : Nat) :
    (Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) ≃ Terminal N :=
  ((Equiv.prodCongr
      ((binaryEquiv (tradeoffBits N + shortLogBits N)).trans
        (qftReverseBitsPerm (tradeoffBits N + shortLogBits N)))
      ((binaryEquiv (tradeoffBits N)).trans (qftReverseBitsPerm (tradeoffBits N)))).trans
    prodEquiv).trans
      (Equiv.ofBijective
        (ShortDLP.BornProbability.shortDLPMeasurementOutcome
          (ShortDLP.CompiledMAU.registerParameters
            (shortLogBits N) (tradeoffBits N) (arithmeticBits N)))
        (ShortDLP.BornProbability.shortDLPMeasurementOutcome_bijective _))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The complete parameter read by the actual selected member. -/
def parameterRead (batch : Fin count) (stored : Store (readyContext base noQuantum N count)) :
    (ParameterShape N).Value :=
  stored.read (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
    (ClassicalFrame.parameterRef base N count batch)))

/-- The actual paid Store update at the uniquely determined chronological outcome. -/
def updateMember (batch : Fin count) (index : Fin 16)
    (terminal : Terminal N) (stored : Store (readyContext base noQuantum N count)) :
    Store (readyContext base noQuantum N count) :=
  PackedReference.packedStore (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.packedRef base N count batch index)) stored ((terminalEquiv N).symm terminal)

/-- One actual member preserves every complete parameter in the parent frame. -/
lemma updateMember_parameter (batch previous : Fin count) (index : Fin 16)
    (terminal : Terminal N) (stored : Store (readyContext base noQuantum N count)) :
    parameterRead base noQuantum N count previous
        (updateMember base noQuantum N count batch index terminal stored) =
      parameterRead base noQuantum N count previous stored :=
  rsaRecyclingParent_packedStore_parameter base noQuantum N count batch previous index stored _

/-- The actual branch mass is the unchanged ideal source PMF at that stored parameter. -/
lemma memberBornWeight_eq (input : Input N) (batch : Fin count)
    (stored : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) :
    memberBornWeight base noQuantum N count batch stored outcome =
      (selectedOutcomePMF (parameterRead base noQuantum N count batch stored)
        (terminalEquiv N outcome)).toReal := by
  have domain : 1 < N ∧ N < 2 ^ arithmeticBits N :=
    ⟨input.modulus_gt_one, modulus_lt_arithmeticCapacity N⟩
  have actual := ShortDLP.CompiledMAU.outcomePMF_eq_ideal
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (parameterRead base noQuantum N count batch stored))
    (parameterTarget (parameterRead base noQuantum N count batch stored)) domain.1 domain.2
  rw [selectedOutcomePMF, dif_pos domain]
  exact congrArg (fun distribution => (distribution (terminalEquiv N outcome)).toReal) actual

/-- Reindex the actual complete-Store kernel, without replacing its Store transition. -/
lemma memberReferenceKernel_terminal (input : Input N) (batch : Fin count) (index : Fin 16)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    memberReferenceKernel base noQuantum N count batch index weight stored =
      ∑ terminal : Terminal N,
        ((selectedOutcomePMF (parameterRead base noQuantum N count batch stored)
          terminal).toReal : ℂ) *
          weight (updateMember base noQuantum N count batch index terminal stored) := by
  have reindex := (terminalEquiv N).sum_comp (fun terminal =>
    ((selectedOutcomePMF (parameterRead base noQuantum N count batch stored)
      terminal).toReal : ℂ) *
      weight (updateMember base noQuantum N count batch index terminal stored))
  refine Eq.trans ?_ reindex
  unfold memberReferenceKernel
  apply Finset.sum_congr rfl
  intro outcome _
  rw [memberBornWeight_eq base noQuantum N count input]
  simp only [updateMember, Equiv.symm_apply_apply, mul_comm]

end

end QuantumAlg.Factoring.RSA.Recycling.Program.Probability

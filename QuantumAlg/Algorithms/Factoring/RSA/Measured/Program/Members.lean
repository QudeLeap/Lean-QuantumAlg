/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Member
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame.Composition

/-!
# All configured actual RSA members on one measured arithmetic bank

The public member count controls the real chronological circuit. Every
member receives the complete preceding posterior and its actual stored
parameter, writes the paid packed result and performs its complete restart
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Actual member kernels compose in their original increasing sample order. -/
def membersParentReferenceKernel (count : Nat) (batch : Fin count)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ) :
    Store (Recycling.ClassicalFrame.context base N count) → ℂ :=
  Circuit.forRangeReferenceKernel membersPerBatch
    (memberParentReferenceKernel base N count batch) weight

/-- All configured actual members retain the complete parent/reference conditional law. -/
lemma rsaMeasuredParent_members_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (count : Nat) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((members base noQuantum N input count batch).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => membersParentReferenceKernel base N count batch weight
          (parentStoreAt base noQuantum N count entry.1)) left right :=
  measuredForRange_parent_referenceFiberSum (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) membersPerBatch
    (member base noQuantum N input count batch) environment (memberSeed base noQuantum N count)
    (memberParentReferenceKernel base N count batch)
    (fun index _ _ _ state =>
      rsaMeasuredParent_member_seeded base noQuantum N input count batch index environment state)
    (fun index _ _ _ state seeded weight left right =>
      rsaMeasuredParent_member_parent_referenceFiberSum base noQuantum N input count batch index
        environment state seeded weight left right)
    state seeded weight left right

/-- Every chronological real member keeps the bank seed established by actual preparation. -/
lemma rsaMeasuredParent_members_seeded (input : Input N) (count : Nat) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((members base noQuantum N input count batch).execute environment Reference state) :=
  measuredForRange_seeded (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) membersPerBatch
    (member base noQuantum N input count batch) environment (memberSeed base noQuantum N count)
    (fun index _ _ _ state =>
      rsaMeasuredParent_member_seeded base noQuantum N input count batch index environment state)
    state seeded

end

end QuantumAlg.Factoring.RSA.Measured.Program

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Arithmetic

/-!
# Complete-reference composition at the five actual point records

The five components read the literal Store returned by their predecessor.
All original outcomes remain explicit. This internal composition law
combines component actions; concrete field and table proofs must supply
those actions before it can describe a point addition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Window.Sampling

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

attribute [local irreducible] InstrumentBranchAction referenceKet

private lemma branchAction_seq_power
    {First Second : Type} [Fintype First] [Fintype Second]
    {first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    (head : Execution.Instrument first First environment)
    (tail : Execution.Instrument second Second environment)
    (store : Store ctx) (firstOutcome : First) (secondOutcome : Second)
    (firstPower secondPower : Nat) (initial middle final : Window.Raw)
    {Reference : Register} (reference : Reference.Index)
    (headAction : parameters.InstrumentBranchAction (Reference := Reference)
      environment head store firstOutcome (NormalizedVector.invSqrt2 ^ firstPower)
      initial middle reference)
    (tailAction : parameters.InstrumentBranchAction (Reference := Reference)
      environment tail (head.record store firstOutcome).1 secondOutcome
      (NormalizedVector.invSqrt2 ^ secondPower) middle final reference) :
    parameters.InstrumentBranchAction (Reference := Reference) environment (head.seq tail)
      store (firstOutcome, secondOutcome)
      (NormalizedVector.invSqrt2 ^ (firstPower + secondPower)) initial final reference := by
  simpa only [← pow_add] using parameters.instrumentBranchAction_seq (Reference := Reference)
    environment head tail store firstOutcome secondOutcome
    (NormalizedVector.invSqrt2 ^ firstPower) (NormalizedVector.invSqrt2 ^ secondPower)
    initial middle final reference headAction tailAction

private def FivePointActions
    {A B C D E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    {a b c d e : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    (first : Execution.Instrument a A environment)
    (second : Execution.Instrument b B environment)
    (third : Execution.Instrument c C environment)
    (fourth : Execution.Instrument d D environment)
    (fifth : Execution.Instrument e E environment)
    (store : Store ctx) (pa : A) (pb : B) (pc : C) (pd : D) (pe : E)
    (initial one two three four final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) : Prop :=
  (parameters.InstrumentBranchAction (Reference := Reference)
      environment first store pa (NormalizedVector.invSqrt2 ^ 512) initial one reference) →
  (parameters.InstrumentBranchAction (Reference := Reference)
      environment second (first.record store pa).1 pb
      (NormalizedVector.invSqrt2 ^ 256) one two reference) →
  (parameters.InstrumentBranchAction (Reference := Reference)
      environment third (second.record (first.record store pa).1 pb).1 pc
      (NormalizedVector.invSqrt2 ^ 512) two three reference) →
  (parameters.InstrumentBranchAction (Reference := Reference)
      environment fourth
      (third.record (second.record (first.record store pa).1 pb).1 pc).1 pd
      (NormalizedVector.invSqrt2 ^ 256) three four reference) →
  (parameters.InstrumentBranchAction (Reference := Reference)
      environment fifth
      (fourth.record (third.record (second.record (first.record store pa).1 pb).1 pc).1 pd).1 pe
      (NormalizedVector.invSqrt2 ^ 512) four final reference) →
  parameters.InstrumentBranchAction (Reference := Reference)
      environment (first.seq (second.seq (third.seq (fourth.seq fifth))))
      store (pa, (pb, (pc, (pd, pe)))) (NormalizedVector.invSqrt2 ^ 2048)
      initial final reference

attribute [local irreducible] FivePointActions

/-- Each actual phase receives exactly its predecessor's returned Store. -/
lemma fivePointInstruments_branchAction
    {A B C D E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    {a b c d e : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx ctx false}
    (first : Execution.Instrument a A environment)
    (second : Execution.Instrument b B environment)
    (third : Execution.Instrument c C environment)
    (fourth : Execution.Instrument d D environment)
    (fifth : Execution.Instrument e E environment)
    (store : Store ctx) (pa : A) (pb : B) (pc : C) (pd : D) (pe : E)
    (initial one two three four final : Window.Raw)
    {Reference : Register} (reference : Reference.Index) :
    parameters.FivePointActions (Reference := Reference) environment
      first second third fourth fifth store pa pb pc pd pe
      initial one two three four final reference := by
  unfold FivePointActions
  intro firstAction secondAction thirdAction fourthAction fifthAction
  have lastTwo := parameters.branchAction_seq_power (Reference := Reference)
    environment fourth fifth
    (third.record (second.record (first.record store pa).1 pb).1 pc).1 pd pe
    256 512 three four final reference fourthAction fifthAction
  have lastThree := parameters.branchAction_seq_power (Reference := Reference)
    environment third (fourth.seq fifth)
    (second.record (first.record store pa).1 pb).1 pc (pd, pe)
    512 768 two three final reference thirdAction lastTwo
  have lastFour := parameters.branchAction_seq_power (Reference := Reference)
    environment second (third.seq (fourth.seq fifth))
    (first.record store pa).1 pb (pc, (pd, pe))
    256 1280 one two final reference secondAction lastThree
  exact parameters.branchAction_seq_power (Reference := Reference)
    environment first (second.seq (third.seq (fourth.seq fifth)))
    store pa (pb, (pc, (pd, pe)))
    512 1536 initial one final reference firstAction lastFour

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Window
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Inputs
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Action

/-!
# The actual chronological point action on every original good source branch

The prepared Store and original admissibility proof discharge the specified
named driver's hypotheses. The action keeps every outcome, the entire point
workspace, the remaining full source and an arbitrary reference.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open QuantumAlg.Execution.Instrument

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] PrimeFieldShortWeierstrass.Arithmetic.P256.modulus
  prefixAffine branchGood sourceFedRaw Driver.namedDriverKetAction

private lemma driverKetAction_spec {parameters : Driver.Parameters ctx}
    {frame : Outer.Frame ctx 256} {firstSpec lastSpec : ClassicalAlgorithms.Modular.ModulusSpec 256}
    (same : firstSpec = lastSpec) {row : Fin 34}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment} {before : Store ctx} {first last : Raw}
    {Reference : Register} {reference : Reference.Index}
    (action : Driver.namedDriverKetAction parameters frame firstSpec row environment before
      first last (Reference := Reference) reference) :
    Driver.namedDriverKetAction parameters frame lastSpec row environment before
      first last (Reference := Reference) reference := by
  cases same
  exact action

private lemma driverKetAction_raw {parameters : Driver.Parameters ctx}
    {frame : Outer.Frame ctx 256} {spec : ClassicalAlgorithms.Modular.ModulusSpec 256}
    {row : Fin 34}
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment} {before : Store ctx} {first last nextFirst nextLast : Raw}
    {Reference : Register} {reference : Reference.Index}
    (firstSame : first = nextFirst) (lastSame : last = nextLast)
    (action : Driver.namedDriverKetAction parameters frame spec row environment before
      first last (Reference := Reference) reference) :
    Driver.namedDriverKetAction parameters frame spec row environment before
      nextFirst nextLast (Reference := Reference) reference := by
  cases firstSame
  cases lastSame
  exact action

/-- The same actual named point driver advances one original admissible prefix. -/
private def PointPrefixActionStatement : Prop :=
  ∀ (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx)
    (_values : Driver.driverInputValues parameters.frame (actualCurveSpec I)
      (chronologicalBasePoint I position) (Sampling.chronologicalIndex position).row before)
    (Reference : Register) (reference : Reference.Index),
    let index := Sampling.chronologicalIndex position
    let first := prefixAffine I branch good position.val position.isLt.le
    let last := prefixAffine I branch good (position.val + 1) (Nat.succ_le_of_lt position.isLt)
    Driver.namedDriverKetAction (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row
      environment before
      (sourceFedRaw parameters index (sourceBranch I branch)
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          first (false, false, false) 0))
      (sourceFedRaw parameters index (sourceBranch I branch)
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          last (false, false, false) 0))
      (Reference := Reference) reference

/-- The same actual named point driver advances one original admissible prefix. -/
lemma point_prefix_action :
    PointPrefixActionStatement (ctx := ctx) (services := services) := by
  unfold PointPrefixActionStatement
  intro parameters I sameSpec scratch branch good position assigned environment before values
    Reference reference
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  intro index first last
  let fed := sourceFedRaw parameters index (sourceBranch I branch)
    (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
      first (false, false, false) 0)
  have currentGeometry := point_prefix_fed_geometry (ctx := ctx)
    parameters I branch good position
  have normal := fed_affine_normal parameters index (sourceBranch I branch)
    (actualCurveSpec I) (actualCurveSpec_modulus I) first
  have actionAtCurve := Driver.namedDriverInstrument_affine_action
    (ctx := ctx) (services := services) (Reference := Reference)
    (parameters.pointParameters index) parameters.frame scratch
    (fun bit => Fin.castLE index.lowCapacity bit) (Fin.castLE_injective index.lowCapacity) assigned
    (actualCurveSpec I) (actualCurveSpec_modulus I)
  have actionAtPoint := actionAtCurve (chronologicalBasePoint I position)
    index.row environment before values first last fed.1.2 fed.2 normal
  have actionAtOrder := actionAtPoint
    DomainParameters.subgroupOrder I.subgroupCert.prime subgroupOrder_large
    (chronologicalBasePoint_order I position)
    (windowTableFits (index.highRemaining + index.lowWidth) index.addressBound)
  have action := actionAtOrder (by
    change Driver.affineRowGeometry
      (Group := (DomainParameters.curve I.curveCert).MathlibPoint) _ _ _ _
    unfold fed first last index
    change Driver.affineRowGeometry
      (Group := (DomainParameters.curve I.curveCert).MathlibPoint) _ _ _ _ at currentGeometry
    generalize_proofs at currentGeometry ⊢
    exact currentGeometry) reference
  have actual := driverKetAction_spec sameSpec.symm action
  have firstSame := fed_affine_blank parameters index (sourceBranch I branch)
    (actualCurveSpec I) (actualCurveSpec_modulus I) first
  have lastSame := fed_affine_changePoint parameters index (sourceBranch I branch)
    (actualCurveSpec I) (actualCurveSpec_modulus I) first last
  exact driverKetAction_raw firstSame.symm lastSame.symm actual

/-- Every real point/Fourier outcome advances the good column with its original phase. -/
private def GoodWindowSourceKetStatement : Prop :=
  ∀ (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (_values : Driver.driverInputValues parameters.frame (actualCurveSpec I)
      (chronologicalBasePoint I position) (Sampling.chronologicalIndex position).row before)
    (Reference : Register) (reference : Reference.Index),
    let index := Sampling.chronologicalIndex position
    let first := prefixAffine I branch good position.val position.isLt.le
    let last := prefixAffine I branch good (position.val + 1) (Nat.succ_le_of_lt position.isLt)
    let firstRaw := Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
      first (false, false, false) 0
    let lastRaw := Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
      last (false, false, false) 0
    Sampling.sourceWindowKetAction parameters index environment before hidden
      (sourceBranch I branch) firstRaw lastRaw Reference reference

/-- Every real point/Fourier outcome advances the good column with its original phase. -/
lemma good_window_source_ket :
    GoodWindowSourceKetStatement (ctx := ctx) (services := services) := by
  unfold GoodWindowSourceKetStatement
  intro parameters I sameSpec scratch branch good position assigned environment before hidden values
    Reference reference index first last firstRaw lastRaw
  apply named_window_source_ket parameters index
    environment before hidden (sourceBranch I branch)
  · unfold firstRaw Driver.driverAffineBlank
    exact sourceBlank_zero_bank parameters index _ _
  · unfold lastRaw Driver.driverAffineBlank
    exact sourceBlank_zero_bank parameters index _ _
  · have pointAction := point_prefix_action parameters I sameSpec scratch branch good position
      assigned environment before values (Sampling.SourceRegister.prod Reference)
      (remainingSource (Sampling.chronologicalIndex position).sourceEnd (sourceBranch I branch),
        reference)
    unfold firstRaw lastRaw first last index
    change Driver.namedDriverKetAction (ctx := ctx) (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row
      environment before _ _ (Reference := Sampling.SourceRegister.prod Reference)
      (remainingSource index.sourceEnd (sourceBranch I branch), reference) at pointAction
    generalize_proofs at pointAction ⊢
    exact pointAction

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good

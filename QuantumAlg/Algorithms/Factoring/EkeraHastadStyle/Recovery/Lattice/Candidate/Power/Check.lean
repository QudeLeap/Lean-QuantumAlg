/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Construction
import all QuantumAlg.Components.Classical.Modular.NativePower.BodyExecution
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources

/-!
# Actual candidate-power verification with one lexical result

One fresh result word receives the existing expanded native modular power.
The next actual equality instruction compares that word with the original
stored target, and writes only the supplied decision bit. The result word is
released by its own lexical scope. Neither a zero destination nor spare keys
are required from the caller; all power initialization remains in the actual
modular-power construction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.PowerCheck

open Execution
open ClassicalRoutines.Modular
open ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}

/-- One actual fresh result word outside the modular-power component's own scratch. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The candidate power is stored in the actual new lexical head. -/
def result (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  .workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Original inputs remain structural reads below the actual result cell. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (context ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The comparison writes the original decision cell through the single actual scope. -/
def compareOp (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit
      (context ctx width) (context ctx width) :=
  .wordBinary .equal width (context ctx width)
    (.product (NativePower.wordRead (result ctx width)) (underRead target width))
    (decision.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh)

/-- Expanded real modular exponentiation followed by its actual word equality. -/
def body (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit) :
    Circuit (context ctx width) (context ctx width) :=
  .seq (NativePower.into spec (underRead base width) (underRead exponent width) (result ctx width))
    (.classical (compareOp target decision))

/-- The complete actual candidate-power check supplies and releases its own result word. -/
def circuit (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit) :
    Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (body spec base exponent target decision)

noncomputable section

/-- The actual body update includes the modular-power path and final comparison instruction. -/
def bodyStep (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (store : Store (context ctx width)) :
    Store (context ctx width) × (body spec base exponent target decision).Path :=
  let powered := NativePower.intoStep spec (underRead base width) (underRead exponent width)
    (result ctx width) store
  (powered.1.applyOp (compareOp target decision), (powered.2, ()))

/-- The actual result scope preserves the complete body path and only removes its own head. -/
def step (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx × (circuit spec base exponent target decision).Path :=
  let final := bodyStep spec base exponent target decision
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh final.1, final.2)

/-- Independent native coordinate allowance for expanded power and the one actual comparison. -/
def eventEnvelope (kind : ProblemKind) (width exponentWidth : Nat) : ResourcePool kind :=
  NativePower.eventEnvelope kind width exponentWidth +
    ResourcePool.singleton (.classicalOperation (.wordBinary .equal width))

/-- The actual lexical check charges every native power operation and its final comparison. -/
theorem nativeRecovery_powerCheck_pool_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (path : (circuit spec base exponent target decision).Path) :
    (circuit spec base exponent target decision).resourcePool path ≤
      eventEnvelope kind width exponentWidth := by
  change ResourcePool.ofList
    ((NativePower.into spec (underRead base width) (underRead exponent width)
      (result ctx width)).eventTrace path.1 ++
        [.classicalOperation (.wordBinary .equal width)]) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (NativePower.nativePower_into_pool_le spec (underRead base width) (underRead exponent width)
      (result ctx width) path.1) le_rfl

/-- Unit-duration depth includes the actual comparison after the complete native power. -/
theorem nativeRecovery_powerCheck_unitDepth_le (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (path : (circuit spec base exponent target decision).Path) :
    (circuit spec base exponent target decision).depth (fun _ => 1) path ≤
      2 * width + 6 + 6 * exponentWidth := by
  have actual := NativePower.nativePower_into_unitDepth_le spec (underRead base width)
    (underRead exponent width) (result ctx width) path.1
  change (NativePower.into spec (underRead base width) (underRead exponent width)
    (result ctx width)).depth (fun _ => 1) path.1 + 1 ≤ _
  omega

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.PowerCheck

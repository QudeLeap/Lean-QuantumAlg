/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Candidate.Power.Check
import all QuantumAlg.Components.Classical.Modular.NativePower.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Preservation
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Exact native candidate-power decision on the original stored operands

Fresh allocation makes the power result distinct from every original input.
The actual modular-power component overwrites that result without an initial
value premise. The following actual equality reads the preserved target and
returns exactly the source power predicate. The complete state equation and
borrowed restoration preserve arbitrary incoming quantum-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.PowerCheck

open Execution
open ClassicalRoutines.Modular
open ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}

/-- Every body block follows the actual native power and then the actual comparison store map. -/
theorem nativeRecovery_powerCheck_body_execute (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx width) Reference History) :
    (body spec base exponent target decision).execute Reference state =
      state.mapClassical (fun entry =>
        ((bodyStep spec base exponent target decision entry.1).1,
          (entry.2, (bodyStep spec base exponent target decision entry.1).2))) := by
  have composed :=
    Circuit.execute_seq_mapClassical
      (NativePower.into spec (underRead base width) (underRead exponent width) (result ctx width))
      (.classical (compareOp target decision))
      (NativePower.intoStep spec (underRead base width) (underRead exponent width)
        (result ctx width))
      (fun store => (store.applyOp (compareOp target decision), ()))
      (fun reference {_} _ initial => NativePower.nativePower_into_execute spec
        (underRead base width) (underRead exponent width) (result ctx width) reference initial)
      (fun reference {Past} _ initial => by
        refine (Circuit.execute_classical_mapClassical
          (compareOp target decision) reference initial).trans ?_
        exact congrArg
          (fun equality : DecidableEq (Store (context ctx width) × (Past × Unit)) =>
            @ExecutionState.mapClassical _ _ _ _
              (Register.prod (context ctx width).register reference) equality initial
              (fun entry => (entry.1.applyOp (compareOp target decision), (entry.2, ()))))
          (Subsingleton.elim _ _))
      Reference state
  refine composed.trans ?_
  exact congrArg
    (fun equality : DecidableEq
        (Store (context ctx width) × (History × (body spec base exponent target decision).Path)) =>
      @ExecutionState.mapClassical _ _ _ _
        (Register.prod (context ctx width).register Reference) equality state
        (fun entry =>
          ((bodyStep spec base exponent target decision entry.1).1,
            (entry.2, (bodyStep spec base exponent target decision entry.1).2))))
    (Subsingleton.elim _ _)

/-- The actual scope initializes and releases exactly the single candidate-power result. -/
theorem nativeRecovery_powerCheck_execute (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (circuit spec base exponent target decision).execute Reference state =
      state.mapClassical (fun entry =>
        ((step spec base exponent target decision entry.1).1,
          (entry.2, (step spec base exponent target decision entry.1).2))) :=
  Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (body spec base exponent target decision)
    (bodyStep spec base exponent target decision)
    (fun reference {_} _ initial =>
      nativeRecovery_powerCheck_body_execute spec base exponent target decision reference initial)
    Reference state

private theorem result_fresh {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    (result ctx width).key ∉ (underRead input width).storageKeys := by
  have keys := CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh
  intro present
  have original : ctx.canonicalFreshKey ∈ input.storageKeys :=
    (congrArg (fun storage => ctx.canonicalFreshKey ∈ storage) keys).mp present
  exact ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context original)

/-- The final decision is the source modular-power equality on the original target read. -/
theorem nativeRecovery_powerCheck_decision (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (store : Store ctx) (input : Pow.Input spec exponentWidth)
    (represented : NativePower.InputRepresents spec base exponent store input) :
    (((step spec base exponent target decision store).1).read
      (NativePower.wordRead decision)).toBool =
        decide (input.base.val ^ input.exponent.val % spec.modulus =
          (store.read target).toNat) := by
  let entered : Store (context ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let powered := NativePower.intoStep spec (underRead base width) (underRead exponent width)
    (result ctx width) entered
  have inherited : NativePower.InputRepresents spec (underRead base width)
      (underRead exponent width) entered input :=
    ⟨(Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh base).trans represented.1,
      (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh exponent).trans represented.2⟩
  have powerValue := NativePower.nativePower_into_toNat spec (underRead base width)
    (underRead exponent width) (result ctx width) entered input inherited
  have targetValue :=
    (NativePower.nativePower_into_read_other spec (underRead base width)
      (underRead exponent width) (result ctx width) entered (underRead target width)
      (result_fresh target width)).trans
      (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh target)
  have compared :
      ((powered.1.applyOp (compareOp target decision)).read
        (.storage (compareOp target decision).outputRef.toCStorageRef)).toBool =
        decide ((powered.1.read (NativePower.wordRead (result ctx width))).toNat =
          (powered.1.read (underRead target width)).toNat) :=
    congrArg CShape.Value.toBool (Store.read_applyOp_output powered.1 (compareOp target decision))
  have exited := congrArg CShape.Value.toBool
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh (powered.1.applyOp (compareOp target decision))
      (NativePower.wordRead decision))
  exact exited.trans (compared.trans (by rw [powerValue, targetValue]))

/-- The complete actual check preserves all borrowed classical-quantum-reference correlations. -/
theorem nativeRecovery_powerCheck_borrowedRestored (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (target : CInputRef ctx (.unsignedWord width)) (decision : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (circuit spec base exponent target decision).BorrowedRestored Reference state
      ((circuit spec base exponent target decision).execute Reference state) :=
  Circuit.borrowedRestored_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (body spec base exponent target decision) Reference
    (fun {_} _ initial => Circuit.borrowedRestored_seq
      (NativePower.into spec (underRead base width) (underRead exponent width) (result ctx width))
      (.classical (compareOp target decision)) initial
      (NativePower.nativePower_into_borrowedRestored spec (underRead base width)
        (underRead exponent width) (result ctx width) Reference initial)
      (Circuit.borrowedRestored_classical (compareOp target decision) _)) state

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.PowerCheck

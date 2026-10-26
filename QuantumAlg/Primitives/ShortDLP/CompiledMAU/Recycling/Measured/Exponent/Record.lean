/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Record

/-!
# Complete physical outcome and Store/path families of an actual exponent stream

The recursion follows the original exponent suffix. Every stage feeds its
real output Store to the next stage and keeps all chronological arithmetic
and exponent outcomes, even when physical arithmetic cells are reused
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpCtx := context base noQuantum m ell width

variable (modulus : BitVec width) (wide : 2 ≤ width) {bits : Nat}
  (unit : (ZMod modulus.toNat)ˣ)

/-- All actual chronological arithmetic and exponent measurements of the original suffix. -/
def ExponentOutcomes : (remaining position : Nat) → position + remaining ≤ bits → Type
  | 0, _, _ => Unit
  | remaining + 1, position, bounded =>
      (stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          (⟨position, by omega⟩ : Fin bits) ×
        Fin ((ExpCtx base noQuantum m ell width).quantumLayout.wire
          (control base noQuantum m ell width)).dimension) ×
        ExponentOutcomes remaining (position + 1) (by omega)

instance exponentOutcomesFintype (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    Fintype (ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position
      bounded) := by
  induction remaining generalizing position with
  | zero => change Fintype Unit; infer_instance
  | succ remaining induction =>
      change Fintype ((stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          (⟨position, by omega⟩ : Fin bits) ×
        Fin ((ExpCtx base noQuantum m ell width).quantumLayout.wire
          (control base noQuantum m ell width)).dimension) ×
        ExponentOutcomes base noQuantum m ell width modulus wide unit remaining (position + 1)
          (by omega))
      letI := induction (position + 1) (by omega)
      infer_instance

variable (inverse : Bool)
  (outputs : Fin bits → CWriteRef (ExpCtx base noQuantum m ell width) (.finite 2))

/-- Every real stage Store and full chronological Path is passed into the actual next stage. -/
def exponentActualRecord : (remaining position : Nat) →
    (bounded : position + remaining ≤ bits) → Store (ExpCtx base noQuantum m ell width) →
    ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position bounded →
    Store (ExpCtx base noQuantum m ell width) ×
      (exponentSuffix base noQuantum m ell width wide inverse outputs modulus unit remaining
        position bounded).Path
  | 0, _, _, store, _ => (store, ())
  | remaining + 1, position, bounded, store, outcomes =>
      let head := stageRecord base noQuantum m ell width modulus wide inverse outputs unit
        (⟨position, by omega⟩ : Fin bits) store outcomes.1.1 outcomes.1.2
      let tail := exponentActualRecord remaining (position + 1) (by omega) head.1 outcomes.2
      (tail.1, (head.2, tail.2))

variable [NeZero modulus.toNat]

/-- Actual chronological native matrices of the same original measured exponent suffix. -/
def exponentActualKraus (environment : model.Environment) (Reference : Register) :
    (remaining position : Nat) → (bounded : position + remaining ≤ bits) →
    Store (ExpCtx base noQuantum m ell width) →
    ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position bounded →
    HilbertOperator ((ExpCtx base noQuantum m ell width).register.prod Reference)
  | 0, _, _, _, _ => 1
  | remaining + 1, position, bounded, store, outcomes =>
      let head := stageRecord base noQuantum m ell width modulus wide inverse outputs unit
        (⟨position, by omega⟩ : Fin bits) store outcomes.1.1 outcomes.1.2
      exponentActualKraus environment Reference remaining (position + 1) (by omega) head.1
          outcomes.2 *
        stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit
          (⟨position, by omega⟩ : Fin bits) environment store outcomes.1.1 outcomes.1.2 Reference

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

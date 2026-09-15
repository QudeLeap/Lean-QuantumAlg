/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration.Space

/-!
# Actual retained results and the shared physical bank of a finite Shor batch

Each actual iteration keeps `22m+1` classical bits. The last iteration's
sampler workspace has the largest allowance, giving the independent peak
bound `(count-1)(22m+1)+27m+15` for nonempty batches. The zero-round case has
no extra live storage. Every quantum peak coordinate equals that of the
incoming bank, including the multiplier work word already present there.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

noncomputable section

/-- Exact final resident capacity of the actual retained result contexts. -/
theorem context_resident (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).residentSpace =
      ctx.residentSpace + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) := by
  induction count generalizing ctx with
  | zero =>
      apply SpacePool.ext
      intro axis
      cases axis <;> simp [context, SpacePool.ofShape]
  | succ count induction =>
      change (context (NativeIteration.context ctx N) N count).residentSpace = _
      rw [induction, NativeIteration.context_resident]
      apply SpacePool.ext
      intro axis
      cases axis with
      | classicalBits =>
          change ctx.residentSpace .classicalBits + (22 * modulusBits N + 1) +
              count * (22 * modulusBits N + 1) =
            ctx.residentSpace .classicalBits + (count + 1) * (22 * modulusBits N + 1)
          rw [Nat.add_mul, Nat.one_mul]
          omega
      | quantumSystems dimension => rfl

/-- Every retained result is also actual owned auxiliary capacity. -/
theorem context_auxiliary (ctx : RuntimeCtx .quantum) (N count : Nat) :
    (context ctx N count).auxiliarySpace =
      ctx.auxiliarySpace + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) := by
  induction count generalizing ctx with
  | zero =>
      apply SpacePool.ext
      intro axis
      cases axis <;> simp [context, SpacePool.ofShape]
  | succ count induction =>
      change (context (NativeIteration.context ctx N) N count).auxiliarySpace = _
      rw [induction, NativeIteration.context_auxiliary]
      apply SpacePool.ext
      intro axis
      cases axis with
      | classicalBits =>
          change ctx.auxiliarySpace .classicalBits + (22 * modulusBits N + 1) +
              count * (22 * modulusBits N + 1) =
            ctx.auxiliarySpace .classicalBits + (count + 1) * (22 * modulusBits N + 1)
          rw [Nat.add_mul, Nat.one_mul]
          omega
      | quantumSystems dimension => rfl

/-- The explicit largest additional classical capacity in the actual finite schedule. -/
def additionalBits (N count : Nat) : Nat :=
  if count = 0 then 0 else (count - 1) * (22 * modulusBits N + 1) + 27 * modulusBits N + 15

private theorem additionalBits_succ (N count : Nat) :
    additionalBits N (count + 1) = count * (22 * modulusBits N + 1) + 27 * modulusBits N + 15 := by
  simp [additionalBits]

private theorem first_allowance (base : SpacePool .quantum) (N count : Nat) :
    base + Sampler.Retained.additionalSpace .quantum (modulusBits N) ≤
      base + SpacePool.ofShape (.bits (additionalBits N (count + 1))) := by
  intro axis
  cases axis <;> simp [Sampler.Retained.additionalSpace, SpacePool.ofShape, additionalBits]

private theorem continued_allowance (base : SpacePool .quantum) (N count : Nat) :
    base + SpacePool.ofShape (.bits (22 * modulusBits N + 1)) +
        SpacePool.ofShape (.bits (additionalBits N count)) ≤
      base + SpacePool.ofShape (.bits (additionalBits N (count + 1))) := by
  intro axis
  cases count with
  | zero =>
      cases axis <;> simp [SpacePool.ofShape, additionalBits]
      omega
  | succ count =>
      cases axis with
      | classicalBits =>
          change base .classicalBits + (22 * modulusBits N + 1) +
              additionalBits N (count + 1) ≤
            base .classicalBits + additionalBits N (count + 1 + 1)
          rw [additionalBits_succ, additionalBits_succ, Nat.add_mul, Nat.one_mul]
          omega
      | quantumSystems dimension => exact le_rfl

/-- The bound includes the actual sampler workspace and all results retained by earlier rounds. -/
theorem resident_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    (path : (code ctx N sameWires count).Path) :
    (code ctx N sameWires count).peakResidentSpace path ≤
      ctx.residentSpace + SpacePool.ofShape (.bits (additionalBits N count)) := by
  induction count generalizing ctx with
  | zero =>
      intro axis
      change max (ctx.residentSpace axis) 0 ≤
        ctx.residentSpace axis + (SpacePool.ofShape (.bits 0) : SpacePool .quantum) axis
      cases axis <;> simp [SpacePool.ofShape]
  | succ count induction =>
      refine (Circuit.peakResidentSpace_seq (NativeIteration.code ctx N sameWires)
        (code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count) path).le.trans ?_
      apply SpacePool.max_le
      · exact (NativeIteration.resident_le ctx N sameWires path.1).trans
          (first_allowance ctx.residentSpace N count)
      · have tailBound := induction (NativeIteration.context ctx N)
          ((NativeIteration.quantumWires ctx N).trans sameWires) path.2
        rw [NativeIteration.context_resident] at tailBound
        exact tailBound.trans (continued_allowance ctx.residentSpace N count)

/-- The actual auxiliary peak also includes the complete retained frame and sampler work. -/
theorem auxiliary_le (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    (path : (code ctx N sameWires count).Path) :
    (code ctx N sameWires count).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + SpacePool.ofShape (.bits (additionalBits N count)) := by
  induction count generalizing ctx with
  | zero =>
      intro axis
      change max (ctx.auxiliarySpace axis) 0 ≤
        ctx.auxiliarySpace axis + (SpacePool.ofShape (.bits 0) : SpacePool .quantum) axis
      cases axis <;> simp [SpacePool.ofShape]
  | succ count induction =>
      refine (Circuit.peakAuxiliarySpace_seq (NativeIteration.code ctx N sameWires)
        (code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count) path).le.trans ?_
      apply SpacePool.max_le
      · exact (NativeIteration.auxiliary_le ctx N sameWires path.1).trans
          (first_allowance ctx.auxiliarySpace N count)
      · have tailBound := induction (NativeIteration.context ctx N)
          ((NativeIteration.quantumWires ctx N).trans sameWires) path.2
        rw [NativeIteration.context_auxiliary] at tailBound
        exact tailBound.trans (continued_allowance ctx.auxiliarySpace N count)

/-- Actual live quantum capacity is constant along every complete finite batch path. -/
theorem quantum_peak_eq (ctx : RuntimeCtx .quantum) (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires) (count : Nat)
    (path : (code ctx N sameWires count).Path) (dimension : ℕ+) :
    (code ctx N sameWires count).peakResidentSpace path (.quantumSystems dimension) =
      ctx.residentSpace (.quantumSystems dimension) := by
  induction count generalizing ctx with
  | zero => exact Nat.max_zero _
  | succ count induction =>
      refine (congrArg (fun pool : SpacePool .quantum => pool (.quantumSystems dimension))
        (Circuit.peakResidentSpace_seq (NativeIteration.code ctx N sameWires)
          (code (NativeIteration.context ctx N) N
            ((NativeIteration.quantumWires ctx N).trans sameWires) count) path)).trans ?_
      change max
        ((NativeIteration.code ctx N sameWires).peakResidentSpace path.1
          (.quantumSystems dimension))
        ((code (NativeIteration.context ctx N) N
          ((NativeIteration.quantumWires ctx N).trans sameWires) count).peakResidentSpace path.2
          (.quantumSystems dimension)) = _
      rw [NativeIteration.quantum_peak_eq, induction, NativeIteration.context_resident]
      simp only [SpacePool.ofShape, Pi.add_apply, Nat.add_zero, Nat.max_self]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Components.Gates
public import QuantumAlg.Core.Measurement
public import QuantumAlg.Core.Cost

/-!
# Amplitude amplification in the good/bad plane

Amplitude amplification reduces to a two-dimensional invariant plane spanned by
an orthonormal bad state and good state. If the initial state has angle `θ` from
the bad axis, one amplification iterate rotates that plane by `2θ`; after `k`
iterations the good amplitude is `sin((2k+1)θ)` [dW19, qcnotes.tex:2954].

This module formalizes exactly that two-dimensional core. The ambient register
is the quotient plane, represented as one qubit: `|0⟩` is the bad axis and `|1⟩`
is the good axis. Concrete algorithms provide reflections whose product agrees
with `amplitudeAmplificationStep θ` on this plane.

## Main results

- `QuantumAlg.amplitude_amplification_correct` — exact state after `k`
  amplification iterates under explicit reflection-product assumptions.
- `QuantumAlg.amplitude_amplification_success_probability` — the corresponding
  good-state measurement probability.
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-- The angle after `k` amplitude-amplification iterates: `(2k+1)θ`. -/
def amplitudeAmplificationAngle (θ : ℝ) (k : ℕ) : ℝ := ((2 : ℝ) * k + 1) * θ

/-- The good/bad-plane state with bad amplitude `cos((2k+1)θ)` and good
amplitude `sin((2k+1)θ)`. In this two-dimensional model, `|0⟩` is the bad axis
and `|1⟩` is the good axis. -/
def amplitudeAmplificationState (θ : ℝ) (k : ℕ) : PureState 1 :=
  ((Real.cos (amplitudeAmplificationAngle θ k) : ℂ) • ket0) +
    ((Real.sin (amplitudeAmplificationAngle θ k) : ℂ) • ket1)

/-- One amplitude-amplification iterate on the good/bad plane: rotation by
`2θ`. Since `rotY φ` rotates the real plane by `φ/2`, this is `rotY (4θ)`. -/
def amplitudeAmplificationStep (θ : ℝ) : Gate 1 := rotY (4 * θ)

/-- The plane rotation used by amplitude amplification is unitary. -/
theorem amplitudeAmplificationStep_mem_unitaryGroup (θ : ℝ) :
    amplitudeAmplificationStep θ ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ :=
  rotY_mem_unitaryGroup _

/-- One amplitude-amplification step increases the good/bad-plane angle by
`2θ`. -/
theorem amplitudeAmplificationStep_apply_state (θ : ℝ) (k : ℕ) :
    (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) =
      amplitudeAmplificationState θ (k + 1) := by
  apply WithLp.ofLp_injective
  funext i
  have hangle : amplitudeAmplificationAngle θ (k + 1) =
      amplitudeAmplificationAngle θ k + 2 * θ := by
    unfold amplitudeAmplificationAngle
    norm_num
    ring
  fin_cases i
  · change (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) 0 =
      amplitudeAmplificationState θ (k + 1) 0
    rw [Gate.apply_apply]
    simp [amplitudeAmplificationStep, amplitudeAmplificationState, rotY,
      ket0, ket1, ket_apply, PiLp.smul_apply, PiLp.add_apply]
    rw [hangle]
    norm_num
    rw [Complex.cos_add]
    ring_nf
  · change (amplitudeAmplificationStep θ).apply (amplitudeAmplificationState θ k) 1 =
      amplitudeAmplificationState θ (k + 1) 1
    rw [Gate.apply_apply]
    simp [amplitudeAmplificationStep, amplitudeAmplificationState, rotY,
      ket0, ket1, ket_apply, PiLp.smul_apply, PiLp.add_apply]
    rw [hangle]
    norm_num
    rw [Complex.sin_add]
    ring_nf

/-- Iterating the abstract amplification step gives the standard closed form
`cos((2k+1)θ)|bad⟩ + sin((2k+1)θ)|good⟩`. -/
theorem amplitudeAmplificationStep_pow_apply (θ : ℝ) (k : ℕ) :
    ((amplitudeAmplificationStep θ) ^ k).apply (amplitudeAmplificationState θ 0) =
      amplitudeAmplificationState θ k := by
  induction k with
  | zero =>
      simp [Gate.one_apply]
  | succ k ih =>
      rw [pow_succ', Gate.mul_apply, ih, amplitudeAmplificationStep_apply_state]

/-- An amplitude-amplification instance on the two-dimensional good/bad plane.
The fields are deliberately explicit: a good-state reflection, a start-state
reflection, and the proof that their product restricts to the standard rotation
on this plane. -/
structure AmplitudeAmplificationModel where
  /-- Initial angle from the bad axis; the initial good probability is
  `sin θ ^ 2`. -/
  θ : ℝ
  /-- Reflection that flips the good component and fixes the bad component. -/
  goodReflection : Gate 1
  /-- Reflection through the prepared start state. -/
  startReflection : Gate 1
  /-- The product of the two reflections acts as the amplification rotation on
  the invariant good/bad plane. -/
  iterate_eq : startReflection * goodReflection = amplitudeAmplificationStep θ

/-- Amplitude amplification correctness in the accepted two-dimensional scope:
if the reflection product acts as the standard good/bad-plane rotation, then `k`
iterations produce the closed-form amplified state. -/
theorem amplitude_amplification_correct (M : AmplitudeAmplificationModel) (k : ℕ) :
    Gate.apply ((M.startReflection * M.goodReflection) ^ k)
        (amplitudeAmplificationState M.θ 0) =
      amplitudeAmplificationState M.θ k := by
  rw [M.iterate_eq]
  exact amplitudeAmplificationStep_pow_apply M.θ k

/-- The success probability of the closed-form amplitude-amplified state is the
squared good amplitude. -/
theorem amplitudeAmplificationState_good_probability (θ : ℝ) (k : ℕ) :
    PureState.probOutcome (amplitudeAmplificationState θ k) (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle θ k) ^ 2 := by
  rw [PureState.probOutcome]
  simp [amplitudeAmplificationState, ket0, ket1, ket_apply, PiLp.smul_apply,
    PiLp.add_apply]
  rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Amplitude amplification success probability after `k` reflection-product
iterations. -/
theorem amplitude_amplification_success_probability
    (M : AmplitudeAmplificationModel) (k : ℕ) :
    PureState.probOutcome
        (Gate.apply ((M.startReflection * M.goodReflection) ^ k)
          (amplitudeAmplificationState M.θ 0))
        (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [amplitude_amplification_correct, amplitudeAmplificationState_good_probability]

namespace AmplitudeAmplification

/-- The state after `k` amplification iterates, annotated with iterate cost `k`. -/
def timedIterate (M : AmplitudeAmplificationModel) (k : ℕ) : Timed (PureState 1) :=
  Timed.trusted k
    (Gate.apply ((M.startReflection * M.goodReflection) ^ k)
      (amplitudeAmplificationState M.θ 0))

@[simp]
theorem timedIterate_ret (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).ret =
      Gate.apply ((M.startReflection * M.goodReflection) ^ k)
        (amplitudeAmplificationState M.θ 0) := rfl

@[simp]
theorem timedIterate_time (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).time = k := rfl

/-- Amplitude-amplification correctness, phrased through the TimeM return value. -/
theorem timedIterate_correct (M : AmplitudeAmplificationModel) (k : ℕ) :
    (timedIterate M k).ret = amplitudeAmplificationState M.θ k := by
  exact amplitude_amplification_correct M k

/-- The good-state success probability after the timed iterate. -/
theorem timedIterate_success_probability
    (M : AmplitudeAmplificationModel) (k : ℕ) :
    PureState.probOutcome (timedIterate M k).ret (1 : Fin (2 ^ 1)) =
      Real.sin (amplitudeAmplificationAngle M.θ k) ^ 2 := by
  rw [timedIterate_correct, amplitudeAmplificationState_good_probability]

end AmplitudeAmplification


end

end QuantumAlg

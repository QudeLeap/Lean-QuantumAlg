/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word21Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word21State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word21Step0 :
    word21Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word21State1 := by decide +kernel

private def word21Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word21State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word21Step1 :
    word21Chunk1.foldl (fun acc a => a.applyPacked acc)
      word21State1 = word21State2 := by decide +kernel

private def word21Chunk2 : List Letter := [.h, .s, .s, .s, .h, .s, .s, .h]
private def word21State3 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word21Step2 :
    word21Chunk2.foldl (fun acc a => a.applyPacked acc)
      word21State2 = word21State3 := by decide +kernel

private def word21Chunk3 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word21State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word21Step3 :
    word21Chunk3.foldl (fun acc a => a.applyPacked acc)
      word21State3 = word21State4 := by decide +kernel

private def word21Chunk4 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word21State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word21Step4 :
    word21Chunk4.foldl (fun acc a => a.applyPacked acc)
      word21State4 = word21State5 := by decide +kernel

private def word21Chunk5 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word21State6 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word21Step5 :
    word21Chunk5.foldl (fun acc a => a.applyPacked acc)
      word21State5 = word21State6 := by decide +kernel

private def word21Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word21State7 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-7 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word21Step6 :
    word21Chunk6.foldl (fun acc a => a.applyPacked acc)
      word21State6 = word21State7 := by decide +kernel

private def word21Chunk7 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word21State8 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word21Step7 :
    word21Chunk7.foldl (fun acc a => a.applyPacked acc)
      word21State7 = word21State8 := by decide +kernel

private def word21Chunk8 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word21State9 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((15 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((23 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word21Step8 :
    word21Chunk8.foldl (fun acc a => a.applyPacked acc)
      word21State8 = word21State9 := by decide +kernel

private def word21Chunk9 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word21State10 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 6),
        ((49 : Dyadic) * half ^ 7)⟩,
       ⟨((25 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 5)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-17 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((43 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word21Step9 :
    word21Chunk9.foldl (fun acc a => a.applyPacked acc)
      word21State9 = word21State10 := by decide +kernel

private def word21Chunk10 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word21State11 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((81 : Dyadic) * half ^ 8)⟩,
       ⟨((-11 : Dyadic) * half ^ 7),
        ((41 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((103 : Dyadic) * half ^ 7),
        ((29 : Dyadic) * half ^ 8)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 6),
        ((-111 : Dyadic) * half ^ 8)⟩,
       ⟨((11 : Dyadic) * half ^ 7),
        ((95 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 8)⟩,
       ⟨((-61 : Dyadic) * half ^ 7),
        ((43 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word21Step10 :
    word21Chunk10.foldl (fun acc a => a.applyPacked acc)
      word21State10 = word21State11 := by decide +kernel

private def word21Chunk11 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word21State12 : PackedMat2 :=
    ⟨⟨⟨((-61 : Dyadic) * half ^ 7),
        ((-153 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 8),
        ((17 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 7),
        ((27 : Dyadic) * half ^ 9)⟩,
       ⟨((-133 : Dyadic) * half ^ 8),
        ((159 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 7),
        ((27 : Dyadic) * half ^ 9)⟩,
       ⟨((133 : Dyadic) * half ^ 8),
        ((-159 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((61 : Dyadic) * half ^ 7),
        ((153 : Dyadic) * half ^ 9)⟩,
       ⟨((3 : Dyadic) * half ^ 8),
        ((17 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word21Step11 :
    word21Chunk11.foldl (fun acc a => a.applyPacked acc)
      word21State11 = word21State12 := by decide +kernel

private def word21Chunk12 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word21State13 : PackedMat2 :=
    ⟨⟨⟨((-45 : Dyadic) * half ^ 8),
        ((-121 : Dyadic) * half ^ 8)⟩,
       ⟨((-3 : Dyadic) * half ^ 7),
        ((-95 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((75 : Dyadic) * half ^ 9),
        ((-13 : Dyadic) * half ^ 7)⟩,
       ⟨((317 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 6),
        ((121 : Dyadic) * half ^ 9)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((49 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-147 : Dyadic) * half ^ 9),
        ((-39 : Dyadic) * half ^ 9)⟩,
       ⟨((337 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word21Step12 :
    word21Chunk12.foldl (fun acc a => a.applyPacked acc)
      word21State12 = word21State13 := by decide +kernel

private def word21Chunk13 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State14 : PackedMat2 :=
    ⟨⟨⟨((-53 : Dyadic) * half ^ 10),
        ((419 : Dyadic) * half ^ 10)⟩,
       ⟨((-527 : Dyadic) * half ^ 10),
        ((-1 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-531 : Dyadic) * half ^ 10),
        ((-3 : Dyadic) * half ^ 6)⟩,
       ⟨((-17 : Dyadic) * half ^ 10),
        ((255 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 10),
        ((-255 : Dyadic) * half ^ 10)⟩,
       ⟨((531 : Dyadic) * half ^ 10),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-527 : Dyadic) * half ^ 10),
        ((-1 : Dyadic) * half ^ 9)⟩,
       ⟨((-53 : Dyadic) * half ^ 10),
        ((419 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word21Step13 :
    word21Chunk13.foldl (fun acc a => a.applyPacked acc)
      word21State13 = word21State14 := by decide +kernel

private def word21Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State15 : PackedMat2 :=
    ⟨⟨⟨((509 : Dyadic) * half ^ 10),
        ((-435 : Dyadic) * half ^ 11)⟩,
       ⟨((711 : Dyadic) * half ^ 10),
        ((179 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-141 : Dyadic) * half ^ 10),
        ((-233 : Dyadic) * half ^ 10)⟩,
       ⟨((-45 : Dyadic) * half ^ 8),
        ((-79 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 7),
        ((-321 : Dyadic) * half ^ 11)⟩,
       ⟨((-77 : Dyadic) * half ^ 9),
        ((39 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-305 : Dyadic) * half ^ 9)⟩,
       ⟨((307 : Dyadic) * half ^ 10),
        ((101 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word21Step14 :
    word21Chunk14.foldl (fun acc a => a.applyPacked acc)
      word21State14 = word21State15 := by decide +kernel

private def word21Chunk15 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word21State16 : PackedMat2 :=
    ⟨⟨⟨((-1287 : Dyadic) * half ^ 11),
        ((373 : Dyadic) * half ^ 12)⟩,
       ⟨((217 : Dyadic) * half ^ 9),
        ((1145 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-795 : Dyadic) * half ^ 11),
        ((311 : Dyadic) * half ^ 12)⟩,
       ⟨((103 : Dyadic) * half ^ 9),
        ((-647 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((795 : Dyadic) * half ^ 11),
        ((-311 : Dyadic) * half ^ 12)⟩,
       ⟨((103 : Dyadic) * half ^ 9),
        ((-647 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1287 : Dyadic) * half ^ 11),
        ((373 : Dyadic) * half ^ 12)⟩,
       ⟨((-217 : Dyadic) * half ^ 9),
        ((-1145 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word21Step15 :
    word21Chunk15.foldl (fun acc a => a.applyPacked acc)
      word21State15 = word21State16 := by decide +kernel

private def word21Chunk16 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word21State17 : PackedMat2 :=
    ⟨⟨⟨((-283 : Dyadic) * half ^ 10),
        ((-1301 : Dyadic) * half ^ 13)⟩,
       ⟨((2303 : Dyadic) * half ^ 12),
        ((-1387 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((147 : Dyadic) * half ^ 10),
        ((-2315 : Dyadic) * half ^ 13)⟩,
       ⟨((-1059 : Dyadic) * half ^ 12),
        ((-2911 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((147 : Dyadic) * half ^ 10),
        ((-2315 : Dyadic) * half ^ 13)⟩,
       ⟨((1059 : Dyadic) * half ^ 12),
        ((2911 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((283 : Dyadic) * half ^ 10),
        ((1301 : Dyadic) * half ^ 13)⟩,
       ⟨((2303 : Dyadic) * half ^ 12),
        ((-1387 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word21Step16 :
    word21Chunk16.foldl (fun acc a => a.applyPacked acc)
      word21State16 = word21State17 := by decide +kernel

private def word21Chunk17 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State18 : PackedMat2 :=
    ⟨⟨⟨((-135 : Dyadic) * half ^ 11),
        ((-1531 : Dyadic) * half ^ 13)⟩,
       ⟨((-465 : Dyadic) * half ^ 10),
        ((521 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1901 : Dyadic) * half ^ 13),
        ((4087 : Dyadic) * half ^ 13)⟩,
       ⟨((1337 : Dyadic) * half ^ 13),
        ((-631 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2359 : Dyadic) * half ^ 12),
        ((-141 : Dyadic) * half ^ 12)⟩,
       ⟨((27 : Dyadic) * half ^ 6),
        ((1619 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3615 : Dyadic) * half ^ 13),
        ((795 : Dyadic) * half ^ 12)⟩,
       ⟨((-553 : Dyadic) * half ^ 13),
        ((1065 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word21Step17 :
    word21Chunk17.foldl (fun acc a => a.applyPacked acc)
      word21State17 = word21State18 := by decide +kernel

private def word21Chunk18 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word21State19 : PackedMat2 :=
    ⟨⟨⟨((-2943 : Dyadic) * half ^ 13),
        ((-389 : Dyadic) * half ^ 14)⟩,
       ⟨((-6977 : Dyadic) * half ^ 13),
        ((-695 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2361 : Dyadic) * half ^ 13),
        ((1211 : Dyadic) * half ^ 13)⟩,
       ⟨((475 : Dyadic) * half ^ 12),
        ((-145 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2361 : Dyadic) * half ^ 13),
        ((-1211 : Dyadic) * half ^ 13)⟩,
       ⟨((475 : Dyadic) * half ^ 12),
        ((-145 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2943 : Dyadic) * half ^ 13),
        ((-389 : Dyadic) * half ^ 14)⟩,
       ⟨((6977 : Dyadic) * half ^ 13),
        ((695 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word21Step18 :
    word21Chunk18.foldl (fun acc a => a.applyPacked acc)
      word21State18 = word21State19 := by decide +kernel

private def word21Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word21State20 : PackedMat2 :=
    ⟨⟨⟨((8717 : Dyadic) * half ^ 14),
        ((8429 : Dyadic) * half ^ 15)⟩,
       ⟨((2279 : Dyadic) * half ^ 13),
        ((-11025 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((365 : Dyadic) * half ^ 11),
        ((-1409 : Dyadic) * half ^ 15)⟩,
       ⟨((-1703 : Dyadic) * half ^ 14),
        ((11221 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((365 : Dyadic) * half ^ 11),
        ((-1409 : Dyadic) * half ^ 15)⟩,
       ⟨((1703 : Dyadic) * half ^ 14),
        ((-11221 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-8717 : Dyadic) * half ^ 14),
        ((-8429 : Dyadic) * half ^ 15)⟩,
       ⟨((2279 : Dyadic) * half ^ 13),
        ((-11025 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word21Step19 :
    word21Chunk19.foldl (fun acc a => a.applyPacked acc)
      word21State19 = word21State20 := by decide +kernel

private def word21Chunk20 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State21 : PackedMat2 :=
    ⟨⟨⟨((-157 : Dyadic) * half ^ 13),
        ((2673 : Dyadic) * half ^ 15)⟩,
       ⟨((1141 : Dyadic) * half ^ 13),
        ((5377 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-16249 : Dyadic) * half ^ 15),
        ((-6809 : Dyadic) * half ^ 15)⟩,
       ⟨((14087 : Dyadic) * half ^ 15),
        ((-11219 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-2205 : Dyadic) * half ^ 14),
        ((237 : Dyadic) * half ^ 9)⟩,
       ⟨((-4507 : Dyadic) * half ^ 13),
        ((-1081 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-8081 : Dyadic) * half ^ 15),
        ((-649 : Dyadic) * half ^ 13)⟩,
       ⟨((-13427 : Dyadic) * half ^ 15),
        ((-123 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word21Step20 :
    word21Chunk20.foldl (fun acc a => a.applyPacked acc)
      word21State20 = word21State21 := by decide +kernel

private def word21Chunk21 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word21State22 : PackedMat2 :=
    ⟨⟨⟨((-15467 : Dyadic) * half ^ 16),
        ((-18191 : Dyadic) * half ^ 16)⟩,
       ⟨((6793 : Dyadic) * half ^ 16),
        ((2307 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-27077 : Dyadic) * half ^ 16),
        ((-7703 : Dyadic) * half ^ 16)⟩,
       ⟨((-34123 : Dyadic) * half ^ 16),
        ((1127 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-10329 : Dyadic) * half ^ 16),
        ((3825 : Dyadic) * half ^ 13)⟩,
       ⟨((25735 : Dyadic) * half ^ 16),
        ((-3523 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((265 : Dyadic) * half ^ 16),
        ((-4337 : Dyadic) * half ^ 16)⟩,
       ⟨((-36647 : Dyadic) * half ^ 16),
        ((-5565 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word21Step21 :
    word21Chunk21.foldl (fun acc a => a.applyPacked acc)
      word21State21 = word21State22 := by decide +kernel

private def word21Chunk22 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word21State23 : PackedMat2 :=
    ⟨⟨⟨((-16423 : Dyadic) * half ^ 16),
        ((-64523 : Dyadic) * half ^ 17)⟩,
       ⟨((-2145 : Dyadic) * half ^ 16),
        ((-7875 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((4613 : Dyadic) * half ^ 15),
        ((-10193 : Dyadic) * half ^ 15)⟩,
       ⟨((22817 : Dyadic) * half ^ 16),
        ((-3837 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4613 : Dyadic) * half ^ 15),
        ((-10193 : Dyadic) * half ^ 15)⟩,
       ⟨((-22817 : Dyadic) * half ^ 16),
        ((3837 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((16423 : Dyadic) * half ^ 16),
        ((64523 : Dyadic) * half ^ 17)⟩,
       ⟨((-2145 : Dyadic) * half ^ 16),
        ((-7875 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word21Step22 :
    word21Chunk22.foldl (fun acc a => a.applyPacked acc)
      word21State22 = word21State23 := by decide +kernel

private def word21Chunk23 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word21State24 : PackedMat2 :=
    ⟨⟨⟨((-34131 : Dyadic) * half ^ 16),
        ((2177 : Dyadic) * half ^ 18)⟩,
       ⟨((-15417 : Dyadic) * half ^ 16),
        ((11227 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((106969 : Dyadic) * half ^ 17),
        ((1191 : Dyadic) * half ^ 16)⟩,
       ⟨((189 : Dyadic) * half ^ 14),
        ((-4901 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((2519 : Dyadic) * half ^ 17),
        ((-108481 : Dyadic) * half ^ 18)⟩,
       ⟨((-7283 : Dyadic) * half ^ 17),
        ((-105457 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((3351 : Dyadic) * half ^ 16),
        ((-12387 : Dyadic) * half ^ 15)⟩,
       ⟨((-4525 : Dyadic) * half ^ 17),
        ((-9357 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word21Step23 :
    word21Chunk23.foldl (fun acc a => a.applyPacked acc)
      word21State23 = word21State24 := by decide +kernel

private def word21Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word21State25 : PackedMat2 :=
    ⟨⟨⟨((34995 : Dyadic) * half ^ 16),
        ((-142987 : Dyadic) * half ^ 19)⟩,
       ⟨((-58547 : Dyadic) * half ^ 18),
        ((-49689 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((35757 : Dyadic) * half ^ 17),
        ((221563 : Dyadic) * half ^ 19)⟩,
       ⟨((66333 : Dyadic) * half ^ 18),
        ((19015 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((35757 : Dyadic) * half ^ 17),
        ((221563 : Dyadic) * half ^ 19)⟩,
       ⟨((-66333 : Dyadic) * half ^ 18),
        ((-19015 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-34995 : Dyadic) * half ^ 16),
        ((142987 : Dyadic) * half ^ 19)⟩,
       ⟨((-58547 : Dyadic) * half ^ 18),
        ((-49689 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word21Step24 :
    word21Chunk24.foldl (fun acc a => a.applyPacked acc)
      word21State24 = word21State25 := by decide +kernel

private def word21Chunk25 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State26 : PackedMat2 :=
    ⟨⟨⟨((-7071 : Dyadic) * half ^ 16),
        ((306383 : Dyadic) * half ^ 19)⟩,
       ⟨((2241 : Dyadic) * half ^ 15),
        ((-965 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-176553 : Dyadic) * half ^ 19),
        ((-46205 : Dyadic) * half ^ 19)⟩,
       ⟨((66923 : Dyadic) * half ^ 19),
        ((145353 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((95779 : Dyadic) * half ^ 18),
        ((60869 : Dyadic) * half ^ 18)⟩,
       ⟨((24787 : Dyadic) * half ^ 17),
        ((-54815 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((321823 : Dyadic) * half ^ 19),
        ((-11553 : Dyadic) * half ^ 17)⟩,
       ⟨((-290943 : Dyadic) * half ^ 19),
        ((2589 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word21Step25 :
    word21Chunk25.foldl (fun acc a => a.applyPacked acc)
      word21State25 = word21State26 := by decide +kernel

private def word21Chunk26 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word21State27 : PackedMat2 :=
    ⟨⟨⟨((509987 : Dyadic) * half ^ 20),
        ((-186481 : Dyadic) * half ^ 20)⟩,
       ⟨((89105 : Dyadic) * half ^ 20),
        ((97111 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-123477 : Dyadic) * half ^ 20),
        ((-168673 : Dyadic) * half ^ 19)⟩,
       ⟨((57585 : Dyadic) * half ^ 20),
        ((327101 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-57585 : Dyadic) * half ^ 20),
        ((-327101 : Dyadic) * half ^ 20)⟩,
       ⟨((123477 : Dyadic) * half ^ 20),
        ((168673 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((89105 : Dyadic) * half ^ 20),
        ((97111 : Dyadic) * half ^ 18)⟩,
       ⟨((509987 : Dyadic) * half ^ 20),
        ((-186481 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word21Step26 :
    word21Chunk26.foldl (fun acc a => a.applyPacked acc)
      word21State26 = word21State27 := by decide +kernel

private def word21Chunk27 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State28 : PackedMat2 :=
    ⟨⟨⟨((-615801 : Dyadic) * half ^ 20),
        ((-318623 : Dyadic) * half ^ 21)⟩,
       ⟨((373161 : Dyadic) * half ^ 20),
        ((61967 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-254725 : Dyadic) * half ^ 20),
        ((154079 : Dyadic) * half ^ 20)⟩,
       ⟨((39835 : Dyadic) * half ^ 18),
        ((-441937 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-143929 : Dyadic) * half ^ 19),
        ((-95385 : Dyadic) * half ^ 21)⟩,
       ⟨((37251 : Dyadic) * half ^ 16),
        ((-414065 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((16041 : Dyadic) * half ^ 17),
        ((15165 : Dyadic) * half ^ 17)⟩,
       ⟨((190295 : Dyadic) * half ^ 20),
        ((494481 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word21Step27 :
    word21Chunk27.foldl (fun acc a => a.applyPacked acc)
      word21State27 = word21State28 := by decide +kernel

private def word21Chunk28 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word21State29 : PackedMat2 :=
    ⟨⟨⟨((-207191 : Dyadic) * half ^ 19),
        ((7481 : Dyadic) * half ^ 20)⟩,
       ⟨((13587 : Dyadic) * half ^ 19),
        ((-953127 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-772963 : Dyadic) * half ^ 21),
        ((-452021 : Dyadic) * half ^ 21)⟩,
       ⟨((510523 : Dyadic) * half ^ 21),
        ((-558633 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((510523 : Dyadic) * half ^ 21),
        ((-558633 : Dyadic) * half ^ 21)⟩,
       ⟨((-772963 : Dyadic) * half ^ 21),
        ((-452021 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-13587 : Dyadic) * half ^ 19),
        ((953127 : Dyadic) * half ^ 21)⟩,
       ⟨((207191 : Dyadic) * half ^ 19),
        ((-7481 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word21Step28 :
    word21Chunk28.foldl (fun acc a => a.applyPacked acc)
      word21State28 = word21State29 := by decide +kernel

private def word21Chunk29 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word21State30 : PackedMat2 :=
    ⟨⟨⟨((731851 : Dyadic) * half ^ 22),
        ((365389 : Dyadic) * half ^ 22)⟩,
       ⟨((-1714665 : Dyadic) * half ^ 22),
        ((-30431 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1307217 : Dyadic) * half ^ 22),
        ((756119 : Dyadic) * half ^ 22)⟩,
       ⟨((-3262229 : Dyadic) * half ^ 22),
        ((104237 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-1173067 : Dyadic) * half ^ 22),
        ((488753 : Dyadic) * half ^ 21)⟩,
       ⟨((-339171 : Dyadic) * half ^ 22),
        ((-2284723 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((304527 : Dyadic) * half ^ 22),
        ((-491407 : Dyadic) * half ^ 22)⟩,
       ⟨((426251 : Dyadic) * half ^ 22),
        ((611629 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word21Step29 :
    word21Chunk29.foldl (fun acc a => a.applyPacked acc)
      word21State29 = word21State30 := by decide +kernel

private def word21Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word21State31 : PackedMat2 :=
    ⟨⟨⟨((12731 : Dyadic) * half ^ 20),
        ((40653 : Dyadic) * half ^ 21)⟩,
       ⟨((-255593 : Dyadic) * half ^ 22),
        ((21987 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((1513017 : Dyadic) * half ^ 22),
        ((1477045 : Dyadic) * half ^ 23)⟩,
       ⟨((3728589 : Dyadic) * half ^ 22),
        ((-577473 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((224893 : Dyadic) * half ^ 21),
        ((2620803 : Dyadic) * half ^ 22)⟩,
       ⟨((1027259 : Dyadic) * half ^ 22),
        ((-553893 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-128601 : Dyadic) * half ^ 21),
        ((204669 : Dyadic) * half ^ 23)⟩,
       ⟨((47295 : Dyadic) * half ^ 21),
        ((-306517 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word21Step30 :
    word21Chunk30.foldl (fun acc a => a.applyPacked acc)
      word21State30 = word21State31 := by decide +kernel

private def word21Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word21State32 : PackedMat2 :=
    ⟨⟨⟨((-206899 : Dyadic) * half ^ 19),
        ((327529 : Dyadic) * half ^ 24)⟩,
       ⟨((-1110301 : Dyadic) * half ^ 23),
        ((-1825619 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2507137 : Dyadic) * half ^ 23),
        ((3955299 : Dyadic) * half ^ 24)⟩,
       ⟨((246617 : Dyadic) * half ^ 21),
        ((9096835 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((160673 : Dyadic) * half ^ 19),
        ((3493605 : Dyadic) * half ^ 24)⟩,
       ⟨((6526067 : Dyadic) * half ^ 23),
        ((-1520669 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((538287 : Dyadic) * half ^ 22),
        ((-2200083 : Dyadic) * half ^ 24)⟩,
       ⟨((749045 : Dyadic) * half ^ 23),
        ((4420685 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word21Step31 :
    word21Chunk31.foldl (fun acc a => a.applyPacked acc)
      word21State31 = word21State32 := by decide +kernel

private def word21Chunk32 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word21State33 : PackedMat2 :=
    ⟨⟨⟨((6483727 : Dyadic) * half ^ 24),
        ((4197421 : Dyadic) * half ^ 24)⟩,
       ⟨((-5456265 : Dyadic) * half ^ 24),
        ((843881 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((30101 : Dyadic) * half ^ 23),
        ((-1840015 : Dyadic) * half ^ 22)⟩,
       ⟨((3171423 : Dyadic) * half ^ 23),
        ((-3494867 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3865193 : Dyadic) * half ^ 24),
        ((-1570661 : Dyadic) * half ^ 23)⟩,
       ⟨((10854927 : Dyadic) * half ^ 24),
        ((-800381 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-838385 : Dyadic) * half ^ 22),
        ((-1492499 : Dyadic) * half ^ 22)⟩,
       ⟨((2520651 : Dyadic) * half ^ 23),
        ((513731 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word21Step32 :
    word21Chunk32.foldl (fun acc a => a.applyPacked acc)
      word21State32 = word21State33 := by decide +kernel

private def word21Chunk33 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State34 : PackedMat2 :=
    ⟨⟨⟨((-1539115 : Dyadic) * half ^ 25),
        ((-553157 : Dyadic) * half ^ 23)⟩,
       ⟨((27836221 : Dyadic) * half ^ 25),
        ((665747 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-13621781 : Dyadic) * half ^ 25),
        ((1743609 : Dyadic) * half ^ 25)⟩,
       ⟨((-12096269 : Dyadic) * half ^ 25),
        ((-74969 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-12096269 : Dyadic) * half ^ 25),
        ((-74969 : Dyadic) * half ^ 24)⟩,
       ⟨((-13621781 : Dyadic) * half ^ 25),
        ((1743609 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-27836221 : Dyadic) * half ^ 25),
        ((-665747 : Dyadic) * half ^ 25)⟩,
       ⟨((1539115 : Dyadic) * half ^ 25),
        ((553157 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word21Step33 :
    word21Chunk33.foldl (fun acc a => a.applyPacked acc)
      word21State33 = word21State34 := by decide +kernel

private def word21Chunk34 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word21State35 : PackedMat2 :=
    ⟨⟨⟨((-15183965 : Dyadic) * half ^ 25),
        ((-1483809 : Dyadic) * half ^ 25)⟩,
       ⟨((-450323 : Dyadic) * half ^ 24),
        ((19241309 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((9230931 : Dyadic) * half ^ 25),
        ((1215825 : Dyadic) * half ^ 26)⟩,
       ⟨((-7734269 : Dyadic) * half ^ 25),
        ((2795893 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-2005859 : Dyadic) * half ^ 25),
        ((-748331 : Dyadic) * half ^ 25)⟩,
       ⟨((395017 : Dyadic) * half ^ 24),
        ((-1060325 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((4439375 : Dyadic) * half ^ 23),
        ((-16084611 : Dyadic) * half ^ 26)⟩,
       ⟨((-10362559 : Dyadic) * half ^ 24),
        ((-14283319 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word21Step34 :
    word21Chunk34.foldl (fun acc a => a.applyPacked acc)
      word21State34 = word21State35 := by decide +kernel

private def word21Chunk35 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word21State36 : PackedMat2 :=
    ⟨⟨⟨((-9801241 : Dyadic) * half ^ 26),
        ((-66054655 : Dyadic) * half ^ 27)⟩,
       ⟨((2033099 : Dyadic) * half ^ 22),
        ((-3553085 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((2462685 : Dyadic) * half ^ 24),
        ((-22816649 : Dyadic) * half ^ 27)⟩,
       ⟨((27210789 : Dyadic) * half ^ 26),
        ((-11285095 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((2462685 : Dyadic) * half ^ 24),
        ((-22816649 : Dyadic) * half ^ 27)⟩,
       ⟨((-27210789 : Dyadic) * half ^ 26),
        ((11285095 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((9801241 : Dyadic) * half ^ 26),
        ((66054655 : Dyadic) * half ^ 27)⟩,
       ⟨((2033099 : Dyadic) * half ^ 22),
        ((-3553085 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word21Step35 :
    word21Chunk35.foldl (fun acc a => a.applyPacked acc)
      word21State35 = word21State36 := by decide +kernel

private def word21Chunk36 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word21State37 : PackedMat2 :=
    ⟨⟨⟨((-115635111 : Dyadic) * half ^ 27),
        ((5253033 : Dyadic) * half ^ 26)⟩,
       ⟨((-19120103 : Dyadic) * half ^ 27),
        ((-1147221 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-951473 : Dyadic) * half ^ 23),
        ((1032279 : Dyadic) * half ^ 25)⟩,
       ⟨((14908215 : Dyadic) * half ^ 26),
        ((36967877 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((14908215 : Dyadic) * half ^ 26),
        ((36967877 : Dyadic) * half ^ 27)⟩,
       ⟨((-951473 : Dyadic) * half ^ 23),
        ((1032279 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((19120103 : Dyadic) * half ^ 27),
        ((1147221 : Dyadic) * half ^ 24)⟩,
       ⟨((115635111 : Dyadic) * half ^ 27),
        ((-5253033 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word21Step36 :
    word21Chunk36.foldl (fun acc a => a.applyPacked acc)
      word21State36 = word21State37 := by decide +kernel

private def word21Chunk37 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word21State38 : PackedMat2 :=
    ⟨⟨⟨((-4996263 : Dyadic) * half ^ 27),
        ((35611621 : Dyadic) * half ^ 27)⟩,
       ⟨((43902155 : Dyadic) * half ^ 27),
        ((-28073645 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-48302781 : Dyadic) * half ^ 28),
        ((-33157589 : Dyadic) * half ^ 28)⟩,
       ⟨((218839601 : Dyadic) * half ^ 28),
        ((7197433 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-20177511 : Dyadic) * half ^ 27),
        ((-133571191 : Dyadic) * half ^ 28)⟩,
       ⟨((6490039 : Dyadic) * half ^ 26),
        ((-42634205 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-99296887 : Dyadic) * half ^ 28),
        ((24449209 : Dyadic) * half ^ 27)⟩,
       ⟨((43149597 : Dyadic) * half ^ 28),
        ((9726473 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word21Step37 :
    word21Chunk37.foldl (fun acc a => a.applyPacked acc)
      word21State37 = word21State38 := by decide +kernel

private def word21Chunk38 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word21State39 : PackedMat2 :=
    ⟨⟨⟨((102944955 : Dyadic) * half ^ 29),
        ((12809677 : Dyadic) * half ^ 27)⟩,
       ⟨((152699785 : Dyadic) * half ^ 29),
        ((166224985 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-295147305 : Dyadic) * half ^ 29),
        ((3930757 : Dyadic) * half ^ 27)⟩,
       ⟨((-121712225 : Dyadic) * half ^ 29),
        ((213755657 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((229478685 : Dyadic) * half ^ 29),
        ((-208429765 : Dyadic) * half ^ 29)⟩,
       ⟨((-198032629 : Dyadic) * half ^ 29),
        ((-21679385 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-217463693 : Dyadic) * half ^ 29),
        ((-63911185 : Dyadic) * half ^ 28)⟩,
       ⟨((114986277 : Dyadic) * half ^ 29),
        ((24877415 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word21Step38 :
    word21Chunk38.foldl (fun acc a => a.applyPacked acc)
      word21State38 = word21State39 := by decide +kernel

private def word21Chunk39 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word21State40 : PackedMat2 :=
    ⟨⟨⟨((44814079 : Dyadic) * half ^ 28),
        ((-271709795 : Dyadic) * half ^ 30)⟩,
       ⟨((29670287 : Dyadic) * half ^ 27),
        ((117220953 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-16076353 : Dyadic) * half ^ 28),
        ((-159181333 : Dyadic) * half ^ 28)⟩,
       ⟨((123675143 : Dyadic) * half ^ 29),
        ((-40555891 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((16076353 : Dyadic) * half ^ 28),
        ((159181333 : Dyadic) * half ^ 28)⟩,
       ⟨((123675143 : Dyadic) * half ^ 29),
        ((-40555891 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((44814079 : Dyadic) * half ^ 28),
        ((-271709795 : Dyadic) * half ^ 30)⟩,
       ⟨((-29670287 : Dyadic) * half ^ 27),
        ((-117220953 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word21Step39 :
    word21Chunk39.foldl (fun acc a => a.applyPacked acc)
      word21State39 = word21State40 := by decide +kernel

private def word21Chunk40 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word21State41 : PackedMat2 :=
    ⟨⟨⟨((67480501 : Dyadic) * half ^ 29),
        ((-430724685 : Dyadic) * half ^ 31)⟩,
       ⟨((112776197 : Dyadic) * half ^ 28),
        ((-197161161 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-12713379 : Dyadic) * half ^ 29),
        ((-278497869 : Dyadic) * half ^ 29)⟩,
       ⟨((-388935855 : Dyadic) * half ^ 30),
        ((-152655233 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-709650971 : Dyadic) * half ^ 30),
        ((-414362613 : Dyadic) * half ^ 31)⟩,
       ⟨((-404340505 : Dyadic) * half ^ 30),
        ((363509097 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((313942923 : Dyadic) * half ^ 30),
        ((-293032895 : Dyadic) * half ^ 30)⟩,
       ⟨((58390881 : Dyadic) * half ^ 29),
        ((158071893 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word21Step40 :
    word21Chunk40.foldl (fun acc a => a.applyPacked acc)
      word21State40 = word21State41 := by decide +kernel

private def word21Chunk41 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word21State42 : PackedMat2 :=
    ⟨⟨⟨((219667797 : Dyadic) * half ^ 29),
        ((-520133 : Dyadic) * half ^ 23)⟩,
       ⟨((-95532975 : Dyadic) * half ^ 28),
        ((-616489013 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((702403453 : Dyadic) * half ^ 31),
        ((-723248667 : Dyadic) * half ^ 31)⟩,
       ⟨((-930438225 : Dyadic) * half ^ 31),
        ((-165352999 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-930438225 : Dyadic) * half ^ 31),
        ((-165352999 : Dyadic) * half ^ 31)⟩,
       ⟨((702403453 : Dyadic) * half ^ 31),
        ((-723248667 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((95532975 : Dyadic) * half ^ 28),
        ((616489013 : Dyadic) * half ^ 31)⟩,
       ⟨((-219667797 : Dyadic) * half ^ 29),
        ((520133 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word21Step41 :
    word21Chunk41.foldl (fun acc a => a.applyPacked acc)
      word21State41 = word21State42 := by decide +kernel

private def word21Chunk42 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word21State43 : PackedMat2 :=
    ⟨⟨⟨((476108995 : Dyadic) * half ^ 31),
        ((-1718630415 : Dyadic) * half ^ 32)⟩,
       ⟨((-437512759 : Dyadic) * half ^ 30),
        ((77952309 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1093955897 : Dyadic) * half ^ 32),
        ((399834801 : Dyadic) * half ^ 30)⟩,
       ⟨((-1478339891 : Dyadic) * half ^ 32),
        ((-54028605 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((853698207 : Dyadic) * half ^ 31),
        ((643073947 : Dyadic) * half ^ 31)⟩,
       ⟨((-745640997 : Dyadic) * half ^ 31),
        ((192191997 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1874535033 : Dyadic) * half ^ 32),
        ((-1351134513 : Dyadic) * half ^ 32)⟩,
       ⟨((-1562725797 : Dyadic) * half ^ 32),
        ((-398916523 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word21Step42 :
    word21Chunk42.foldl (fun acc a => a.applyPacked acc)
      word21State42 = word21State43 := by decide +kernel

private def word21Chunk43 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word21State44 : PackedMat2 :=
    ⟨⟨⟨((-3165549685 : Dyadic) * half ^ 33),
        ((344128081 : Dyadic) * half ^ 32)⟩,
       ⟨((2357983123 : Dyadic) * half ^ 33),
        ((-1869342247 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((6427069335 : Dyadic) * half ^ 33),
        ((1046108489 : Dyadic) * half ^ 33)⟩,
       ⟨((-74376513 : Dyadic) * half ^ 33),
        ((57488429 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-74376513 : Dyadic) * half ^ 33),
        ((57488429 : Dyadic) * half ^ 28)⟩,
       ⟨((6427069335 : Dyadic) * half ^ 33),
        ((1046108489 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-2357983123 : Dyadic) * half ^ 33),
        ((1869342247 : Dyadic) * half ^ 33)⟩,
       ⟨((3165549685 : Dyadic) * half ^ 33),
        ((-344128081 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word21Step43 :
    word21Chunk43.foldl (fun acc a => a.applyPacked acc)
      word21State43 = word21State44 := by decide +kernel

private def word21Chunk44 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word21State45 : PackedMat2 :=
    ⟨⟨⟨((952133709 : Dyadic) * half ^ 33),
        ((1880138973 : Dyadic) * half ^ 34)⟩,
       ⟨((-3848877709 : Dyadic) * half ^ 33),
        ((6296962209 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((418459947 : Dyadic) * half ^ 31),
        ((623902861 : Dyadic) * half ^ 31)⟩,
       ⟨((3774365191 : Dyadic) * half ^ 33),
        ((933374595 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2181180317 : Dyadic) * half ^ 32),
        ((-5448204979 : Dyadic) * half ^ 34)⟩,
       ⟨((-314431127 : Dyadic) * half ^ 32),
        ((2100525403 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((4088550591 : Dyadic) * half ^ 33),
        ((-45261625 : Dyadic) * half ^ 28)⟩,
       ⟨((-1104205809 : Dyadic) * half ^ 32),
        ((2400505709 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word21Step44 :
    word21Chunk44.foldl (fun acc a => a.applyPacked acc)
      word21State44 = word21State45 := by decide +kernel

private def word21Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word21State46 : PackedMat2 :=
    ⟨⟨⟨((9518424263 : Dyadic) * half ^ 34),
        ((-9414092639 : Dyadic) * half ^ 35)⟩,
       ⟨((-631336627 : Dyadic) * half ^ 31),
        ((-2072115215 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4470246849 : Dyadic) * half ^ 34),
        ((1904918069 : Dyadic) * half ^ 35)⟩,
       ⟨((2226973329 : Dyadic) * half ^ 32),
        ((7928502671 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3011792301 : Dyadic) * half ^ 34),
        ((-4437646467 : Dyadic) * half ^ 35)⟩,
       ⟨((-2458355185 : Dyadic) * half ^ 33),
        ((-13378140165 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((458873589 : Dyadic) * half ^ 31),
        ((-14569117279 : Dyadic) * half ^ 35)⟩,
       ⟨((-5743103927 : Dyadic) * half ^ 34),
        ((4467731247 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word21Step45 :
    word21Chunk45.foldl (fun acc a => a.applyPacked acc)
      word21State45 = word21State46 := by decide +kernel

private def word21Chunk46 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word21State47 : PackedMat2 :=
    ⟨⟨⟨((7899660047 : Dyadic) * half ^ 35),
        ((4256899841 : Dyadic) * half ^ 36)⟩,
       ⟨((-11545694949 : Dyadic) * half ^ 34),
        ((-12108412807 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((8868988155 : Dyadic) * half ^ 35),
        ((-22335620561 : Dyadic) * half ^ 36)⟩,
       ⟨((-5446218953 : Dyadic) * half ^ 34),
        ((10570066093 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-8868988155 : Dyadic) * half ^ 35),
        ((22335620561 : Dyadic) * half ^ 36)⟩,
       ⟨((-5446218953 : Dyadic) * half ^ 34),
        ((10570066093 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((7899660047 : Dyadic) * half ^ 35),
        ((4256899841 : Dyadic) * half ^ 36)⟩,
       ⟨((11545694949 : Dyadic) * half ^ 34),
        ((12108412807 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word21Step46 :
    word21Chunk46.foldl (fun acc a => a.applyPacked acc)
      word21State46 = word21State47 := by decide +kernel

private def word21Chunk47 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word21State48 : PackedMat2 :=
    ⟨⟨⟨((9410266479 : Dyadic) * half ^ 35),
        ((47170472439 : Dyadic) * half ^ 37)⟩,
       ⟨((-21888511519 : Dyadic) * half ^ 36),
        ((-9914320707 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-14108508127 : Dyadic) * half ^ 35),
        ((28744990297 : Dyadic) * half ^ 37)⟩,
       ⟨((-5381569169 : Dyadic) * half ^ 36),
        ((54572427953 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-14108508127 : Dyadic) * half ^ 35),
        ((28744990297 : Dyadic) * half ^ 37)⟩,
       ⟨((5381569169 : Dyadic) * half ^ 36),
        ((-54572427953 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-9410266479 : Dyadic) * half ^ 35),
        ((-47170472439 : Dyadic) * half ^ 37)⟩,
       ⟨((-21888511519 : Dyadic) * half ^ 36),
        ((-9914320707 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word21Step47 :
    word21Chunk47.foldl (fun acc a => a.applyPacked acc)
      word21State47 = word21State48 := by decide +kernel

private def word21Chunk48 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word21State49 : PackedMat2 :=
    ⟨⟨⟨((28072632565 : Dyadic) * half ^ 36),
        ((12359969769 : Dyadic) * half ^ 37)⟩,
       ⟨((-16376248437 : Dyadic) * half ^ 36),
        ((4624004353 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((5584162893 : Dyadic) * half ^ 37),
        ((-75857752469 : Dyadic) * half ^ 37)⟩,
       ⟨((44983487565 : Dyadic) * half ^ 37),
        ((7456936699 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((5207168073 : Dyadic) * half ^ 33),
        ((38475903 : Dyadic) * half ^ 28)⟩,
       ⟨((-34200407885 : Dyadic) * half ^ 36),
        ((25283825229 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-6136047643 : Dyadic) * half ^ 37),
        ((22224440501 : Dyadic) * half ^ 36)⟩,
       ⟨((-30855987181 : Dyadic) * half ^ 37),
        ((-91378001 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word21Step48 :
    word21Chunk48.foldl (fun acc a => a.applyPacked acc)
      word21State48 = word21State49 := by decide +kernel

private def word21Chunk49 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word21State50 : PackedMat2 :=
    ⟨⟨⟨((63056599305 : Dyadic) * half ^ 38),
        ((-38208504751 : Dyadic) * half ^ 38)⟩,
       ⟨((48153812389 : Dyadic) * half ^ 38),
        ((-6962365951 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-252844257633 : Dyadic) * half ^ 38),
        ((-14232743575 : Dyadic) * half ^ 38)⟩,
       ⟨((-12254460583 : Dyadic) * half ^ 38),
        ((-3094561873 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((12254460583 : Dyadic) * half ^ 38),
        ((3094561873 : Dyadic) * half ^ 36)⟩,
       ⟨((252844257633 : Dyadic) * half ^ 38),
        ((14232743575 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((48153812389 : Dyadic) * half ^ 38),
        ((-6962365951 : Dyadic) * half ^ 36)⟩,
       ⟨((63056599305 : Dyadic) * half ^ 38),
        ((-38208504751 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word21Step49 :
    word21Chunk49.foldl (fun acc a => a.applyPacked acc)
      word21State49 = word21State50 := by decide +kernel

private def word21Chunk50 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word21State51 : PackedMat2 :=
    ⟨⟨⟨((-7669770363 : Dyadic) * half ^ 35),
        ((105600480817 : Dyadic) * half ^ 38)⟩,
       ⟨((-9626659685 : Dyadic) * half ^ 38),
        ((-61302025735 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-13285033757 : Dyadic) * half ^ 38),
        ((-233014616683 : Dyadic) * half ^ 39)⟩,
       ⟨((-105771392031 : Dyadic) * half ^ 38),
        ((-82092410005 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-1230886823 : Dyadic) * half ^ 31),
        ((-29764106447 : Dyadic) * half ^ 37)⟩,
       ⟨((-75461103339 : Dyadic) * half ^ 38),
        ((46243179137 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-22149227541 : Dyadic) * half ^ 37),
        ((70984822589 : Dyadic) * half ^ 39)⟩,
       ⟨((-20862813319 : Dyadic) * half ^ 35),
        ((51731503219 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word21Step50 :
    word21Chunk50.foldl (fun acc a => a.applyPacked acc)
      word21State50 = word21State51 := by decide +kernel

private def word21Chunk51 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word21State52 : PackedMat2 :=
    ⟨⟨⟨((80333815797 : Dyadic) * half ^ 39),
        ((-259384839171 : Dyadic) * half ^ 40)⟩,
       ⟨((-20723537869 : Dyadic) * half ^ 37),
        ((355306548789 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-703132633 : Dyadic) * half ^ 39),
        ((478578207551 : Dyadic) * half ^ 40)⟩,
       ⟨((-115984830811 : Dyadic) * half ^ 38),
        ((-218247129247 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((703132633 : Dyadic) * half ^ 39),
        ((-478578207551 : Dyadic) * half ^ 40)⟩,
       ⟨((-115984830811 : Dyadic) * half ^ 38),
        ((-218247129247 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((80333815797 : Dyadic) * half ^ 39),
        ((-259384839171 : Dyadic) * half ^ 40)⟩,
       ⟨((20723537869 : Dyadic) * half ^ 37),
        ((-355306548789 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word21Step51 :
    word21Chunk51.foldl (fun acc a => a.applyPacked acc)
      word21State51 = word21State52 := by decide +kernel

private def word21Chunk52 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word21State53 : PackedMat2 :=
    ⟨⟨⟨((-304615921431 : Dyadic) * half ^ 39),
        ((164620567039 : Dyadic) * half ^ 41)⟩,
       ⟨((-388102377531 : Dyadic) * half ^ 40),
        ((-195263155923 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((105113624235 : Dyadic) * half ^ 39),
        ((721696400369 : Dyadic) * half ^ 41)⟩,
       ⟨((157782087675 : Dyadic) * half ^ 40),
        ((-806240137791 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((105113624235 : Dyadic) * half ^ 39),
        ((721696400369 : Dyadic) * half ^ 41)⟩,
       ⟨((-157782087675 : Dyadic) * half ^ 40),
        ((806240137791 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((304615921431 : Dyadic) * half ^ 39),
        ((-164620567039 : Dyadic) * half ^ 41)⟩,
       ⟨((-388102377531 : Dyadic) * half ^ 40),
        ((-195263155923 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word21Step52 :
    word21Chunk52.foldl (fun acc a => a.applyPacked acc)
      word21State52 = word21State53 := by decide +kernel

private def word21Chunk53 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word21State54 : PackedMat2 :=
    ⟨⟨⟨((323759197503 : Dyadic) * half ^ 41),
        ((319606997517 : Dyadic) * half ^ 42)⟩,
       ⟨((151724092759 : Dyadic) * half ^ 39),
        ((-1180321743331 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1767449832725 : Dyadic) * half ^ 41),
        ((476944341713 : Dyadic) * half ^ 42)⟩,
       ⟨((76321726445 : Dyadic) * half ^ 39),
        ((-753775923477 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1767449832725 : Dyadic) * half ^ 41),
        ((-476944341713 : Dyadic) * half ^ 42)⟩,
       ⟨((76321726445 : Dyadic) * half ^ 39),
        ((-753775923477 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((323759197503 : Dyadic) * half ^ 41),
        ((319606997517 : Dyadic) * half ^ 42)⟩,
       ⟨((-151724092759 : Dyadic) * half ^ 39),
        ((1180321743331 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word21Step53 :
    word21Chunk53.foldl (fun acc a => a.applyPacked acc)
      word21State53 = word21State54 := by decide +kernel

private def word21Chunk54 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word21State55 : PackedMat2 :=
    ⟨⟨⟨((1053955286285 : Dyadic) * half ^ 42),
        ((726882162775 : Dyadic) * half ^ 41)⟩,
       ⟨((-124595707665 : Dyadic) * half ^ 42),
        ((44049587799 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((3906202885 : Dyadic) * half ^ 34),
        ((1491925003089 : Dyadic) * half ^ 42)⟩,
       ⟨((1032136488473 : Dyadic) * half ^ 41),
        ((-364914531505 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((2951583129109 : Dyadic) * half ^ 42),
        ((-532142519193 : Dyadic) * half ^ 42)⟩,
       ⟨((-32266877069 : Dyadic) * half ^ 42),
        ((-1532130457753 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-1333657373 : Dyadic) * half ^ 32),
        ((-589275496975 : Dyadic) * half ^ 42)⟩,
       ⟨((385465875287 : Dyadic) * half ^ 40),
        ((232339894655 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word21Step54 :
    word21Chunk54.foldl (fun acc a => a.applyPacked acc)
      word21State54 = word21State55 := by decide +kernel

private def word21Chunk55 : List Letter := [.t, .h]
private def word21State56 : PackedMat2 :=
    ⟨⟨⟨((2945689328639 : Dyadic) * half ^ 42),
        ((2053943224845 : Dyadic) * half ^ 43)⟩,
       ⟨((773878650809 : Dyadic) * half ^ 41),
        ((-2188868684611 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((38160677539 : Dyadic) * half ^ 42),
        ((-53967347725 : Dyadic) * half ^ 43)⟩,
       ⟨((-685779475211 : Dyadic) * half ^ 41),
        ((1939677269281 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-38160677539 : Dyadic) * half ^ 42),
        ((53967347725 : Dyadic) * half ^ 43)⟩,
       ⟨((-685779475211 : Dyadic) * half ^ 41),
        ((1939677269281 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((2945689328639 : Dyadic) * half ^ 42),
        ((2053943224845 : Dyadic) * half ^ 43)⟩,
       ⟨((-773878650809 : Dyadic) * half ^ 41),
        ((2188868684611 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word21Step55 :
    word21Chunk55.foldl (fun acc a => a.applyPacked acc)
      word21State55 = word21State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word21_check : check word21 21 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word21 = word21State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word21Chunk0 ++ word21Chunk1 ++ word21Chunk2 ++ word21Chunk3 ++
      word21Chunk4 ++ word21Chunk5 ++ word21Chunk6 ++ word21Chunk7 ++
      word21Chunk8 ++ word21Chunk9 ++ word21Chunk10 ++ word21Chunk11 ++
      word21Chunk12 ++ word21Chunk13 ++ word21Chunk14 ++ word21Chunk15 ++
      word21Chunk16 ++ word21Chunk17 ++ word21Chunk18 ++ word21Chunk19 ++
      word21Chunk20 ++ word21Chunk21 ++ word21Chunk22 ++ word21Chunk23 ++
      word21Chunk24 ++ word21Chunk25 ++ word21Chunk26 ++ word21Chunk27 ++
      word21Chunk28 ++ word21Chunk29 ++ word21Chunk30 ++ word21Chunk31 ++
      word21Chunk32 ++ word21Chunk33 ++ word21Chunk34 ++ word21Chunk35 ++
      word21Chunk36 ++ word21Chunk37 ++ word21Chunk38 ++ word21Chunk39 ++
      word21Chunk40 ++ word21Chunk41 ++ word21Chunk42 ++ word21Chunk43 ++
      word21Chunk44 ++ word21Chunk45 ++ word21Chunk46 ++ word21Chunk47 ++
      word21Chunk48 ++ word21Chunk49 ++ word21Chunk50 ++ word21Chunk51 ++
      word21Chunk52 ++ word21Chunk53 ++ word21Chunk54 ++ word21Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word21Step0, word21Step1, word21Step2, word21Step3, word21Step4,
      word21Step5, word21Step6, word21Step7, word21Step8, word21Step9,
      word21Step10, word21Step11, word21Step12, word21Step13, word21Step14,
      word21Step15, word21Step16, word21Step17, word21Step18, word21Step19,
      word21Step20, word21Step21, word21Step22, word21Step23, word21Step24,
      word21Step25, word21Step26, word21Step27, word21Step28, word21Step29,
      word21Step30, word21Step31, word21Step32, word21Step33, word21Step34,
      word21Step35, word21Step36, word21Step37, word21Step38, word21Step39,
      word21Step40, word21Step41, word21Step42, word21Step43, word21Step44,
      word21Step45, word21Step46, word21Step47, word21Step48, word21Step49,
      word21Step50, word21Step51, word21Step52, word21Step53, word21Step54,
      word21Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

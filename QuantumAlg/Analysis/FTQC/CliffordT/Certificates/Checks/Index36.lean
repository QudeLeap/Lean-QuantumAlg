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
private def word36Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word36State1 : PackedMat2 :=
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
private lemma word36Step0 :
    word36Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word36State1 := by decide +kernel

private def word36Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word36State2 : PackedMat2 :=
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
private lemma word36Step1 :
    word36Chunk1.foldl (fun acc a => a.applyPacked acc)
      word36State1 = word36State2 := by decide +kernel

private def word36Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word36State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word36Step2 :
    word36Chunk2.foldl (fun acc a => a.applyPacked acc)
      word36State2 = word36State3 := by decide +kernel

private def word36Chunk3 : List Letter := [.s, .s, .h, .s, .t, .h, .s, .t]
private def word36State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word36Step3 :
    word36Chunk3.foldl (fun acc a => a.applyPacked acc)
      word36State3 = word36State4 := by decide +kernel

private def word36Chunk4 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word36State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word36Step4 :
    word36Chunk4.foldl (fun acc a => a.applyPacked acc)
      word36State4 = word36State5 := by decide +kernel

private def word36Chunk5 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word36Step5 :
    word36Chunk5.foldl (fun acc a => a.applyPacked acc)
      word36State5 = word36State6 := by decide +kernel

private def word36Chunk6 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word36State7 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word36Step6 :
    word36Chunk6.foldl (fun acc a => a.applyPacked acc)
      word36State6 = word36State7 := by decide +kernel

private def word36Chunk7 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word36State8 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word36Step7 :
    word36Chunk7.foldl (fun acc a => a.applyPacked acc)
      word36State7 = word36State8 := by decide +kernel

private def word36Chunk8 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word36State9 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((-15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((15 : Dyadic) * half ^ 6)⟩,
       ⟨((-27 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word36Step8 :
    word36Chunk8.foldl (fun acc a => a.applyPacked acc)
      word36State8 = word36State9 := by decide +kernel

private def word36Chunk9 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State10 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 6),
        ((49 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((23 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((23 : Dyadic) * half ^ 6),
        ((21 : Dyadic) * half ^ 7)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 6),
        ((-49 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 6),
        ((43 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 4),
        ((21 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word36Step9 :
    word36Chunk9.foldl (fun acc a => a.applyPacked acc)
      word36State9 = word36State10 := by decide +kernel

private def word36Chunk10 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word36State11 : PackedMat2 :=
    ⟨⟨⟨((21 : Dyadic) * half ^ 5),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((-25 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((-9 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((37 : Dyadic) * half ^ 7),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 7),
        ((17 : Dyadic) * half ^ 7)⟩,
       ⟨((11 : Dyadic) * half ^ 7),
        ((67 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word36Step10 :
    word36Chunk10.foldl (fun acc a => a.applyPacked acc)
      word36State10 = word36State11 := by decide +kernel

private def word36Chunk11 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word36State12 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 7),
        ((53 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((67 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((43 : Dyadic) * half ^ 8)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((139 : Dyadic) * half ^ 8),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((-53 : Dyadic) * half ^ 8),
        ((15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-173 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 8)⟩,
       ⟨((-39 : Dyadic) * half ^ 8),
        ((-9 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word36Step11 :
    word36Chunk11.foldl (fun acc a => a.applyPacked acc)
      word36State11 = word36State12 := by decide +kernel

private def word36Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word36State13 : PackedMat2 :=
    ⟨⟨⟨((181 : Dyadic) * half ^ 9),
        ((-121 : Dyadic) * half ^ 9)⟩,
       ⟨((207 : Dyadic) * half ^ 9),
        ((-19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-131 : Dyadic) * half ^ 9),
        ((-185 : Dyadic) * half ^ 9)⟩,
       ⟨((231 : Dyadic) * half ^ 9),
        ((29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((131 : Dyadic) * half ^ 9),
        ((185 : Dyadic) * half ^ 9)⟩,
       ⟨((231 : Dyadic) * half ^ 9),
        ((29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((181 : Dyadic) * half ^ 9),
        ((-121 : Dyadic) * half ^ 9)⟩,
       ⟨((-207 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word36Step12 :
    word36Chunk12.foldl (fun acc a => a.applyPacked acc)
      word36State12 = word36State13 := by decide +kernel

private def word36Chunk13 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word36State14 : PackedMat2 :=
    ⟨⟨⟨((591 : Dyadic) * half ^ 10),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((-197 : Dyadic) * half ^ 10),
        ((359 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-385 : Dyadic) * half ^ 10),
        ((-73 : Dyadic) * half ^ 8)⟩,
       ⟨((-249 : Dyadic) * half ^ 10),
        ((101 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-385 : Dyadic) * half ^ 10),
        ((-73 : Dyadic) * half ^ 8)⟩,
       ⟨((249 : Dyadic) * half ^ 10),
        ((-101 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-591 : Dyadic) * half ^ 10),
        ((7 : Dyadic) * half ^ 8)⟩,
       ⟨((-197 : Dyadic) * half ^ 10),
        ((359 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word36Step13 :
    word36Chunk13.foldl (fun acc a => a.applyPacked acc)
      word36State13 = word36State14 := by decide +kernel

private def word36Chunk14 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word36State15 : PackedMat2 :=
    ⟨⟨⟨((263 : Dyadic) * half ^ 10),
        ((131 : Dyadic) * half ^ 9)⟩,
       ⟨((265 : Dyadic) * half ^ 9),
        ((-31 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-257 : Dyadic) * half ^ 10)⟩,
       ⟨((7 : Dyadic) * half ^ 10),
        ((-225 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-193 : Dyadic) * half ^ 10),
        ((-121 : Dyadic) * half ^ 11)⟩,
       ⟨((-707 : Dyadic) * half ^ 10),
        ((135 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((81 : Dyadic) * half ^ 8),
        ((-267 : Dyadic) * half ^ 11)⟩,
       ⟨((-25 : Dyadic) * half ^ 7),
        ((-793 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word36Step14 :
    word36Chunk14.foldl (fun acc a => a.applyPacked acc)
      word36State14 = word36State15 := by decide +kernel

private def word36Chunk15 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word36State16 : PackedMat2 :=
    ⟨⟨⟨((-231 : Dyadic) * half ^ 10),
        ((-1567 : Dyadic) * half ^ 12)⟩,
       ⟨((61 : Dyadic) * half ^ 11),
        ((927 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-59 : Dyadic) * half ^ 8),
        ((1659 : Dyadic) * half ^ 12)⟩,
       ⟨((-849 : Dyadic) * half ^ 11),
        ((-3 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((831 : Dyadic) * half ^ 11),
        ((377 : Dyadic) * half ^ 12)⟩,
       ⟨((-207 : Dyadic) * half ^ 9),
        ((1321 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((1247 : Dyadic) * half ^ 11),
        ((523 : Dyadic) * half ^ 12)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((-401 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word36Step15 :
    word36Chunk15.foldl (fun acc a => a.applyPacked acc)
      word36State15 = word36State16 := by decide +kernel

private def word36Chunk16 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word36State17 : PackedMat2 :=
    ⟨⟨⟨((-289 : Dyadic) * half ^ 10),
        ((-1755 : Dyadic) * half ^ 12)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((-181 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((1023 : Dyadic) * half ^ 11),
        ((-627 : Dyadic) * half ^ 11)⟩,
       ⟨((-67 : Dyadic) * half ^ 9),
        ((-483 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 9),
        ((-483 : Dyadic) * half ^ 12)⟩,
       ⟨((1023 : Dyadic) * half ^ 11),
        ((-627 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((181 : Dyadic) * half ^ 10)⟩,
       ⟨((289 : Dyadic) * half ^ 10),
        ((1755 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word36Step16 :
    word36Chunk16.foldl (fun acc a => a.applyPacked acc)
      word36State16 = word36State17 := by decide +kernel

private def word36Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word36State18 : PackedMat2 :=
    ⟨⟨⟨((-2355 : Dyadic) * half ^ 13),
        ((-1723 : Dyadic) * half ^ 13)⟩,
       ⟨((-4341 : Dyadic) * half ^ 13),
        ((-173 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-3003 : Dyadic) * half ^ 13),
        ((2143 : Dyadic) * half ^ 13)⟩,
       ⟨((3559 : Dyadic) * half ^ 13),
        ((-255 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((3003 : Dyadic) * half ^ 13),
        ((-2143 : Dyadic) * half ^ 13)⟩,
       ⟨((3559 : Dyadic) * half ^ 13),
        ((-255 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-2355 : Dyadic) * half ^ 13),
        ((-1723 : Dyadic) * half ^ 13)⟩,
       ⟨((4341 : Dyadic) * half ^ 13),
        ((173 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word36Step17 :
    word36Chunk17.foldl (fun acc a => a.applyPacked acc)
      word36State17 = word36State18 := by decide +kernel

private def word36Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word36State19 : PackedMat2 :=
    ⟨⟨⟨((-1165 : Dyadic) * half ^ 14),
        ((765 : Dyadic) * half ^ 13)⟩,
       ⟨((-6565 : Dyadic) * half ^ 14),
        ((-2015 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((3731 : Dyadic) * half ^ 14),
        ((-2923 : Dyadic) * half ^ 13)⟩,
       ⟨((11279 : Dyadic) * half ^ 14),
        ((919 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4927 : Dyadic) * half ^ 14),
        ((7505 : Dyadic) * half ^ 14)⟩,
       ⟨((-6765 : Dyadic) * half ^ 14),
        ((-1887 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((485 : Dyadic) * half ^ 14),
        ((3865 : Dyadic) * half ^ 14)⟩,
       ⟨((-3545 : Dyadic) * half ^ 14),
        ((-675 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word36Step18 :
    word36Chunk18.foldl (fun acc a => a.applyPacked acc)
      word36State18 = word36State19 := by decide +kernel

private def word36Chunk19 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word36State20 : PackedMat2 :=
    ⟨⟨⟨((365 : Dyadic) * half ^ 10),
        ((1727 : Dyadic) * half ^ 14)⟩,
       ⟨((-8101 : Dyadic) * half ^ 14),
        ((135 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-4465 : Dyadic) * half ^ 14),
        ((215 : Dyadic) * half ^ 11)⟩,
       ⟨((5565 : Dyadic) * half ^ 13),
        ((339 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-91 : Dyadic) * half ^ 12),
        ((15595 : Dyadic) * half ^ 15)⟩,
       ⟨((769 : Dyadic) * half ^ 12),
        ((6665 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-433 : Dyadic) * half ^ 14),
        ((13941 : Dyadic) * half ^ 15)⟩,
       ⟨((-3887 : Dyadic) * half ^ 14),
        ((2261 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word36Step19 :
    word36Chunk19.foldl (fun acc a => a.applyPacked acc)
      word36State19 = word36State20 := by decide +kernel

private def word36Chunk20 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word36State21 : PackedMat2 :=
    ⟨⟨⟨((1291 : Dyadic) * half ^ 12),
        ((9657 : Dyadic) * half ^ 15)⟩,
       ⟨((10939 : Dyadic) * half ^ 15),
        ((1899 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((12627 : Dyadic) * half ^ 15),
        ((767 : Dyadic) * half ^ 14)⟩,
       ⟨((8511 : Dyadic) * half ^ 14),
        ((-4719 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((12627 : Dyadic) * half ^ 15),
        ((767 : Dyadic) * half ^ 14)⟩,
       ⟨((-8511 : Dyadic) * half ^ 14),
        ((4719 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1291 : Dyadic) * half ^ 12),
        ((-9657 : Dyadic) * half ^ 15)⟩,
       ⟨((10939 : Dyadic) * half ^ 15),
        ((1899 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word36Step20 :
    word36Chunk20.foldl (fun acc a => a.applyPacked acc)
      word36State20 = word36State21 := by decide +kernel

private def word36Chunk21 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word36State22 : PackedMat2 :=
    ⟨⟨⟨((217 : Dyadic) * half ^ 16),
        ((29917 : Dyadic) * half ^ 17)⟩,
       ⟨((16215 : Dyadic) * half ^ 15),
        ((8645 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-1971 : Dyadic) * half ^ 16),
        ((70907 : Dyadic) * half ^ 17)⟩,
       ⟨((3869 : Dyadic) * half ^ 15),
        ((-19009 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-22479 : Dyadic) * half ^ 15),
        ((9709 : Dyadic) * half ^ 17)⟩,
       ⟨((25949 : Dyadic) * half ^ 16),
        ((5767 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((2659 : Dyadic) * half ^ 14),
        ((-32213 : Dyadic) * half ^ 17)⟩,
       ⟨((-19281 : Dyadic) * half ^ 16),
        ((-32647 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word36Step21 :
    word36Chunk21.foldl (fun acc a => a.applyPacked acc)
      word36State21 = word36State22 := by decide +kernel

private def word36Chunk22 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word36State23 : PackedMat2 :=
    ⟨⟨⟨((-66969 : Dyadic) * half ^ 17),
        ((-30533 : Dyadic) * half ^ 17)⟩,
       ⟨((13017 : Dyadic) * half ^ 17),
        ((29843 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((49827 : Dyadic) * half ^ 17),
        ((-23455 : Dyadic) * half ^ 16)⟩,
       ⟨((-3041 : Dyadic) * half ^ 17),
        ((15759 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((3041 : Dyadic) * half ^ 17),
        ((-15759 : Dyadic) * half ^ 16)⟩,
       ⟨((-49827 : Dyadic) * half ^ 17),
        ((23455 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((13017 : Dyadic) * half ^ 17),
        ((29843 : Dyadic) * half ^ 17)⟩,
       ⟨((-66969 : Dyadic) * half ^ 17),
        ((-30533 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word36Step22 :
    word36Chunk22.foldl (fun acc a => a.applyPacked acc)
      word36State22 = word36State23 := by decide +kernel

private def word36Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word36State24 : PackedMat2 :=
    ⟨⟨⟨((4345 : Dyadic) * half ^ 18),
        ((-61623 : Dyadic) * half ^ 17)⟩,
       ⟨((-22675 : Dyadic) * half ^ 18),
        ((5877 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-151155 : Dyadic) * half ^ 18),
        ((-5421 : Dyadic) * half ^ 16)⟩,
       ⟨((113553 : Dyadic) * half ^ 18),
        ((-22975 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-151155 : Dyadic) * half ^ 18),
        ((-5421 : Dyadic) * half ^ 16)⟩,
       ⟨((-113553 : Dyadic) * half ^ 18),
        ((22975 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-4345 : Dyadic) * half ^ 18),
        ((61623 : Dyadic) * half ^ 17)⟩,
       ⟨((-22675 : Dyadic) * half ^ 18),
        ((5877 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word36Step23 :
    word36Chunk23.foldl (fun acc a => a.applyPacked acc)
      word36State23 = word36State24 := by decide +kernel

private def word36Chunk24 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word36State25 : PackedMat2 :=
    ⟨⟨⟨((-213739 : Dyadic) * half ^ 19),
        ((-17635 : Dyadic) * half ^ 16)⟩,
       ⟨((-93689 : Dyadic) * half ^ 19),
        ((-100067 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((231279 : Dyadic) * half ^ 19),
        ((-59 : Dyadic) * half ^ 12)⟩,
       ⟨((236505 : Dyadic) * half ^ 19),
        ((-159755 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((167307 : Dyadic) * half ^ 19),
        ((-58473 : Dyadic) * half ^ 17)⟩,
       ⟨((-152203 : Dyadic) * half ^ 19),
        ((2613 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-241147 : Dyadic) * half ^ 19),
        ((-76857 : Dyadic) * half ^ 18)⟩,
       ⟨((-41013 : Dyadic) * half ^ 19),
        ((-60025 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word36Step24 :
    word36Chunk24.foldl (fun acc a => a.applyPacked acc)
      word36State24 = word36State25 := by decide +kernel

private def word36Chunk25 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word36State26 : PackedMat2 :=
    ⟨⟨⟨((205445 : Dyadic) * half ^ 19),
        ((2469 : Dyadic) * half ^ 20)⟩,
       ⟨((-50975 : Dyadic) * half ^ 18),
        ((-234229 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((326669 : Dyadic) * half ^ 19),
        ((-40339 : Dyadic) * half ^ 20)⟩,
       ⟨((3367 : Dyadic) * half ^ 16),
        ((-416149 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-3367 : Dyadic) * half ^ 16),
        ((416149 : Dyadic) * half ^ 20)⟩,
       ⟨((-326669 : Dyadic) * half ^ 19),
        ((40339 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-50975 : Dyadic) * half ^ 18),
        ((-234229 : Dyadic) * half ^ 20)⟩,
       ⟨((205445 : Dyadic) * half ^ 19),
        ((2469 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word36Step25 :
    word36Chunk25.foldl (fun acc a => a.applyPacked acc)
      word36State25 = word36State26 := by decide +kernel

private def word36Chunk26 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State27 : PackedMat2 :=
    ⟨⟨⟨((271623 : Dyadic) * half ^ 20),
        ((916793 : Dyadic) * half ^ 21)⟩,
       ⟨((-111965 : Dyadic) * half ^ 18),
        ((328743 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((127995 : Dyadic) * half ^ 20),
        ((-813203 : Dyadic) * half ^ 21)⟩,
       ⟨((-14979 : Dyadic) * half ^ 19),
        ((-76597 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((368303 : Dyadic) * half ^ 20),
        ((-157953 : Dyadic) * half ^ 21)⟩,
       ⟨((-111225 : Dyadic) * half ^ 18),
        ((98037 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((294025 : Dyadic) * half ^ 20),
        ((719483 : Dyadic) * half ^ 21)⟩,
       ⟨((-38923 : Dyadic) * half ^ 16),
        ((176237 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word36Step26 :
    word36Chunk26.foldl (fun acc a => a.applyPacked acc)
      word36State26 = word36State27 := by decide +kernel

private def word36Chunk27 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word36State28 : PackedMat2 :=
    ⟨⟨⟨((1394611 : Dyadic) * half ^ 21),
        ((72775 : Dyadic) * half ^ 20)⟩,
       ⟨((472371 : Dyadic) * half ^ 21),
        ((208569 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-1231105 : Dyadic) * half ^ 21),
        ((330665 : Dyadic) * half ^ 21)⟩,
       ⟨((323021 : Dyadic) * half ^ 21),
        ((21837 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-323021 : Dyadic) * half ^ 21),
        ((-21837 : Dyadic) * half ^ 21)⟩,
       ⟨((1231105 : Dyadic) * half ^ 21),
        ((-330665 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((472371 : Dyadic) * half ^ 21),
        ((208569 : Dyadic) * half ^ 20)⟩,
       ⟨((1394611 : Dyadic) * half ^ 21),
        ((72775 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word36Step27 :
    word36Chunk27.foldl (fun acc a => a.applyPacked acc)
      word36State27 = word36State28 := by decide +kernel

private def word36Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word36State29 : PackedMat2 :=
    ⟨⟨⟨((-490099 : Dyadic) * half ^ 22),
        ((219317 : Dyadic) * half ^ 19)⟩,
       ⟨((2581389 : Dyadic) * half ^ 22),
        ((163879 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((66721 : Dyadic) * half ^ 22),
        ((-395911 : Dyadic) * half ^ 21)⟩,
       ⟨((-1750119 : Dyadic) * half ^ 22),
        ((-279805 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((66721 : Dyadic) * half ^ 22),
        ((-395911 : Dyadic) * half ^ 21)⟩,
       ⟨((1750119 : Dyadic) * half ^ 22),
        ((279805 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((490099 : Dyadic) * half ^ 22),
        ((-219317 : Dyadic) * half ^ 19)⟩,
       ⟨((2581389 : Dyadic) * half ^ 22),
        ((163879 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word36Step28 :
    word36Chunk28.foldl (fun acc a => a.applyPacked acc)
      word36State28 = word36State29 := by decide +kernel

private def word36Chunk29 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State30 : PackedMat2 :=
    ⟨⟨⟨((-173017 : Dyadic) * half ^ 23),
        ((-1267091 : Dyadic) * half ^ 22)⟩,
       ⟨((5156997 : Dyadic) * half ^ 23),
        ((-983221 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1281319 : Dyadic) * half ^ 23),
        ((-458149 : Dyadic) * half ^ 20)⟩,
       ⟨((662355 : Dyadic) * half ^ 23),
        ((-97031 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3762223 : Dyadic) * half ^ 23),
        ((154741 : Dyadic) * half ^ 22)⟩,
       ⟨((3568161 : Dyadic) * half ^ 23),
        ((971837 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-3517403 : Dyadic) * half ^ 23),
        ((1245995 : Dyadic) * half ^ 22)⟩,
       ⟨((-1550961 : Dyadic) * half ^ 23),
        ((-2665007 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word36Step29 :
    word36Chunk29.foldl (fun acc a => a.applyPacked acc)
      word36State29 = word36State30 := by decide +kernel

private def word36Chunk30 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word36State31 : PackedMat2 :=
    ⟨⟨⟨((-1576205 : Dyadic) * half ^ 21),
        ((631547 : Dyadic) * half ^ 24)⟩,
       ⟨((741695 : Dyadic) * half ^ 22),
        ((-1824233 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1094247 : Dyadic) * half ^ 23),
        ((-6369633 : Dyadic) * half ^ 24)⟩,
       ⟨((2250079 : Dyadic) * half ^ 23),
        ((-125379 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3122127 : Dyadic) * half ^ 23),
        ((-1672163 : Dyadic) * half ^ 23)⟩,
       ⟨((1623753 : Dyadic) * half ^ 22),
        ((-144479 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-613945 : Dyadic) * half ^ 22),
        ((3894105 : Dyadic) * half ^ 23)⟩,
       ⟨((-596343 : Dyadic) * half ^ 23),
        ((-2410715 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word36Step30 :
    word36Chunk30.foldl (fun acc a => a.applyPacked acc)
      word36State30 = word36State31 := by decide +kernel

private def word36Chunk31 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word36State32 : PackedMat2 :=
    ⟨⟨⟨((-4202319 : Dyadic) * half ^ 24),
        ((-3455393 : Dyadic) * half ^ 23)⟩,
       ⟨((1141675 : Dyadic) * half ^ 22),
        ((-1532789 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((4963707 : Dyadic) * half ^ 23),
        ((-183551 : Dyadic) * half ^ 20)⟩,
       ⟨((-2124205 : Dyadic) * half ^ 24),
        ((-1674379 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4963707 : Dyadic) * half ^ 23),
        ((183551 : Dyadic) * half ^ 20)⟩,
       ⟨((-2124205 : Dyadic) * half ^ 24),
        ((-1674379 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-4202319 : Dyadic) * half ^ 24),
        ((-3455393 : Dyadic) * half ^ 23)⟩,
       ⟨((-1141675 : Dyadic) * half ^ 22),
        ((1532789 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word36Step31 :
    word36Chunk31.foldl (fun acc a => a.applyPacked acc)
      word36State31 = word36State32 := by decide +kernel

private def word36Chunk32 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word36State33 : PackedMat2 :=
    ⟨⟨⟨((-2313903 : Dyadic) * half ^ 24),
        ((-12710567 : Dyadic) * half ^ 25)⟩,
       ⟨((-20344419 : Dyadic) * half ^ 25),
        ((-124511 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((933709 : Dyadic) * half ^ 25),
        ((-1188911 : Dyadic) * half ^ 24)⟩,
       ⟨((-1131245 : Dyadic) * half ^ 21),
        ((230437 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((933709 : Dyadic) * half ^ 25),
        ((-1188911 : Dyadic) * half ^ 24)⟩,
       ⟨((1131245 : Dyadic) * half ^ 21),
        ((-230437 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((2313903 : Dyadic) * half ^ 24),
        ((12710567 : Dyadic) * half ^ 25)⟩,
       ⟨((-20344419 : Dyadic) * half ^ 25),
        ((-124511 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word36Step32 :
    word36Chunk32.foldl (fun acc a => a.applyPacked acc)
      word36State32 = word36State33 := by decide +kernel

private def word36Chunk33 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word36State34 : PackedMat2 :=
    ⟨⟨⟨((-6385885 : Dyadic) * half ^ 26),
        ((8906687 : Dyadic) * half ^ 27)⟩,
       ⟨((55115 : Dyadic) * half ^ 23),
        ((-85143601 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((135665 : Dyadic) * half ^ 26),
        ((-30478791 : Dyadic) * half ^ 27)⟩,
       ⟨((-1952415 : Dyadic) * half ^ 25),
        ((-25238871 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((327495 : Dyadic) * half ^ 23),
        ((-4040495 : Dyadic) * half ^ 27)⟩,
       ⟨((-27858831 : Dyadic) * half ^ 26),
        ((-3769165 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((5878143 : Dyadic) * half ^ 23),
        ((-6826805 : Dyadic) * half ^ 27)⟩,
       ⟨((38118457 : Dyadic) * half ^ 26),
        ((5944965 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word36Step33 :
    word36Chunk33.foldl (fun acc a => a.applyPacked acc)
      word36State33 = word36State34 := by decide +kernel

private def word36Chunk34 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word36State35 : PackedMat2 :=
    ⟨⟨⟨((1075179 : Dyadic) * half ^ 24),
        ((2618315 : Dyadic) * half ^ 24)⟩,
       ⟨((-5476541 : Dyadic) * half ^ 23),
        ((17513699 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-5047019 : Dyadic) * half ^ 25),
        ((8301757 : Dyadic) * half ^ 27)⟩,
       ⟨((-12331143 : Dyadic) * half ^ 26),
        ((-30858013 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((53414269 : Dyadic) * half ^ 27),
        ((22425181 : Dyadic) * half ^ 27)⟩,
       ⟨((-70017783 : Dyadic) * half ^ 27),
        ((-2237105 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((38460219 : Dyadic) * half ^ 27),
        ((-9877903 : Dyadic) * half ^ 25)⟩,
       ⟨((3432821 : Dyadic) * half ^ 27),
        ((12028261 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word36Step34 :
    word36Chunk34.foldl (fun acc a => a.applyPacked acc)
      word36State34 = word36State35 := by decide +kernel

private def word36Chunk35 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word36State36 : PackedMat2 :=
    ⟨⟨⟨((102644121 : Dyadic) * half ^ 28),
        ((337767 : Dyadic) * half ^ 26)⟩,
       ⟨((110024021 : Dyadic) * half ^ 28),
        ((-97794817 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((123469577 : Dyadic) * half ^ 28),
        ((38298947 : Dyadic) * half ^ 27)⟩,
       ⟨((38684597 : Dyadic) * half ^ 28),
        ((30078903 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((106676797 : Dyadic) * half ^ 28),
        ((81077087 : Dyadic) * half ^ 28)⟩,
       ⟨((46518991 : Dyadic) * half ^ 28),
        ((21196245 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((96443749 : Dyadic) * half ^ 28),
        ((-106334071 : Dyadic) * half ^ 28)⟩,
       ⟨((-99145885 : Dyadic) * half ^ 28),
        ((1844975 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word36Step35 :
    word36Chunk35.foldl (fun acc a => a.applyPacked acc)
      word36State35 = word36State36 := by decide +kernel

private def word36Chunk36 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word36State37 : PackedMat2 :=
    ⟨⟨⟨((-1711365 : Dyadic) * half ^ 27),
        ((86915443 : Dyadic) * half ^ 28)⟩,
       ⟨((-28652329 : Dyadic) * half ^ 28),
        ((123936223 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-9595717 : Dyadic) * half ^ 28),
        ((-85309189 : Dyadic) * half ^ 28)⟩,
       ⟨((23078973 : Dyadic) * half ^ 27),
        ((32821507 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((9595717 : Dyadic) * half ^ 28),
        ((85309189 : Dyadic) * half ^ 28)⟩,
       ⟨((23078973 : Dyadic) * half ^ 27),
        ((32821507 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-1711365 : Dyadic) * half ^ 27),
        ((86915443 : Dyadic) * half ^ 28)⟩,
       ⟨((28652329 : Dyadic) * half ^ 28),
        ((-123936223 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word36Step36 :
    word36Chunk36.foldl (fun acc a => a.applyPacked acc)
      word36State36 = word36State37 := by decide +kernel

private def word36Chunk37 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word36State38 : PackedMat2 :=
    ⟨⟨⟨((-411384545 : Dyadic) * half ^ 29),
        ((9433127 : Dyadic) * half ^ 29)⟩,
       ⟨((-36411217 : Dyadic) * half ^ 29),
        ((203579097 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((18438909 : Dyadic) * half ^ 29),
        ((483195 : Dyadic) * half ^ 25)⟩,
       ⟨((102634679 : Dyadic) * half ^ 29),
        ((424391 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-7273451 : Dyadic) * half ^ 25),
        ((-30268397 : Dyadic) * half ^ 28)⟩,
       ⟨((6307061 : Dyadic) * half ^ 25),
        ((42097885 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((832079 : Dyadic) * half ^ 21),
        ((-223897881 : Dyadic) * half ^ 29)⟩,
       ⟨((-97072985 : Dyadic) * half ^ 28),
        ((-23435833 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word36Step37 :
    word36Chunk37.foldl (fun acc a => a.applyPacked acc)
      word36State37 = word36State38 := by decide +kernel

private def word36Chunk38 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State39 : PackedMat2 :=
    ⟨⟨⟨((-694594175 : Dyadic) * half ^ 30),
        ((-37598901 : Dyadic) * half ^ 30)⟩,
       ⟨((229564853 : Dyadic) * half ^ 30),
        ((-133928465 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((555970683 : Dyadic) * half ^ 30),
        ((-34540059 : Dyadic) * half ^ 28)⟩,
       ⟨((-358781719 : Dyadic) * half ^ 30),
        ((-113498441 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-358781719 : Dyadic) * half ^ 30),
        ((-113498441 : Dyadic) * half ^ 29)⟩,
       ⟨((555970683 : Dyadic) * half ^ 30),
        ((-34540059 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-229564853 : Dyadic) * half ^ 30),
        ((133928465 : Dyadic) * half ^ 30)⟩,
       ⟨((694594175 : Dyadic) * half ^ 30),
        ((37598901 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word36Step38 :
    word36Chunk38.foldl (fun acc a => a.applyPacked acc)
      word36State38 = word36State39 := by decide +kernel

private def word36Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word36State40 : PackedMat2 :=
    ⟨⟨⟨((-669919773 : Dyadic) * half ^ 31),
        ((-115517807 : Dyadic) * half ^ 29)⟩,
       ⟨((-873614459 : Dyadic) * half ^ 31),
        ((649342153 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((253988613 : Dyadic) * half ^ 31),
        ((507741113 : Dyadic) * half ^ 30)⟩,
       ⟨((5647355 : Dyadic) * half ^ 31),
        ((-34862441 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-980619785 : Dyadic) * half ^ 31),
        ((-1014203 : Dyadic) * half ^ 24)⟩,
       ⟨((-1050344667 : Dyadic) * half ^ 31),
        ((-124170629 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((187270925 : Dyadic) * half ^ 31),
        ((-192941779 : Dyadic) * half ^ 29)⟩,
       ⟨((-1111413381 : Dyadic) * half ^ 31),
        ((101847343 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word36Step39 :
    word36Chunk39.foldl (fun acc a => a.applyPacked acc)
      word36State39 = word36State40 := by decide +kernel

private def word36Chunk40 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word36State41 : PackedMat2 :=
    ⟨⟨⟨((-152258305 : Dyadic) * half ^ 31),
        ((-291843019 : Dyadic) * half ^ 29)⟩,
       ⟨((39650743 : Dyadic) * half ^ 28),
        ((-42829629 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((338849331 : Dyadic) * half ^ 30),
        ((-86610087 : Dyadic) * half ^ 31)⟩,
       ⟨((528939095 : Dyadic) * half ^ 31),
        ((92946857 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((338849331 : Dyadic) * half ^ 30),
        ((-86610087 : Dyadic) * half ^ 31)⟩,
       ⟨((-528939095 : Dyadic) * half ^ 31),
        ((-92946857 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((152258305 : Dyadic) * half ^ 31),
        ((291843019 : Dyadic) * half ^ 29)⟩,
       ⟨((39650743 : Dyadic) * half ^ 28),
        ((-42829629 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word36Step40 :
    word36Chunk40.foldl (fun acc a => a.applyPacked acc)
      word36State40 = word36State41 := by decide +kernel

private def word36Chunk41 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word36State42 : PackedMat2 :=
    ⟨⟨⟨((30653011 : Dyadic) * half ^ 32),
        ((3062607857 : Dyadic) * half ^ 33)⟩,
       ⟨((-712762371 : Dyadic) * half ^ 30),
        ((-1171035813 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1326883253 : Dyadic) * half ^ 32),
        ((2284936465 : Dyadic) * half ^ 33)⟩,
       ⟨((282624569 : Dyadic) * half ^ 31),
        ((-708917973 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1496927219 : Dyadic) * half ^ 32),
        ((1892132391 : Dyadic) * half ^ 33)⟩,
       ⟨((394004623 : Dyadic) * half ^ 31),
        ((-761634115 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2116821835 : Dyadic) * half ^ 32),
        ((2881702495 : Dyadic) * half ^ 33)⟩,
       ⟨((-472893011 : Dyadic) * half ^ 31),
        ((2820396473 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word36Step41 :
    word36Chunk41.foldl (fun acc a => a.applyPacked acc)
      word36State41 = word36State42 := by decide +kernel

private def word36Chunk42 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word36State43 : PackedMat2 :=
    ⟨⟨⟨((-2268391395 : Dyadic) * half ^ 33),
        ((3676778209 : Dyadic) * half ^ 33)⟩,
       ⟨((-904271615 : Dyadic) * half ^ 33),
        ((82366413 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-4020155961 : Dyadic) * half ^ 33),
        ((-472430853 : Dyadic) * half ^ 33)⟩,
       ⟨((4209651203 : Dyadic) * half ^ 33),
        ((835814997 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((4020155961 : Dyadic) * half ^ 33),
        ((472430853 : Dyadic) * half ^ 33)⟩,
       ⟨((4209651203 : Dyadic) * half ^ 33),
        ((835814997 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2268391395 : Dyadic) * half ^ 33),
        ((3676778209 : Dyadic) * half ^ 33)⟩,
       ⟨((904271615 : Dyadic) * half ^ 33),
        ((-82366413 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word36Step42 :
    word36Chunk42.foldl (fun acc a => a.applyPacked acc)
      word36State42 = word36State43 := by decide +kernel

private def word36Chunk43 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State44 : PackedMat2 :=
    ⟨⟨⟨((8515537 : Dyadic) * half ^ 34),
        ((387996245 : Dyadic) * half ^ 34)⟩,
       ⟨((13155823737 : Dyadic) * half ^ 34),
        ((131913703 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-4772673969 : Dyadic) * half ^ 34),
        ((3887271127 : Dyadic) * half ^ 34)⟩,
       ⟨((7541462663 : Dyadic) * half ^ 34),
        ((-611125553 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2665020021 : Dyadic) * half ^ 34),
        ((1384394347 : Dyadic) * half ^ 34)⟩,
       ⟨((5109522233 : Dyadic) * half ^ 34),
        ((-1539267079 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2498615493 : Dyadic) * half ^ 34),
        ((-6582169637 : Dyadic) * half ^ 34)⟩,
       ⟨((1722623003 : Dyadic) * half ^ 34),
        ((1643413525 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word36Step43 :
    word36Chunk43.foldl (fun acc a => a.applyPacked acc)
      word36State43 = word36State44 := by decide +kernel

private def word36Chunk44 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word36State45 : PackedMat2 :=
    ⟨⟨⟨((-1664214091 : Dyadic) * half ^ 32),
        ((3475152287 : Dyadic) * half ^ 35)⟩,
       ⟨((2444360011 : Dyadic) * half ^ 33),
        ((15229337909 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3575250559 : Dyadic) * half ^ 34),
        ((13076086217 : Dyadic) * half ^ 35)⟩,
       ⟨((-2031678271 : Dyadic) * half ^ 34),
        ((2248434237 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3575250559 : Dyadic) * half ^ 34),
        ((-13076086217 : Dyadic) * half ^ 35)⟩,
       ⟨((-2031678271 : Dyadic) * half ^ 34),
        ((2248434237 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1664214091 : Dyadic) * half ^ 32),
        ((3475152287 : Dyadic) * half ^ 35)⟩,
       ⟨((-2444360011 : Dyadic) * half ^ 33),
        ((-15229337909 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word36Step44 :
    word36Chunk44.foldl (fun acc a => a.applyPacked acc)
      word36State44 = word36State45 := by decide +kernel

private def word36Chunk45 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word36State46 : PackedMat2 :=
    ⟨⟨⟨((-4537913981 : Dyadic) * half ^ 34),
        ((-22936121807 : Dyadic) * half ^ 36)⟩,
       ⟨((3158655555 : Dyadic) * half ^ 35),
        ((14796164619 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((12230004793 : Dyadic) * half ^ 34),
        ((-11167071697 : Dyadic) * half ^ 36)⟩,
       ⟨((-7203909133 : Dyadic) * half ^ 35),
        ((-2532846711 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-4317112493 : Dyadic) * half ^ 35),
        ((31663918719 : Dyadic) * half ^ 36)⟩,
       ⟨((1712489801 : Dyadic) * half ^ 33),
        ((-17256100453 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((18866143213 : Dyadic) * half ^ 35),
        ((12234483517 : Dyadic) * half ^ 36)⟩,
       ⟨((-2034989297 : Dyadic) * half ^ 34),
        ((-5917172407 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word36Step45 :
    word36Chunk45.foldl (fun acc a => a.applyPacked acc)
      word36State45 = word36State46 := by decide +kernel

private def word36Chunk46 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word36State47 : PackedMat2 :=
    ⟨⟨⟨((-23154421315 : Dyadic) * half ^ 36),
        ((-6598339595 : Dyadic) * half ^ 35)⟩,
       ⟨((8631858313 : Dyadic) * half ^ 36),
        ((4469805631 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((28883938109 : Dyadic) * half ^ 36),
        ((7269523937 : Dyadic) * half ^ 36)⟩,
       ⟨((40439356159 : Dyadic) * half ^ 36),
        ((-16564676805 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2323788217 : Dyadic) * half ^ 34),
        ((17330823567 : Dyadic) * half ^ 35)⟩,
       ⟨((11917100371 : Dyadic) * half ^ 35),
        ((-5777709025 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-2341271667 : Dyadic) * half ^ 35),
        ((7261281501 : Dyadic) * half ^ 36)⟩,
       ⟨((15537950857 : Dyadic) * half ^ 35),
        ((7946569907 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word36Step46 :
    word36Chunk46.foldl (fun acc a => a.applyPacked acc)
      word36State46 = word36State47 := by decide +kernel

private def word36Chunk47 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word36State48 : PackedMat2 :=
    ⟨⟨⟨((12330599397 : Dyadic) * half ^ 37),
        ((-13306159211 : Dyadic) * half ^ 37)⟩,
       ⟨((-67543092453 : Dyadic) * half ^ 37),
        ((-10886253205 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-22334672211 : Dyadic) * half ^ 37),
        ((16714123033 : Dyadic) * half ^ 37)⟩,
       ⟨((-12218712605 : Dyadic) * half ^ 37),
        ((1193360475 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((22334672211 : Dyadic) * half ^ 37),
        ((-16714123033 : Dyadic) * half ^ 37)⟩,
       ⟨((-12218712605 : Dyadic) * half ^ 37),
        ((1193360475 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((12330599397 : Dyadic) * half ^ 37),
        ((-13306159211 : Dyadic) * half ^ 37)⟩,
       ⟨((67543092453 : Dyadic) * half ^ 37),
        ((10886253205 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word36Step47 :
    word36Chunk47.foldl (fun acc a => a.applyPacked acc)
      word36State47 = word36State48 := by decide +kernel

private def word36Chunk48 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word36State49 : PackedMat2 :=
    ⟨⟨⟨((-110579076781 : Dyadic) * half ^ 38),
        ((74506715613 : Dyadic) * half ^ 38)⟩,
       ⟨((65516320223 : Dyadic) * half ^ 38),
        ((11856336579 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-102099741715 : Dyadic) * half ^ 38),
        ((35446179789 : Dyadic) * half ^ 38)⟩,
       ⟨((79617202973 : Dyadic) * half ^ 38),
        ((27477715635 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((145357042329 : Dyadic) * half ^ 38),
        ((-11241269371 : Dyadic) * half ^ 38)⟩,
       ⟨((-74464682751 : Dyadic) * half ^ 38),
        ((-11357309043 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-121932061929 : Dyadic) * half ^ 38),
        ((22531378279 : Dyadic) * half ^ 38)⟩,
       ⟨((-27081369297 : Dyadic) * half ^ 38),
        ((44023849251 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word36Step48 :
    word36Chunk48.foldl (fun acc a => a.applyPacked acc)
      word36State48 = word36State49 := by decide +kernel

private def word36Chunk49 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word36State50 : PackedMat2 :=
    ⟨⟨⟨((-49880094351 : Dyadic) * half ^ 37),
        ((15791260389 : Dyadic) * half ^ 39)⟩,
       ⟨((72517403 : Dyadic) * half ^ 34),
        ((300838232775 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((42786079785 : Dyadic) * half ^ 38),
        ((-108237330401 : Dyadic) * half ^ 39)⟩,
       ⟨((39531756653 : Dyadic) * half ^ 38),
        ((148167816171 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((64101286643 : Dyadic) * half ^ 37),
        ((-813580783 : Dyadic) * half ^ 37)⟩,
       ⟨((19965242885 : Dyadic) * half ^ 38),
        ((41158918219 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-142523486193 : Dyadic) * half ^ 38),
        ((-50460233575 : Dyadic) * half ^ 38)⟩,
       ⟨((-79157373291 : Dyadic) * half ^ 37),
        ((49299955127 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word36Step49 :
    word36Chunk49.foldl (fun acc a => a.applyPacked acc)
      word36State49 = word36State50 := by decide +kernel

private def word36Chunk50 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word36State51 : PackedMat2 :=
    ⟨⟨⟨((-58556751247 : Dyadic) * half ^ 39),
        ((22787205583 : Dyadic) * half ^ 38)⟩,
       ⟨((75388926587 : Dyadic) * half ^ 38),
        ((73203865967 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-6776650031 : Dyadic) * half ^ 34),
        ((-30966211519 : Dyadic) * half ^ 39)⟩,
       ⟨((-414939923311 : Dyadic) * half ^ 39),
        ((31476199671 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-6776650031 : Dyadic) * half ^ 34),
        ((-30966211519 : Dyadic) * half ^ 39)⟩,
       ⟨((414939923311 : Dyadic) * half ^ 39),
        ((-31476199671 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((58556751247 : Dyadic) * half ^ 39),
        ((-22787205583 : Dyadic) * half ^ 38)⟩,
       ⟨((75388926587 : Dyadic) * half ^ 38),
        ((73203865967 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word36Step50 :
    word36Chunk50.foldl (fun acc a => a.applyPacked acc)
      word36State50 = word36State51 := by decide +kernel

private def word36Chunk51 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word36State52 : PackedMat2 :=
    ⟨⟨⟨((-571560206797 : Dyadic) * half ^ 40),
        ((-36627301615 : Dyadic) * half ^ 40)⟩,
       ⟨((-134922080763 : Dyadic) * half ^ 40),
        ((-305122143947 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-500450162757 : Dyadic) * half ^ 40),
        ((4231889561 : Dyadic) * half ^ 37)⟩,
       ⟨((-642283926025 : Dyadic) * half ^ 40),
        ((17577749593 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((26041528715 : Dyadic) * half ^ 38),
        ((-571367044391 : Dyadic) * half ^ 40)⟩,
       ⟨((-9113970471 : Dyadic) * half ^ 38),
        ((35458440817 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((170874722781 : Dyadic) * half ^ 39),
        ((88310285945 : Dyadic) * half ^ 38)⟩,
       ⟨((-67123710583 : Dyadic) * half ^ 38),
        ((218319063017 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word36Step51 :
    word36Chunk51.foldl (fun acc a => a.applyPacked acc)
      word36State51 = word36State52 := by decide +kernel

private def word36Chunk52 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word36State53 : PackedMat2 :=
    ⟨⟨⟨((-42498637327 : Dyadic) * half ^ 41),
        ((304928981541 : Dyadic) * half ^ 41)⟩,
       ⟨((-1145348612807 : Dyadic) * half ^ 41),
        ((-60616566003 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((368244713439 : Dyadic) * half ^ 41),
        ((-924002304909 : Dyadic) * half ^ 41)⟩,
       ⟨((-91333323681 : Dyadic) * half ^ 41),
        ((-413373936277 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-368244713439 : Dyadic) * half ^ 41),
        ((924002304909 : Dyadic) * half ^ 41)⟩,
       ⟨((-91333323681 : Dyadic) * half ^ 41),
        ((-413373936277 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-42498637327 : Dyadic) * half ^ 41),
        ((304928981541 : Dyadic) * half ^ 41)⟩,
       ⟨((1145348612807 : Dyadic) * half ^ 41),
        ((60616566003 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word36Step52 :
    word36Chunk52.foldl (fun acc a => a.applyPacked acc)
      word36State52 = word36State53 := by decide +kernel

private def word36Chunk53 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word36State54 : PackedMat2 :=
    ⟨⟨⟨((1348351468419 : Dyadic) * half ^ 42),
        ((1245594788739 : Dyadic) * half ^ 42)⟩,
       ⟨((-371885256545 : Dyadic) * half ^ 42),
        ((-645990834681 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((1733740328281 : Dyadic) * half ^ 42),
        ((-1225939542873 : Dyadic) * half ^ 42)⟩,
       ⟨((21972672897 : Dyadic) * half ^ 42),
        ((-785240640997 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-2796420824867 : Dyadic) * half ^ 42),
        ((877856500589 : Dyadic) * half ^ 42)⟩,
       ⟨((344541739121 : Dyadic) * half ^ 42),
        ((213970956923 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((46386880623 : Dyadic) * half ^ 42),
        ((-488233105937 : Dyadic) * half ^ 42)⟩,
       ⟨((-2537576458101 : Dyadic) * half ^ 42),
        ((-430059181241 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word36Step53 :
    word36Chunk53.foldl (fun acc a => a.applyPacked acc)
      word36State53 = word36State54 := by decide +kernel

private def word36Chunk54 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word36State55 : PackedMat2 :=
    ⟨⟨⟨((1420551080563 : Dyadic) * half ^ 42),
        ((4210814419775 : Dyadic) * half ^ 43)⟩,
       ⟨((-1484676099293 : Dyadic) * half ^ 42),
        ((2099649075067 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((-711434253797 : Dyadic) * half ^ 41),
        ((2012239940913 : Dyadic) * half ^ 43)⟩,
       ⟨((-7358845911 : Dyadic) * half ^ 40),
        ((41627918763 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((711434253797 : Dyadic) * half ^ 41),
        ((-2012239940913 : Dyadic) * half ^ 43)⟩,
       ⟨((-7358845911 : Dyadic) * half ^ 40),
        ((41627918763 : Dyadic) * half ^ 43)⟩⟩,
     ⟨⟨((1420551080563 : Dyadic) * half ^ 42),
        ((4210814419775 : Dyadic) * half ^ 43)⟩,
       ⟨((1484676099293 : Dyadic) * half ^ 42),
        ((-2099649075067 : Dyadic) * half ^ 43)⟩⟩⟩
private lemma word36Step54 :
    word36Chunk54.foldl (fun acc a => a.applyPacked acc)
      word36State54 = word36State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word36_check : check word36 36 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word36 = word36State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word36Chunk0 ++ word36Chunk1 ++ word36Chunk2 ++ word36Chunk3 ++
      word36Chunk4 ++ word36Chunk5 ++ word36Chunk6 ++ word36Chunk7 ++
      word36Chunk8 ++ word36Chunk9 ++ word36Chunk10 ++ word36Chunk11 ++
      word36Chunk12 ++ word36Chunk13 ++ word36Chunk14 ++ word36Chunk15 ++
      word36Chunk16 ++ word36Chunk17 ++ word36Chunk18 ++ word36Chunk19 ++
      word36Chunk20 ++ word36Chunk21 ++ word36Chunk22 ++ word36Chunk23 ++
      word36Chunk24 ++ word36Chunk25 ++ word36Chunk26 ++ word36Chunk27 ++
      word36Chunk28 ++ word36Chunk29 ++ word36Chunk30 ++ word36Chunk31 ++
      word36Chunk32 ++ word36Chunk33 ++ word36Chunk34 ++ word36Chunk35 ++
      word36Chunk36 ++ word36Chunk37 ++ word36Chunk38 ++ word36Chunk39 ++
      word36Chunk40 ++ word36Chunk41 ++ word36Chunk42 ++ word36Chunk43 ++
      word36Chunk44 ++ word36Chunk45 ++ word36Chunk46 ++ word36Chunk47 ++
      word36Chunk48 ++ word36Chunk49 ++ word36Chunk50 ++ word36Chunk51 ++
      word36Chunk52 ++ word36Chunk53 ++ word36Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word36Step0, word36Step1, word36Step2, word36Step3, word36Step4,
      word36Step5, word36Step6, word36Step7, word36Step8, word36Step9,
      word36Step10, word36Step11, word36Step12, word36Step13, word36Step14,
      word36Step15, word36Step16, word36Step17, word36Step18, word36Step19,
      word36Step20, word36Step21, word36Step22, word36Step23, word36Step24,
      word36Step25, word36Step26, word36Step27, word36Step28, word36Step29,
      word36Step30, word36Step31, word36Step32, word36Step33, word36Step34,
      word36Step35, word36Step36, word36Step37, word36Step38, word36Step39,
      word36Step40, word36Step41, word36Step42, word36Step43, word36Step44,
      word36Step45, word36Step46, word36Step47, word36Step48, word36Step49,
      word36Step50, word36Step51, word36Step52, word36Step53, word36Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end

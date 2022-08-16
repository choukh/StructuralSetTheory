(*** Coq coding by choukh, Aug 2022 ***)

Require Export Ordinal.

Definition LEM := ∀ P, P ∨ ¬ P.
Definition DGP := ∀ P Q : Prop, (P → Q) ∨ (Q → P).
Definition WLEM := ∀ P, ¬ P ∨ ¬ ¬ P.

Lemma LEM_DGP : LEM → DGP.
Proof. intros lem P Q. destruct (lem P), (lem Q); firstorder. Qed.

Lemma DGP_WLEM : DGP → WLEM.
Proof. intros dgp P. destruct (dgp P (¬ P)); firstorder. Qed.

Section WellOrder.

Variable U : Type.
Implicit Types a b c : 𝒫 U.
Implicit Types A B C : 𝒫 𝒫 U.
Implicit Types α β : 𝒫 𝒫 𝒫 U.

Definition 良序 := @良序 U.

Lemma 嵌入线序_DGP : (∀ A B ∈ 良序, A ≼ B ∨ B ≼ A) → DGP.
Proof.
  intros lin P Q. set (e := λ _ : U, False).
  pose (X := λ x, (Q → P) ∧ x = e).
  pose (Y := λ x, (P → Q) ∧ x = e).
  assert (woX: 良序 X). intros A AX [x xA]. exists e. firstorder congruence.
  assert (woY: 良序 Y). intros A AY [x xA]. exists e. firstorder congruence.
  destruct (lin X woX Y woY) as [[f Hf]|[f Hf]].
  - left. intros p. destruct (f ltac:(now exists e)) as [y [q _]]. auto.
  - right. intros q. destruct (f ltac:(now exists e)) as [y [p _]]. auto.
Qed.

Lemma 嵌入可判定_LEM : (∀ A B ∈ 良序, A ≼ B ∨ A ⋠ B) → LEM.
Proof.
  intros dec P. set (e := λ _ : U, False).
  pose (X := λ x, x = e).
  pose (Y := λ x, P ∧ x = e).
  assert (woX: 良序 X). intros A AX [x xA]. exists e. firstorder congruence.
  assert (woY: 良序 Y). intros A AY [x xA]. exists e. firstorder congruence.
  destruct (dec X woX Y woY) as [[f _]|XY].
  - left. destruct (f ltac:(now exists e)) as [y [p _]]. apply p.
  - right. intros p. apply XY. enough (X = Y) as -> by reflexivity.
    apply 外延; firstorder.
Qed.

Fact LEM_iff_嵌入可判定 : LEM ↔ ∀ A B ∈ 良序, A ≼ B ∨ A ⋠ B.
Proof. split.
  - intros lem A _ B _. apply lem.
  - apply 嵌入可判定_LEM.
Qed.

End WellOrder.

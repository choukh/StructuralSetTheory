(*** Coq coding by choukh, Aug 2022 ***)

Require Export Prelim Ordinal.

(* 哈特格斯数 *)
Section Hartgos.

(* 全集 *)
Variable U : Type.

Definition ℍ := Σ (@Ω U).

Definition ℍ序 (α β : ℍ) := (序 (π₁ α) (π₁ β)).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

Lemma ℍ序_自反 (α : ℍ) : α ≤ α.
Proof. apply 序_自反, π₂. Qed.

Lemma ℍ序_传递 (α β γ : ℍ) : α ≤ β → β ≤ γ → α ≤ γ.
Proof. apply 序_传递, π₂. Qed.

Lemma ℍ序_反自反 (α β : ℍ) : α ≤ β → β ≤ α → α = β.
Proof.
  intros H1 H2. apply π_单射.
  apply 序_反自反; trivial; apply π₂.
Qed.

Fact ℍ_势上界 : |ℍ| ≤ |𝒫ₙ 3 U|.
Proof. apply 单射_从子集. Qed.

End Hartgos.

Notation "A ₊" := (ℍ A) (at level 20).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

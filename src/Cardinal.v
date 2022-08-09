(*** Coq coding by choukh, Aug 2022 ***)

Require Export Prelim Ordinal.

(* 哈特格斯数 *)
Section Hartgos.

(* 全集 *)
Variable U : Type.

Definition ℍ := Σ (@Ω U).

Definition ℍ序 (αₛ βₛ : ℍ) := (序 (π₁ αₛ) (π₁ βₛ)).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

Lemma ℍ序_自反 (αₛ : ℍ) : αₛ ≤ αₛ.
Proof. apply 序_自反, π₂. Qed.

Lemma ℍ序_传递 (αₛ βₛ γₛ : ℍ) : αₛ ≤ βₛ → βₛ ≤ γₛ → αₛ ≤ γₛ.
Proof. apply 序_传递, π₂. Qed.

Lemma ℍ序_反自反 (αₛ βₛ : ℍ) : αₛ ≤ βₛ → βₛ ≤ αₛ → αₛ = βₛ.
Proof. intros H1 H2. apply π_单射. apply 序_反自反; trivial; apply π₂. Qed.

Fact ℍ_势上界 : |ℍ| ≤ |𝒫ₙ 3 U|.
Proof. apply 单射_从子集. Qed.

End Hartgos.

Notation "A ₊" := (ℍ A) (at level 20).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

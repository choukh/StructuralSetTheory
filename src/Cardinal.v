(*** Coq coding by choukh, Aug 2022 ***)

Require Export Prelim Ordinal.

(* 哈特格斯数 *)
Section Hartgos.

Definition ℍ U := Σ (@Ω U).
Notation "U ₊" := (ℍ U) (format "U ₊", at level 20).

Variable U : Type.

Definition ℍ序 (αₛ βₛ : U₊) := (序 (π₁ αₛ) (π₁ βₛ)).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

Lemma ℍ序_自反 (αₛ : U₊) : αₛ ≤ αₛ.
Proof. apply 序_自反, π₂. Qed.

Lemma ℍ序_传递 (αₛ βₛ γₛ : U₊) : αₛ ≤ βₛ → βₛ ≤ γₛ → αₛ ≤ γₛ.
Proof. apply 序_传递, π₂. Qed.

Lemma ℍ序_反自反 (αₛ βₛ : U₊) : αₛ ≤ βₛ → βₛ ≤ αₛ → αₛ = βₛ.
Proof. intros H1 H2. apply π_单射. apply 序_反自反; trivial; apply π₂. Qed.

Fact ℍ_势上界 : |U₊| ≤ |𝒫ₙ 3 U|.
Proof. apply 单射_从子集. Qed.

End Hartgos.

Notation "U ₊" := (ℍ U) (at level 20).
Notation "α ≤ β" := (ℍ序 α β) (at level 70).

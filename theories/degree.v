Require Export imports.

Definition DBasis := nat -> nat.

Fixpoint degree (Ξ : DBasis) a :=
  match a with
  | VarTm i => Ξ i
  | ISort Star => 2
  | ISort Kind => 3
  | Abs A a => degree (degree Ξ A - 1 .: Ξ) a
  | Pi A B => degree (degree Ξ A - 1 .: Ξ) B
  | App a b => degree Ξ a
  end.

Fixpoint b2d Γ :=
  match Γ with
  | nil => ids
  | A :: Γ =>
      degree (b2d Γ) A - 1 .: b2d Γ
  end.

Definition ξ_ok ξ (Ξ0 Ξ1 : DBasis) := forall i, Ξ0 i = Ξ1 (ξ i).

Lemma ξ_ok_up ξ Ξ0 Ξ1 i : ξ_ok ξ Ξ0 Ξ1 ->
                            ξ_ok (upRen_Term_Term ξ) (i .: Ξ0) (i .: Ξ1).
Proof.
  move => h.
  case => //=.
Qed.

Lemma renaming Ξ a : forall ξ Ξ', ξ_ok ξ Ξ Ξ' -> degree Ξ a = degree Ξ' a⟨ξ⟩.
Proof.
  elim : a Ξ=>//=; hauto lq:on use:ξ_ok_up.
Qed.

Definition ρ_ok ρ (Ξ0 Ξ1 : DBasis) :=
  forall i, degree Ξ1 (ρ i) = Ξ0 i.

Lemma ρ_ext ρ (Ξ0 Ξ1 : DBasis) a i :
  ρ_ok ρ Ξ0 Ξ1 ->
  degree Ξ1 a = i ->
  ρ_ok (a .: ρ) (i .: Ξ0) Ξ1.
Proof.
  move => hρ.
  rewrite /ρ_ok => h.
  case => //=.
Qed.

Lemma ρ_ξ_comp ρ ξ Ξ0 Ξ1 Ξ2 :
  ρ_ok ρ Ξ0 Ξ1 ->
  ξ_ok ξ Ξ1 Ξ2 ->
  ρ_ok (ρ >> ren_Term ξ) Ξ0 Ξ2.
Proof.
  rewrite /ρ_ok /ξ_ok => hρ hξ i.
  have -> : (ρ >> ren_Term  ξ ) i = (ρ i)⟨ ξ ⟩ by asimpl.
  rewrite -(renaming Ξ1) => //=.
Qed.

Lemma ρ_up ρ Ξ0 Ξ1 i :
  ρ_ok ρ Ξ0 Ξ1 ->
  ρ_ok (up_Term_Term ρ) (i .: Ξ0) (i .: Ξ1).
Proof.
  move => hρ.
  rewrite /up_Term_Term.
  apply ρ_ext => //=.
  apply : ρ_ξ_comp; eauto.
  rewrite /ξ_ok. case => //=.
Qed.

Lemma morphing Ξ a : forall ρ Ξ', ρ_ok ρ Ξ Ξ' -> degree Ξ a = degree Ξ' a[ρ].
Proof.
  elim : a Ξ => //=; hauto lq:on use:ρ_up.
Qed.

Lemma ρ_id Ξ :
  ρ_ok ids Ξ Ξ.
Proof. by rewrite /ρ_ok. Qed.

Lemma subst_one Ξ a b i :
  degree Ξ b = i ->
  degree (i .: Ξ) a = degree Ξ a[b…].
Proof. eauto using morphing, ρ_ext, ρ_id. Qed.

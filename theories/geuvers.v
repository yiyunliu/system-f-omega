Require Export typing.

Inductive kind_interp Γ : Term -> Type -> Prop :=
| KI_Star :
  kind_interp Γ (ISort Star) (Term -> Prop)
| KI_Imp A B S0 S1 :
  kind_interp Γ A S0 ->
  kind_interp (A::Γ) B S1 ->
  kind_interp Γ (Pi A B) (S0 -> S1 -> Prop)
| KI_Fun A B S :
  Γ ⊢ A ∈ ISort Star ->
  kind_interp (A::Γ) B S ->
  kind_interp Γ (Pi A B) S.

(* Lemma that gives the shape of a kind (excludes app) *)

(* Lemma subject_reduction Γ a A  : *)
(*   Γ ⊢ a ∈ A -> forall b, a ⇒ b -> Γ ⊢ b ∈ A. *)
(* Proof. Admitted. *)

(* Lemma kind_interp_eval Γ A B S : *)
(*   kind_interp Γ A S -> A ⇒ B -> kind_interp Γ B S. *)
(* Proof. *)
(*   move => h. move : B. elim : Γ A S /h. *)
(*   - hauto l:on inv:Par. *)
(*   - move => Γ A B S0 S1 hA ihA hB ihB. *)
(*     admit. *)
(* Admitted. *)

Lemma kind_imp Γ A :
  ~ Γ ⊢ ISort Kind ∈ A.
Proof.
  move E : (ISort Kind) => a h.
  move : E.
  elim : Γ a A /h=>//=.
Qed.

Lemma wt_has_interp Γ A :
  Γ ⊢ A ∈ ISort Kind -> exists V, kind_interp Γ A V.
Proof.
  move E : (ISort Kind) => U h.
  move : E.
  elim : Γ A U /h=>//=.
  - move => Γ i A h ?. subst.
    (* Impossible because Kind doesn't have a sort *)
    admit.
  - eauto using KI_Star.
  - move => Γ a b A B ha _ hb _ E.
    have : Γ ⊢ App b a ∈ B[a…] by  eauto using T_App.
    (* Contradiction *)
    admit.
  - move => Γ A s1 B s2 hA ihA hB ihB [?]. subst.
    specialize ihB with (1 := eq_refl).
    case : s1 hA ihA; hauto lq:on ctrs:kind_interp.
  - (* Impossible *)
    move => Γ a A B s ha iha hB ihB heq ?. subst.
    firstorder using kind_imp.
Admitted.

Lemma kind_interp_not_star Γ A S :
  kind_interp Γ A S ->
  ~ Γ ⊢ A ∈ ISort Star.
Proof.
  move => h. elim : Γ A S /h.
  - admit.
  - move => Γ A B S0 S1 hA ihA hB ihB.
    admit.
  - move => Γ A B S hA ihA hB h.
Admitted.

Lemma kind_interp_functionality Γ A S0 S1 :
  kind_interp Γ A S0 -> kind_interp Γ A S1 -> S0 = S1.
Proof.
  move => h. move : S1. elim : Γ A S0 / h.
  - hauto lq:on inv:kind_interp.
  - move => Γ A B SA0 SB0 hA ihA hB ihB S.
    inversion 1; subst.
    sfirstorder.
    firstorder using kind_interp_not_star.
  - move => Γ A B S hA ihA hB S0.
    inversion 1.
    by firstorder using kind_interp_not_star.
    sfirstorder.
Qed.

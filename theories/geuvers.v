Require Export typing.

(* Try simplifying kind_interp using Barendregt's and Barass' methods of degrees *)


(* Lemma b2d_lookup i Γ A : Lookup i Γ A -> ⊢ Γ -> degree (b2d Γ) A = b2d Γ i + 1. *)
(* Proof. *)
(*   move => h. elim : i Γ A / h. *)
(*   - move => A Γ hΓ. simpl. *)
(*     erewrite <-renaming; eauto. *)
(*     rewrite /ξ_ok. case => //=. *)
(*   - move => n Γ A B hn h. *)
(*     simpl. *)
(*     erewrite <-renaming; eauto. *)
(*     rewrite /ξ_ok. case => //=. *)
(* Qed. *)

Lemma wt_degree :
  (forall Γ a A,  Γ ⊢ a ∈ A -> degree (b2d Γ) a + 1 = degree (b2d Γ) A) /\
  (forall Γ, ⊢ Γ -> forall i A, Lookup i Γ A -> b2d Γ i + 1 = degree (b2d Γ) A).
Proof.
  apply Wt_multind; eauto.
  - hauto lq:on use:subst_one solve+:lia.
  - move => Γ a A B s ha iha hB ihB h.
    rewrite iha.
    admit.
  - inversion 1.
  - move => Γ A s hΓ ihΓ hA ihA i A0.
    elim /lookup_inv=>//=_.
    + move => A1 Γ0 ? [*]. subst.
      have -> : degree (b2d Γ) A - 1 + 1 = degree (b2d Γ) A
        by hauto q:on solve+:lia.
      apply renaming. case => //=.
    + move => n Γ0 A1 B ? ? [*]. subst.
      erewrite ihΓ; eauto.
      apply renaming.
      case => //=.


Inductive Skel : Set :=
| SK_Star : Skel
| SK_Arr : Skel -> Skel -> Skel.

Inductive kind_interp Γ : Term -> Skel -> Prop :=
| KI_Star :
  kind_interp Γ (ISort Star) SK_Star
| KI_Imp A B S0 S1 :
  kind_interp Γ A S0 ->
  kind_interp (A::Γ) B S1 ->
  kind_interp Γ (Pi A B) (SK_Arr S0 S1)
| KI_Fun A B S :
  Γ ⊢ A ∈ ISort Star ->
  kind_interp (A::Γ) B S ->
  kind_interp Γ (Pi A B) S.

Fixpoint interp_skel a : Type :=
  match a with
  | SK_Star => Term -> Prop
  | SK_Arr S0 S1 =>
      interp_skel S0 -> interp_skel S1 -> Prop
  end.

Definition ProdSpace (S0 S1 : Term -> Prop) b : Prop := forall a, S0 a -> S1 (App b a).

Definition InterSpace {A : Type} (S : A -> (Term -> Prop) -> Prop) (b : Term) : Prop := forall a S0, S a S0 -> S0 b.

(* TODO: Add conditions that say that the set is saturated *)
Definition ρ_ok_kind (ρ : nat -> option {A : Skel & interp_skel A}) Γ :=
  forall i A, Lookup i Γ A -> exists Sk S, kind_interp Γ A Sk /\ ρ i = Some (existT Sk S).

Inductive type_interp (Γ : Basis) (ρ : nat -> option {A : Skel & interp_skel A}) : Term -> forall (A : Skel), interp_skel A -> Prop :=
| TI_Star s :
  type_interp Γ ρ (ISort s) SK_Star SN

| TI_Var i Sk1 S :
  Some (existT Sk1 S) = ρ i ->
  type_interp Γ ρ (VarTm i) Sk1 S

| TI_App P Q Sk1 Sk2 S1 S2 F :
  type_interp Γ ρ P (SK_Arr Sk1 Sk2) F ->
  type_interp Γ ρ Q Sk1 S1 ->
  F S1 S2 ->
  (* -------------------- *)
  type_interp Γ ρ (App P Q) Sk2 S2

| TI_AppTm Sk P t A S  :
  type_interp Γ ρ P Sk S ->
  Γ ⊢ t ∈ A ->
  Γ ⊢ A ∈ ISort Star ->
  (* ------------------------------- *)
  type_interp Γ ρ (App P t) Sk S

| TI_Abs A B Sk1 Sk2 PF :
  kind_interp Γ A Sk1 ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk1 a) .: ρ) B  Sk2 S) ->
  (* ------------------------------ *)
  type_interp Γ ρ (Abs A B) (SK_Arr Sk1 Sk2) PF

| TI_AbsTm A B Sk S :
  Γ ⊢ A ∈ ISort Star ->
  type_interp (A::Γ) (None .: ρ) B Sk S ->
  (* ------------------------------------ *)
  type_interp Γ ρ (Abs A B) Sk S

| TI_Pi A B S1 S2:
  Γ ⊢ A ∈ ISort Star ->
  type_interp Γ ρ A SK_Star S1 ->
  type_interp (A::Γ) (None .: ρ) B SK_Star S2 ->
  (* ------------------------------------------------------------- *)
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S1 S2)

| TI_PiKind A Sk B S PF :
  kind_interp Γ A Sk ->
  type_interp Γ ρ A SK_Star S  ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk a) .: ρ) B SK_Star S) ->
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S (InterSpace PF)).

(* Lemma kind_interp_eval Γ A B S : *)
(*   kind_interp Γ A S -> A ⇒ B -> kind_interp Γ B S. *)
(* Proof. *)
(*   move => h. move : B. elim : Γ A S /h. *)
(*   - hauto l:on inv:Par. *)
(*   - move => Γ A B S0 S1 hA ihA hB ihB. *)
(*     admit. *)
(* Admitted. *)

Lemma kind_has_interp Γ A :
  Γ ⊢ A ∈ ISort Kind -> exists V, kind_interp Γ A V.
Proof.
  move E : (ISort Kind) => U h.
  move : E.
  elim : Γ A U /h=>//=.
  - hauto lq:on use: wf_lookup, kind_imp.
  - eauto using KI_Star.
  - move => Γ a b A B ha _ hb _ E.
    have : Γ ⊢ App b a ∈ B[a…] by  eauto using T_App.
    case /regularity : hb=>//.
    move => [s]/wt_inv /=.
    move => [s1][s2]hA.
    have ? : s2 = s by hauto l:on use:coherent_sort_inj. subst.
    have : Γ ⊢ B[a…] ∈ ISort s by firstorder using wt_subst_sort.
    rewrite -E.
    firstorder using kind_imp.
  - move => Γ A s1 B s2 hA ihA hB ihB [?]. subst.
    specialize ihB with (1 := eq_refl).
    case : s1 hA ihA; hauto lq:on ctrs:kind_interp.
  - (* Impossible *)
    move => Γ a A B s ha iha hB ihB heq ?. subst.
    firstorder using kind_imp.
Qed.

Lemma kind_interp_not_star Γ A S :
  kind_interp Γ A S ->
  ~ Γ ⊢ A ∈ ISort Star.
Proof.
  move => h. elim : Γ A S /h.
  - hauto l:on use:wt_inv, coherent_sort_inj.
  - hauto lq:on rew:off use:wt_inv, coherent_sort_inj.
  - hauto lq:on rew:off use:wt_inv, coherent_sort_inj.
Qed.

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

Lemma type_has_interp Γ A T Sk:
  Γ ⊢ A ∈ T -> kind_interp Γ T Sk ->
  forall ρ, ρ_ok_kind ρ Γ -> forall Sk0 S, type_interp Γ ρ A Sk0 S -> Sk = Sk0.
Proof.
  move => + + ρ + Sk0 S h.
  move : Sk T.
  elim : Γ ρ A Sk0 S /h.
  - move => Γ ρ s Sk T /wt_inv_sort.
    move => [? ?]. subst.
    inversion 1.
  - move => Γ ρ i sk S hi sk0 T hA hT hρ.
    rewrite /ρ_ok_kind in hρ.
    move /wt_inv : hA => /=.
    move => [A0][hA0 ?].
    move : hρ hA0 => /[apply].
    move => [sk1]/=[S0][h0 h1].
    rewrite h1 in hi.
    case : hi => ?.
    move => h. subst.
    admit.
  - move => Γ ρ P Q Sk1 Sk2 S1 S2.
    rewrite -/interp_skel in S2 *.
    best.

Require Export typing par degree syntactic.

Inductive Cls : Set :=
| C_Atom : nat -> Cls
| C_Branch : Cls -> Cls -> Cls.

Definition CBasis := nat -> Cls.

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

(* Lemma preservation_degree a b : a ⇒ b -> forall Γ A, *)
(*       Γ ⊢ a ∈ A -> degree (b2d Γ) a = degree (b2d Γ) b. *)
(* Proof. *)
(*   move => h . *)
(*   elim : a b /h. *)
(*   - done. *)
(*   - done. *)
(*   - hauto l:on drew:off use:subject_reduction, wt_inv. *)
(*   - hauto l:on drew:off use:subject_reduction, wt_inv. *)
(*   - hauto l:on drew:off use:subject_reduction, wt_inv. *)
(*   - move => A a0 a1 b0 b1 ha iha hb ihb Γ A0 /wt_inv. *)
(*     move => [A1][B][h0][h1]h2. *)
(*     simpl. *)
(*     set q := _ .: _. *)
(*     have -> : q = b2d (A :: Γ) by qauto. *)
(*     erewrite iha. *)
(*     apply degree.morphing. *)
(*     simpl. *)
(*     apply degree.ρ_ext. *)
(*     apply ρ_id. *)
(* Admitted. *)

(* Lemma wt_degree : *)
(*   (forall Γ a A,  Γ ⊢ a ∈ A -> degree (b2d Γ) a + 1 = degree (b2d Γ) A) /\ *)
(*   (forall Γ, ⊢ Γ -> forall i A, Lookup i Γ A -> b2d Γ i + 1 = degree (b2d Γ) A). *)
(* Proof. *)
(*   apply Wt_multind; eauto. *)
(*   - hauto lq:on use:subst_one solve+:lia. *)
(*   - move => Γ a A B s ha iha hB ihB h. *)
(*     rewrite iha. *)
(*     simpl in ihB. *)
(*     case : s ihB hB => //=. *)
(*     + move => hB. *)
(*       have {}hB : degree (b2d Γ) B = 2 by lia. *)
(*       simpl. *)
(*     + best. *)
(*   - inversion 1. *)
(*   - move => Γ A s hΓ ihΓ hA ihA i A0. *)
(*     elim /lookup_inv=>//=_. *)
(*     + move => A1 Γ0 ? [*]. subst. *)
(*       have -> : degree (b2d Γ) A - 1 + 1 = degree (b2d Γ) A *)
(*         by hauto q:on solve+:lia. *)
(*       apply renaming. case => //=. *)
(*     + move => n Γ0 A1 B ? ? [*]. subst. *)
(*       erewrite ihΓ; eauto. *)
(*       apply renaming. *)
(*       case => //=. *)
(* Admitted. *)

Inductive Skel : Set :=
| SK_Unit : Skel
| SK_Star : Skel
| SK_Arr : Skel -> Skel -> Skel.

Fixpoint kind_int A :=
  match A with
  | ISort Star => SK_Star
  | Pi A B => SK_Arr (kind_int A) (kind_int B)
  | _ => SK_Unit
  end.

Fixpoint infer_sig ρ A :=
  match A with
  | VarTm i => ρ i
  | Abs A a => SK_Arr (kind_int A) (infer_sig (kind_int A .: ρ) a)
  | App b a => match infer_sig ρ b with
              | SK_Arr _ sk => sk
              | _ => SK_Unit
              end
  | Pi A B => SK_Star
  | ISort _ => SK_Star
  end.

Fixpoint skel_int a : Type :=
  match a with
  | SK_Unit => unit
  | SK_Star => Term -> Prop
  | SK_Arr S0 S1 =>
      skel_int S0 -> skel_int S1
  end.

Fixpoint default_int (s : Skel) : skel_int s :=
  match s as s return (skel_int s) with
  | SK_Unit => tt
  | SK_Star => SN
  | SK_Arr s1 s2 => fun _ => default_int s2
  end.

Scheme Equality for Skel.

Definition ProdSpace (S0 S1 : Term -> Prop) b : Prop := forall a, S0 a -> S1 (App b a).
Definition InterSpace {A : Type} (S : A -> (Term -> Prop)) (b : Term) : Prop := forall a, S a b.

Definition ρξ_lookup (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (i : nat) (sk : Skel) : skel_int sk.
  pose (ξ i) as r.
  destruct (Skel_eq_dec (ρ i) sk).
  - rewrite <- e. apply r.
  - apply default_int.
Defined.

Definition ξ_ext (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (sk : Skel) (r : skel_int sk) :
  (forall i, skel_int ((sk .: ρ) i)).
  destruct i as [|i].
  apply r.
  apply ξ.
Defined.

Fixpoint int_type_with_sig (ρ : nat -> Skel) (ξ : forall i, skel_int (ρ i))
  (sk : Skel) (A : Term) : skel_int sk.
  refine (
      match A with
      | VarTm i => ρξ_lookup ρ ξ i sk
      | ISort _ => default_int sk
      | Abs A a => match sk as s return (skel_int s) with
                  | SK_Arr sk0 sk1 =>
                      fun (v : skel_int sk0) =>
                        int_type_with_sig (sk0 .: ρ) (ξ_ext ρ ξ sk0 v) sk1 a
                  | SK_Unit => tt
                  | SK_Star => default_int SK_Star
                  end
      | App b a => let sk0 := infer_sig ρ a in
                    int_type_with_sig ρ ξ (SK_Arr sk0 sk) b
                      (int_type_with_sig ρ ξ sk0 a)
      | Pi A B => match sk as s return (skel_int s) with
                 | SK_Star =>
                     ProdSpace (int_type_with_sig ρ ξ SK_Star A)
                       (InterSpace (fun (v : skel_int (kind_int A)) =>
                                      int_type_with_sig (kind_int A .: ρ)
                                        (ξ_ext ρ ξ _ v) SK_Star B))
                 | SK_Unit => tt
                 | SK_Arr sk0 sk1 => default_int (SK_Arr sk0 sk1)
                 end
      end
    ).


Lemma kind_has_int Γ A :
  Γ ⊢ A ∈ ISort Kind -> exists V, kind_int A = Some V.
Proof.
  move E : (ISort Kind) => U h.
  move : E.
  elim : Γ A U /h=>//=.
  - hauto lq:on use: wf_lookup, kind_imp.
  - eauto using SK_Star.
  - move => Γ a b A B ha _ hb _ E.
    have : Γ ⊢ App b a ∈ B[a…] by  eauto using T_App.
    case /regularity : hb=>//.
    move => [s]/wt_inv /=.
    move => [s1][s2]hA.
    have ? : s2 = s by hauto l:on use:coherent_sort_inj, coherent'_forget. subst.
    have : Γ ⊢ B[a…] ∈ ISort s by firstorder using wt_subst_sort.
    rewrite -E.
    firstorder using kind_imp.
  - move => Γ A s1 B s2 hA ihA hB ihB [?]. subst.
    specialize ihB with (1 := eq_refl).
    case : s1 hA ihA; hauto q:on.
  - (* Impossible *)
    move => Γ a A B s ha iha hB ihB heq ?. subst.
    firstorder using kind_imp.
Qed.

Lemma kind_no_int Γ A :
  Γ ⊢ A ∈ ISort Star -> kind_int A = None.
Proof.
  elim : A Γ => //=.
  - move => s Γ /wt_inv => //= h. exfalso.
    case : s h=>//=.
    hauto q:on use:coherent'_forget, coherent_sort_inj.
  - move => A ihA B ihB Γ /wt_inv /=.
    move => [s1][s2][hA][hB]E.
    have ? : s2 = Star by eauto using coherent'_forget, coherent_sort_inj. subst.
    hauto lq:on.
Qed.

Lemma app_kind_imp Γ b a :
  ~ Γ ⊢ App b a ∈ ISort Kind.
Proof.
  move /wt_inv => //=.
  move => [A0][B][hb][ha]he.
  move /regularity : hb => []//=.
  move => [s]/wt_inv => //=.
  move => [s1][s2][hA0][hB]hc.
  have ? : s2 = s by eauto using coherent'_forget, coherent_sort_inj. subst.
  have {}hB: Γ ⊢ B[a…] ∈ ISort s by sfirstorder use:wt_subst_sort.
  inversion he; subst;
  hauto q:on use:kind_imp.
Qed.

Lemma kind_int_preservation A B  (h : A ⇒ B) :
  forall Γ,  Γ ⊢ A ∈ ISort Kind ->
   kind_int A = kind_int B.
Proof.
  elim : A B / h; try done.
  - move => A0 A1 B0 B1 hA ihA hB ihB Γ hs.
    rewrite [kind_int]lock; move /wt_inv : hs => //=; rewrite -lock.
    move => [s1][s2][hA0][hB0]h.
    have ? : s2 = Kind by qauto use:coherent'_forget, coherent_sort_inj. subst.
    (* have : Γ ⊢ A1 ∈ ISort s1 by eauto using subject_reduction. *)
    case : s1 hA0.
    + move /[dup] /kind_has_int => [sk1 h0] ?.
      simpl.
      have -> : kind_int A1 = Some sk1 by sfirstorder.
      rewrite h0.
      f_equal.
      apply : ihB; eauto.
    + move => ?.
      simpl.
      have : kind_int A0 = None by eauto using kind_no_int.
      have : kind_int A1 = None by eauto using kind_no_int, subject_reduction.
      hauto lq:on.
  - firstorder using app_kind_imp.
Qed.

(* TODO: Add conditions that say that the set is saturated *)
Definition ρ_ok_kind (ρ : nat -> option {A : Skel & skel_int A}) Γ :=
  forall i (A : Term), Lookup i Γ A -> exists Sk S, kind_int A = Some Sk /\ ρ i = Some (existT Sk S).

(* Fixpoint type_int (Γ : Basis) *)
(*   (ρ : nat -> option {A : Skel & skel_int A}) (a : Term): *)
(*   option {A : Skel & skel_int A}. *)
(*   refine ( *)
(*       match a with *)
(*       | ISort s => Some (existT SK_Star SN) *)
(*       | VarTm i => ρ i *)
(*       | App a b => *)
(*           match type_int Γ ρ a, type_int Γ ρ b with *)
(*           | Some (existT sk1 S1), Some (existT sk2 S2) => _ *)
(*           | r, _ => r *)
(*           end *)
(*       | Abs A a => *)
(*           match kind_int A with *)
(*           | Some sk => *)

(*           | None => _ *)
(*           end *)
(*       | _ => _ *)
(*       end *)
(*     ). *)

Inductive type_interp (Γ : Basis) (ρ : nat -> option {A : Skel & skel_int A}) : Term -> forall (A : Skel), skel_int A -> Prop :=
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
  kind_int A = Some Sk1 ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk1 a) .: ρ) B  Sk2 S) ->
  (* ------------------------------ *)
  type_interp Γ ρ (Abs A B) (SK_Arr Sk1 Sk2) PF

| TI_AbsTm A B Sk S :
  kind_int A = None ->
  type_interp (A::Γ) (None .: ρ) B Sk S ->
  (* ------------------------------------ *)
  type_interp Γ ρ (Abs A B) Sk S

| TI_Pi A B S1 S2:
  kind_int A = None ->
  type_interp Γ ρ A SK_Star S1 ->
  type_interp (A::Γ) (None .: ρ) B SK_Star S2 ->
  (* ------------------------------------------------------------- *)
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S1 S2)

| TI_PiKind A Sk B S PF :
  kind_int A = Some Sk ->
  type_interp Γ ρ A SK_Star S  ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk a) .: ρ) B SK_Star S) ->
  type_interp Γ ρ (Pi A B) SK_Star (ProdSpace S (InterSpace PF)).


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

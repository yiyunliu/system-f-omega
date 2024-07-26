Require Export typing.

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

Definition ProdSpace (S0 S1 : Term -> Prop) b : Prop := forall a, S0 a -> S1 (App b a).

Inductive type_interp (Γ : Basis) (ξ : nat -> option {A : Skel & interp_skel A}) : Term -> forall (A : Skel), interp_skel A -> Prop :=
| TI_Star s :
  type_interp Γ ξ (ISort s) SK_Star SN

| TI_Var i Sk1 S :
  Some (existT Sk1 S) = ξ i ->
  type_interp Γ ξ (VarTm i) Sk1 S

| TI_App P Q Sk1 Sk2 S1 S2 F :
  type_interp Γ ξ P (SK_Arr Sk1 Sk2) F ->
  type_interp Γ ξ Q Sk1 S1 ->
  F S1 S2 ->
  (* -------------------- *)
  type_interp Γ ξ (App P Q) Sk2 S2

| TI_AppTm Sk P t A S  :
  type_interp Γ ξ P Sk S ->
  Γ ⊢ t ∈ A ->
  Γ ⊢ A ∈ ISort Star ->
  (* ------------------------------- *)
  type_interp Γ ξ (App P t) Sk S

| TI_Abs A B Sk1 Sk2 PF :
  kind_interp Γ A Sk1 ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk1 a) .: ξ) B  Sk2 S) ->
  (* ------------------------------ *)
  type_interp Γ ξ (Abs A B) (SK_Arr Sk1 Sk2) PF

| TI_AbsTm A B Sk S :
  Γ ⊢ A ∈ ISort Star ->
  type_interp (A::Γ) (None .: ξ) B Sk S ->
  (* ------------------------------------ *)
  type_interp Γ ξ (Abs A B) Sk S

| TI_Pi A B S1 S2:
  Γ ⊢ A ∈ ISort Star ->
  type_interp Γ ξ A SK_Star S1 ->
  type_interp (A::Γ) (None .: ξ) B SK_Star S2 ->
  (* ------------------------------------------------------------- *)
  type_interp Γ ξ (Pi A B) SK_Star (ProdSpace S1 S2)

| TI_PiKind A Sk B S PF :
  kind_interp Γ A Sk ->
  type_interp Γ ξ A SK_Star S  ->
  (forall a, exists S, PF a S) ->
  (forall a S, PF a S -> type_interp (A::Γ) (Some (existT Sk a) .: ξ) B SK_Star S) ->
  type_interp Γ ξ (Pi A B) SK_Star (ProdSpace S (fun b => forall a S, PF a S -> S b)).

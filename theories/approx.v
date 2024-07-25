Require Export imports typing.
Require Import Unicoq.Unicoq.

Inductive Skel : Set :=
| SK_Star : Skel
| SK_Arr : Skel -> Skel -> Skel.

Inductive Cls : Set :=
| C_Kind : Skel -> Cls
| C_Type : Skel -> Cls
| C_Term : Cls.

Definition EBasis := list Cls.

Inductive ELookup : nat -> EBasis -> Cls -> Prop :=
| EHere c Σ : ELookup 0 (c :: Σ) c
| EThere n c0 c1 Σ : ELookup n Σ c0 ->
                     ELookup (S n) (c1::Σ) c0.

(* Inductive HasCl Σ : Term -> Cls -> Prop := *)
(* | C_Sort : HasCl Σ (ISort Star) (C_Kind SK_Star) *)
(* | C_Var i c : ELookup i Σ c -> HasCl Σ (VarTm i) . *)
(* | *)

Definition down_cls c :=
  match c with
  | C_Kind sk => C_Type sk
  | C_Type sk => C_Term
  | _ => C_Term
  end.

Inductive Kind_Or_Else : Set :=
| KoE_Kind (sk : Skel)
| KoE_Else.

Definition Kind_Or_ElseP a :=
  match a with
  | C_Kind sk => KoE_Kind sk
  | _ => KoE_Else
  end.

Function cl_term Σ a : Cls :=
  match a with
  | ISort _ => C_Kind SK_Star
  | VarTm i => match nth_error Σ i with
              | Some c => down_cls c
              | _ => C_Term
              end
  | Abs A a => match cl_term Σ A , cl_term (cl_term Σ A :: Σ) a with
              | _, C_Kind _ => C_Kind SK_Star
              | C_Kind sk1, C_Type sk2 => C_Type (SK_Arr sk1 sk2)
              | _, c => c
              end
  | App a b => match cl_term Σ a, cl_term Σ b with
              | C_Kind _, _ => C_Kind SK_Star
              | C_Type (SK_Arr sk1 sk2), C_Type _ => C_Type sk2
              | c, _ => c
              end
  | Pi A B => match cl_term Σ A, cl_term (cl_term Σ A::Σ) B with
             | C_Kind sk1, C_Kind sk2 => C_Kind (SK_Arr sk1 sk2)
             | _, c => c
             end
  end.

Inductive loose_eqc : Cls -> Cls -> Prop :=
| L_Kind s :
  loose_eqc (C_Kind s) (C_Kind s)
| L_Type s1 s2 :
  loose_eqc (C_Type s1) (C_Type s2)
| L_Term :
  loose_eqc C_Term C_Term.

Scheme Equality for Skel.

Definition adj_cls c0 c1 :=
  match c0, c1 with
  | C_Type sk1, C_Kind sk2 => Skel_beq sk1 sk2
  | C_Term, C_Type _ => true
  | _, _ => false
  end.

Fixpoint cl_basis Γ :=
  match Γ with
  | nil => nil
  | A :: Γ => cl_term (cl_basis Γ) A :: cl_basis Γ
  end.

(* Lemma Kind_Or_ElseP a : *)
(*   Kind_Or_Else a a. *)
(* Proof. hauto lq:on inv:Cls ctrs:Kind_Or_Else. Qed. *)
(* nth_error (cl_basis Γ) i *)

Lemma cl_up_ren ξ (c : Cls) Σ0 Σ1 :
  (forall i, nth_error Σ0 i = nth_error Σ1 (ξ i)) ->
  (forall i, nth_error (c::Σ0) i = nth_error (c::Σ1) (upRen_Term_Term ξ i)).
Proof. qauto l:on inv:nat. Qed.

Lemma cl_term_abs_eq Σ0 a0 b0 Σ1 a1 b1 :
  cl_term Σ0 a0 = cl_term Σ1 a1 ->
  cl_term (cl_term Σ0 a0 :: Σ0) b0 = cl_term (cl_term Σ0 a0 :: Σ1) b1 ->
  cl_term Σ0 (Abs a0 b0) = cl_term Σ1 (Abs a1 b1).
Proof. hauto lq:on. Qed.

Lemma cl_term_pi_eq Σ0 a0 b0 Σ1 a1 b1 :
  cl_term Σ0 a0 = cl_term Σ1 a1 ->
  cl_term (cl_term Σ0 a0 :: Σ0) b0 = cl_term (cl_term Σ0 a0 :: Σ1) b1 ->
  cl_term Σ0 (Pi a0 b0) = cl_term Σ1 (Pi a1 b1).
Proof. hauto lq:on. Qed.

Lemma cl_term_renaming a ξ Σ0 Σ1 :
  (forall i, nth_error Σ0 i = nth_error Σ1 (ξ i)) ->
  cl_term Σ0 a = cl_term Σ1 (a⟨ξ⟩).
Proof.
  elim : a ξ Σ0 Σ1.
  - hauto lq:on.
  - sfirstorder.
  - sfirstorder use:cl_term_abs_eq, cl_up_ren.
  - hauto lq:on.
  - sfirstorder use:cl_term_pi_eq, cl_up_ren.
Qed.

Lemma Lookup_EBasis i Γ A (h : Lookup i Γ A) :
  nth_error (cl_basis Γ) i = Some (cl_term (cl_basis Γ) A).
Proof.
  elim : i Γ A / h; qauto l:on use:cl_term_renaming.
Qed.

Lemma adj_cls_abs_pi Σ A a B :
  adj_cls (cl_term (cl_term Σ A :: Σ) a) (cl_term (cl_term Σ A :: Σ) B) ->
  adj_cls (cl_term Σ (Abs A a)) (cl_term Σ (Pi A B)).
Proof. best. Qed.

Lemma adj_cls_app Σ b a c :
  adj_cls (cl_term Σ (App b a)) c = adj_cls (cl_term Σ b) c.
Proof. hauto lq:on rew:off. Qed.

Lemma adj_cls_pi Σ A B c :
  adj_cls (cl_term Σ (Pi A B)) c = adj_cls (cl_term (cl_term Σ A :: Σ) B) c.
Proof. hauto lq:on rew:off. Qed.

Lemma cl_term_sound Γ a A :
  Γ ⊢ a ∈ A ->
  forall s, Γ ⊢ A ∈ ISort s ->
  let Σ := cl_basis Γ in
  adj_cls (cl_term Σ a) (cl_term Σ A).
Proof.
  move => h /=. elim : Γ a A / h.
  (* Easy *)
  - simpl.
    move => Γ i A /Lookup_EBasis h s hA.
    rewrite h.
    admit.
  (* Contradiction *)
  - simpl.
    admit.
  (* Pi *)
  - move => Γ A s1 a B s2 hA ihA ha iha hB ihB s h.
    rewrite adj_cls_abs_pi.
    apply : iha; eauto.
  - move => Γ a b A B ha iha hb ihb s h.
    rewrite adj_cls_app.
    admit.
  - move => Γ A s1 B s2 hA ihA hB ihB s hs.
    rewrite adj_cls_pi. simpl.
    apply ihB with (s := s).
    admit.
  - move => Γ a A B s ha iha hB ihB h s0 hs0.
    admit.

Require Export par.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70, no associativity).
Reserved Notation "⊢ Γ" (at level 70, no associativity).

Definition Basis := list Term.

Fixpoint lookup n (Γ : Basis) :=
  match n, Γ with
  | O, (cons A  _) => Some (ren_Term S A)
  | S n, (cons _ Γ) => match lookup n Γ with
                       | None => None
                       | Some A => Some (ren_Term S A)
                       end
  | _ , _ => None
  end.

Inductive Lookup : nat -> Basis -> Term -> Prop :=
| Here A Γ : Lookup 0 (A :: Γ) (ren_Term S A)
| There n Γ A B : Lookup n Γ A ->
                     Lookup (S n) (cons B Γ) (ren_Term S A).

Lemma LookupIff n Γ A : Lookup n Γ A <-> lookup n Γ = Some A.
Proof.
  split.
  - elim; hauto lq:on.
  - elim : n Γ A; hauto q:on inv:list ctrs:Lookup.
Qed.

Lemma lookup_functional n Γ A B : Lookup n Γ A -> Lookup n Γ B -> A = B.
Proof. rewrite !LookupIff. congruence. Qed.

Derive Inversion lookup_inv with (forall i Γ A, Lookup i Γ A) Sort Prop.

Inductive Wt : Basis -> Term -> Term -> Prop :=
| T_Var Γ i A :
  ⊢ Γ ->
  Lookup i Γ A ->
  (* ----------- *)
  Γ ⊢ VarTm i ∈ A

| T_Star Γ :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ ISort Star ∈ ISort Kind

| T_Abs Γ A s1 a B s2 :
  Γ ⊢ A ∈ ISort s1 ->
  A :: Γ ⊢ a ∈ B ->
  A :: Γ ⊢ B ∈ ISort s2 ->
  (* -------------------- *)
  Γ ⊢ Abs A a ∈ Pi A B

| T_App Γ a b A B :
  Γ ⊢ a ∈ A ->
  Γ ⊢ b ∈ Pi A B ->
  (* --------------- *)
  Γ ⊢ App b a ∈ B[a…]

| T_Pi Γ A s1 B s2 :
  Γ ⊢ A ∈ ISort s1 ->
  A :: Γ ⊢ B ∈ ISort s2 ->
  (* -------------------- *)
  Γ ⊢ Pi A B ∈ ISort s2

| T_Conv Γ a A B s :
  Γ ⊢ a ∈ A ->
  Γ ⊢ B ∈ ISort s ->
  A ⇔ B ->
  (* ------------ *)
  Γ ⊢ a ∈ B

with Wf : Basis -> Prop :=
| Wf_Nil :
  (* --- *)
  ⊢ nil

| Wf_Cons Γ A s :
  ⊢ Γ ->
  Γ ⊢ A ∈ ISort s ->
  (* ----------- *)
  ⊢ A :: Γ

where "Γ ⊢ a ∈ A" := (Wt Γ a A) and "⊢ Γ" := (Wf Γ).

Scheme Wt_ind_2 := Induction for Wt Sort Prop
    with Wf_ind_2 := Induction for Wf Sort Prop.
Combined Scheme Wt_multind from Wt_ind_2, Wf_ind_2.

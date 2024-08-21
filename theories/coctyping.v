Require Import cocpar.

Definition CBasis := list CTm.

Fixpoint lookup n (Γ : CBasis) :=
  match n, Γ with
  | O, (cons A  _) => Some (ren_CTm S A)
  | S n, (cons _ Γ) => match lookup n Γ with
                       | None => None
                       | Some A => Some (ren_CTm S A)
                       end
  | _ , _ => None
  end.

Inductive Lookup : nat -> CBasis -> CTm -> Prop :=
| Here A Γ : Lookup 0 (A :: Γ) (ren_CTm S A)
| There n Γ A B : Lookup n Γ A ->
                     Lookup (S n) (cons B Γ) (ren_CTm S A).

Lemma LookupIff n Γ A : Lookup n Γ A <-> lookup n Γ = Some A.
Proof.
  split.
  - elim; hauto lq:on.
  - elim : n Γ A; hauto q:on inv:list ctrs:Lookup.
Qed.

Lemma lookup_functional n Γ A B : Lookup n Γ A -> Lookup n Γ B -> A = B.
Proof. rewrite !LookupIff. congruence. Qed.

Derive Inversion lookup_inv with (forall i Γ A, Lookup i Γ A) Sort Prop.

Inductive Wt : CBasis -> CTm -> CTm -> Prop :=
| T_Var Γ i A :
  Wf Γ ->
  Lookup i Γ A ->
  (* ----------- *)
  Wt Γ (VarCTm i) A

| T_Star Γ :
  Wf Γ ->
  (* --------- *)
  Wt Γ (CTmSort CStar) (CTmSort CKind)

| T_Abs Γ A s1 a B s2 :
  Wt Γ A (CTmSort s1) ->
  Wt (A :: Γ) a B ->
  Wt (A :: Γ) B (CTmSort s2) ->
  (* -------------------- *)
  Wt Γ (CTmAbs a) (CTmForall A B)

| T_App Γ a b A B :
  Wt Γ a A ->
  Wt Γ b (CTmForall A B) ->
  (* --------------- *)
  Wt Γ (CTmApp b a) (subst_CTm (a…) B)

| T_Pi Γ A s1 B s2 :
  Wt Γ A (CTmSort s1) ->
  Wt (A :: Γ) B (CTmSort s2) ->
  (* -------------------- *)
  Wt Γ (CTmForall A B) (CTmSort s2)

| T_Conv Γ a A B s :
  Wt Γ a A ->
  Wt Γ B (CTmSort s) ->
  Coherent A B ->
  (* ------------ *)
  Wt Γ a B

with Wf : CBasis -> Prop :=
| Wf_Nil :
  (* --- *)
  Wf nil

| Wf_Cons Γ A s :
  Wf Γ ->
  Wt Γ A (CTmSort s) ->
  (* ----------- *)
  Wf (A :: Γ).

Scheme Wt_ind_2 := Induction for Wt Sort Prop
    with Wf_ind_2 := Induction for Wf Sort Prop.
Combined Scheme Wt_multind from Wt_ind_2, Wf_ind_2.

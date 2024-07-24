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


Fixpoint cl_term Σ a : Cls :=
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

Definition adj_cls c0 c1 :=
  match c0, c1 with
  | C_Type _, C_Kind _ => true
  | C_Term, C_Type _ => true
  | _, _ => false
  end.

Fixpoint cl_basis Γ :=
  match Γ with
  | nil => nil
  | A :: Γ => cl_term (cl_basis Γ) A :: cl_basis Γ
  end.

Inductive Kind_Or_Else a : Cls ->  Prop :=
| KoE_Kind sk : Kind_Or_Else a (C_Kind sk)
| KoE_Else : Kind_Or_Else a a.

Lemma Kind_Or_ElseP a :
  Kind_Or_Else a a.
Proof. hauto lq:on inv:Cls ctrs:Kind_Or_Else. Qed.

Lemma cl_term_sound Γ a A :
  Γ ⊢ a ∈ A ->
  forall s, Γ ⊢ A ∈ ISort s ->
  let Σ := cl_basis Γ in
  adj_cls (cl_term Σ a) (cl_term Σ A).
Proof.
  move => h /=. elim : Γ a A / h.
  (* Easy *)
  - simpl.
    admit.
  (* Contradiction *)
  - simpl.
    admit.
  (*  *)
  - move => Γ A s1 a B s2 hA ihA ha iha hB ihB s h /=.
    move E : (cl_term (cl_basis Γ) A) => c0.
    case : (Kind_Or_ElseP c0) E.
    + admit.
    + case :

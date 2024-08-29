Require Export typing.
From Equations Require Import Equations.

Definition ren_ok {T} f (Δ0 Δ1 : list T) := forall i k, Lookup i Δ0 k -> Lookup (f i)  Δ1 k.

Equations ren_up {T f k} (Δ0 Δ1 : list T) (hf : ren_ok f Δ0 Δ1) : ren_ok (upRen_Ty_Ty f) (k :: Δ0) (k :: Δ1) :=
  ren_up Δ0 Δ1 hf _ _ (Here k Δ0) := (Here k Δ1);
  ren_up Δ0 Δ1 hf _ _ (There n Δ0 k0 k l) := There _ _ _ _ (hf _ _ l).

Definition ren_ok' {T} f (Δ0 Δ1 : list T) := prod (forall i k, Lookup i Δ0 k -> Lookup (f i) Δ1 k) (forall i k, Lookup (f i) Δ1 k -> Lookup i Δ0 k ).

Lemma ren'_up {T f k} (Δ0 Δ1 : list T) (hf : ren_ok' f Δ0 Δ1) : ren_ok' (upRen_Ty_Ty f) (k :: Δ0) (k :: Δ1).
Proof.
  rewrite /ren_ok' in hf *.
  destruct hf as [hf0 hf1].
  split.
  - sfirstorder use:ren_up unfold:ren_ok.
  - inversion 1; subst.
    case : i X H0 => //=.
    hauto l:on.
    case : i H0 X X0 => //=.
    intros n0. rewrite /funcomp.
    move => [?]. subst.
    sauto lq:on.
Qed.

Lemma ren_S' {T} (k : T) Δ  : ren_ok' S Δ (k :: Δ).
  rewrite /ren_ok'.
  sauto lq:on.
Qed.

Lemma ty_antirenaming {Δ0 Δ1 f A k} (h : TyWt Δ1 (ren_Ty f A) k) (hf : ren_ok' f Δ0 Δ1) : TyWt Δ0 A k.
Proof.
  move : h.
  move E : (ren_Ty f A) => U h.
  move : Δ0 f hf A E.
  elim : Δ1 U k /h.
  - move => Δ i k hk Δ0 f hf []//.
    simpl.
    move => n [?]. subst.
    apply TyT_Var. rewrite /ren_ok' in hf.
    sfirstorder.
  - move => Δ A k0 k1 hA ihA Δ0 f hf []//=.
    hauto l:on use:ren'_up, TyT_Abs.
  - move => Δ b a k0 k1 hb ihb ha iha Δ0 f hf []//=.
    hauto lq:on use:TyT_App.
  - move => Δ A B hA ihA hB ihB Δ0 f hf []//=.
    hauto lq:on use:TyT_Fun.
  - move => Δ k A hA ihA Δ0 f hf []//=.
    hauto l:on use:ren'_up, TyT_Forall.
Qed.

Equations ty_renaming {Δ0 Δ1 f A k} (h : TyWt Δ0 A k) (hf : ren_ok f Δ0 Δ1) : TyWt Δ1 (ren_Ty f A) k :=
  ty_renaming (TyT_Var i k l) hf := TyT_Var Δ1 (f i) k (hf _ _ l) ;
  ty_renaming (TyT_App b a k0 k1 hb ha) hf :=
    TyT_App Δ1 (ren_Ty f b) (ren_Ty f a) k0 k1 (ty_renaming hb hf) (ty_renaming ha hf) ;
  ty_renaming (TyT_Fun A B hA hB) hf :=
    TyT_Fun Δ1 (ren_Ty f A) (ren_Ty f B) (ty_renaming hA hf) (ty_renaming hB hf) ;
  ty_renaming (TyT_Abs A k0 k1 hA) hf :=
    TyT_Abs Δ1 _ k0 k1 (ty_renaming hA (ren_up _ _ hf)) ;
  ty_renaming (TyT_Forall k A hA) hf :=
    TyT_Forall Δ1 k _ (ty_renaming hA (ren_up _ _ hf)).

Equations ren_S {T} (k : T) Δ  : ren_ok S Δ (k :: Δ) :=
  ren_S k Δ i k0 l := There _ _ _ _ l.

Lemma ty_weakening Δ A k k0 (h : TyWt Δ A k) :
  TyWt (k0 :: Δ) (ren_Ty S A) k.
Proof.
  eauto using @ty_renaming, @ren_S.
Defined.

Definition morph_ok ρ Δ0 Δ1  :=
  forall i k, Lookup i Δ0 k ->
         TyWt Δ1 (ρ i) k.

Equations morph_ok_ext ρ Δ0 Δ1 (h : morph_ok ρ Δ0 Δ1) A k (h0 : TyWt Δ1 A k) :
  morph_ok (A .: ρ) (k :: Δ0) Δ1 :=
  morph_ok_ext ρ Δ0 Δ1 h A k h0 i k (Here k Δ0) := h0 ;
  morph_ok_ext ρ Δ0 Δ1 h A k h0 j k0 (There Δ0 k0 k l) := h _ _ l.

Definition morph_ren_comp ξ ρ Δ0 Δ1 Δ2 (h : morph_ok ρ Δ0 Δ1) (h0 : ren_ok ξ Δ1 Δ2) :
  morph_ok (ρ >> ren_Ty ξ) Δ0 Δ2.
  intros i k l.
  change ((ρ >> ren_Ty ξ) i) with (ren_Ty ξ (ρ i)).
  eapply ty_renaming.
  apply h. apply l.
  apply h0.
Defined.

Definition morph_id Δ :
  morph_ok ids Δ Δ.
  unfold morph_ok.
  apply TyT_Var.
Defined.

Definition morph_up ρ Δ0 Δ1 (h : morph_ok ρ Δ0 Δ1) k :
  morph_ok (up_Ty_Ty ρ) (k :: Δ0) (k :: Δ1).
  unfold up_Ty_Ty.
  apply morph_ok_ext.
  apply morph_ren_comp with (Δ1 := Δ1).
  apply h.
  apply ren_S.
  apply TyT_Var.
  apply Here.
Defined.

#[export]Hint Constructors TyWt : wt.

Lemma ty_morphing {Δ0 A k} (h : TyWt Δ0 A k):
  forall {Δ1 ρ},
    morph_ok ρ Δ0 Δ1 ->
    TyWt Δ1 (subst_Ty ρ A) k.
Proof.
  induction h; simpl; eauto using morph_up with wt.
Defined.

Lemma ty_subst {Δ A B k0 k} (h : TyWt (k :: Δ) A k0) (h0 : TyWt Δ B k) :
  TyWt Δ (subst_Ty (B…) A) k0.
Proof.
  apply @ty_morphing with (Δ0 := k :: Δ).
  apply h.
  eauto using morph_ok_ext, morph_id.
Defined.

Lemma ty_preservation Δ A B k :  TyWt Δ A k -> TyPar A B -> TyWt Δ B k.
Proof.
  move => + h. move : Δ k.
  elim : A B /h.
  - done.
  - hauto lq:on inv:TyWt ctrs:TyWt use:ty_subst.
  - hauto lq:on inv:TyWt ctrs:TyWt.
  - move => k b0 b1 a0 a1 hb ihb ha iha Δ k0.
    inversion 1; subst.
    inversion X0; subst.
    qauto l:on use:ty_subst.
  - hauto lq:on rew:off inv:TyWt ctrs:TyWt.
  - hauto lq:on inv:TyWt ctrs:TyWt.
Qed.

Lemma ty_preservation_star Δ A B k :  TyWt Δ A k -> RTC A B -> TyWt Δ B k.
Proof.
  move => + h.
  induction h; hauto l:on use:ty_preservation.
Qed.

Equations regularity {Δ Γ a A} (h : Wt Δ Γ a A) : TyWt Δ A Star :=
regularity (a := ?(VarTm i)) (A := ?(A)) (T_Var i A hwf hl) := hwf _ _ hl ;
regularity (a := ?(TmAbs a)) (A := ?(TyFun A B)) (T_Abs A a B hA ha) :=
  TyT_Fun Δ A B hA (regularity ha) ;
regularity (a := ?(TmApp b a)) (A := ?(B)) (T_App a b A B ha hb)
  with regularity hb  := { | TyT_Fun A B h0 h1 => h1} ;
regularity (T_Forall k a A ha) :=
  TyT_Forall Δ k A (regularity ha) ;
regularity (T_Inst k a A B hB ha)
  with regularity ha := { | TyT_Forall k A hA => ty_subst hA hB } ;
regularity (A := ?(B)) (T_Conv a A B C ha hB _ _) := hB.

Fixpoint int_kind k :=
  match k with
  | Star => Tm -> Prop
  | Arr k0 k1 => int_kind k0 -> int_kind k1
  end.

Definition ty_val Δ :=
  forall i k (l : Lookup i Δ k), int_kind k.

Equations V_Nil : ty_val nil := V_Nil i k !.

Equations V_Cons {Δ k} (h : int_kind k) (ξ : ty_val Δ) : ty_val (k :: Δ) :=
  V_Cons h ξ ?(0) ?(k) (Here k Δ) := h ;
  V_Cons h ξ ?(S n) ?(k0) (There n Δ0 k0 k1 l) := ξ n k0 l.

Definition ty_val_ren {Δ Δ'}
  (ξ : ty_val Δ') f
  (hf : forall i k, Lookup i Δ k -> Lookup (f i) Δ' k) : ty_val Δ :=
  fun i k l => ξ (f i) k (hf _ _ l).

Definition SFun SA SB b : Prop := forall a, SA a -> SB (TmApp b a).

Equations adequateP k (s : int_kind k) : Prop :=
  adequateP Star := fun s => CR s ;
  adequateP (Arr k0 k1) := fun s => forall b, adequateP k0 b -> adequateP k1 (s b).

Definition ty_val_ok Δ (ξ : ty_val Δ) := forall i k l, adequateP k (ξ i k l).

Equations int_type {Δ A k} (h : TyWt Δ A k) (ξ : ty_val Δ) : int_kind k :=
  int_type (TyT_Var i k l) ξ := ξ i k l ;
  int_type (TyT_Abs A k0 k1 hA) ξ := fun s0 => int_type hA (V_Cons s0 ξ);
  int_type (TyT_App b a k0 k1 hb ha) ξ := int_type hb ξ (int_type ha ξ);
  int_type (TyT_Fun A B hA hB) ξ :=
    fun b => forall a, (int_type hA ξ) a -> (int_type hB ξ) (TmApp b a);
  int_type (TyT_Forall k A hA) ξ :=
    fun b => forall s, adequateP _ s -> int_type hA (V_Cons s ξ) b.

Lemma kind_unique Δ A k (h0 : TyWt Δ A k ) : forall k0, TyWt Δ A k0 -> k = k0.
Proof.
  induction h0; hauto lq:on rew:off inv:TyWt use:@lookup_functional.
Qed.

Derive EqDec for Ki.
Set Equations With UIP.

Lemma lookup_unique  i (Γ : list Ki) A (h0 h1 : Lookup i Γ A) : h0 = h1.
  move : h1.
  induction h0.
  - move => h1.
    dependent elimination h1 => //=.
  - move => h1.
    dependent elimination h1 => //=.
    apply f_equal.
    apply IHh0.
Qed.

Lemma int_type_irrel {Δ A k} (h h0 : TyWt Δ A k) (ξ : ty_val Δ) :
  int_type h ξ = int_type h0 ξ.
Proof.
  move : ξ h0.
  elim : Δ A k /h.
  - intros .
    dependent elimination h0.
    have : l = l0 by eauto using lookup_unique.
    congruence.
  - intros Δ A k0 k1 t iht ξ h0.
    dependent elimination h0.
    simp int_type.
    extensionality x.
    apply iht.
  - intros.
    dependent elimination h0.
    simp int_type.
    have ? : k4 = k0 by eauto using kind_unique. subst.
    scongruence.
  - intros.
    dependent elimination h0.
    simp int_type.
    have [-> ->] : int_type t ξ = int_type t4 ξ /\ int_type t0 ξ = int_type t5 ξ
      by hauto l:on.
    done.
  - intros.
    dependent elimination h0.
    simpl.
    simp int_type.
    extensionality b.
    have ? : forall s, int_type t (V_Cons s ξ) = int_type t5 (V_Cons s ξ) by scongruence.
    apply propositional_extensionality.
    qauto l:on.
Qed.

Lemma int_type_ren {Δ Δ' A k} (h : TyWt Δ A k)
  (ξ : ty_val Δ)
  (ξ' : ty_val Δ') f
  (hf : forall i k, Lookup i Δ k -> Lookup (f i) Δ' k)
  (hξ : forall i k (l : Lookup i Δ k), ξ i k l = ξ' (f i) k (hf i k l)) :
  int_type h ξ = int_type (ty_renaming h hf) ξ'.
Proof.
  move : ξ Δ' ξ' f hf hξ.
  elim : Δ A k / h.
  - move => *. simp ty_renaming int_type.
  - move => Δ A k0 k1 h ih ξ Δ' ξ' f hf hl.
    simp int_type ty_renaming => /=.
    extensionality s0. simp int_type.
    apply ih.
    move => i k l.
    dependent elimination l; sfirstorder rew:db:ren_up.
  - hauto q:on rew:db:ty_renaming, int_type.
  - hauto q:on rew:db:ty_renaming, int_type.
  - move => Δ k A hA ihA ξ Δ' ξ' f hf h.
    simp ty_renaming int_type.
    rewrite int_type_equation_5.
    have : forall s, int_type hA (V_Cons s ξ) = int_type (ty_renaming hA (ren_up Δ Δ' hf)) (V_Cons s ξ') by
        move => s; apply ihA => i k0 l;
                              dependent elimination l; sfirstorder rew:db:ren_up.
    clear => h.
    extensionality s.
    apply propositional_extensionality.
    have : forall P0 P1, (forall s, P0 s = P1 s) -> (forall s, (P0 s : Prop)) <-> (forall s, P1 s) by hauto lq:on.
    apply.
    hauto lq:on.
Qed.

Lemma int_type_morph {Δ Δ' A k} (h : TyWt Δ A k) :
  forall ρ
    (ξ : ty_val Δ)
    (ξ' : ty_val Δ')
    (hρ : forall i k, Lookup i Δ k -> TyWt Δ' (ρ i) k),
    (forall i k (l : Lookup i Δ k), ξ _ _ l = int_type (hρ _ _ l) ξ') ->
    int_type h ξ = int_type (ty_morphing h hρ) ξ'.
Proof.
  move : Δ'.
  elim : Δ A k /h.
  - move => *. simp int_type.
  - move => Δ A k0 k1 hA ihA Δ' ρ ξ ξ' hρ hρ' /=.
    simp int_type.
    extensionality s.
    apply ihA.
    intros i k l.
    dependent elimination l.
    + rewrite /morph_up. simp morph_ok_ext.
      simpl.
      by simp V_Cons.
    + rewrite /morph_up. simp morph_ok_ext.
      simp V_Cons.
      rewrite /morph_ren_comp.
      have <- : int_type (hρ n A1 l) ξ' = int_type (ty_renaming (hρ n A1 l) (ren_S B Δ')) (V_Cons s ξ')
        by hauto l:on use:int_type_ren rew:db:V_Cons, ren_S.
      apply hρ'.
  - hauto l:on rew:db:int_type.
  - hauto l:on rew:db:int_type.
  - move => Δ k A hA ihA Δ' ρ ξ ξ' hρ hρ'.
    simpl.
    simp int_type. extensionality b.
    have : forall s, int_type hA (V_Cons s ξ) = int_type (ty_morphing hA (morph_up ρ Δ Δ' hρ k)) (V_Cons s ξ').
    {
      move => s. apply ihA.
      move => i k0 l. dependent elimination l. reflexivity.
      simp V_Cons. rewrite /morph_up /morph_ren_comp.
      simp morph_ok_ext int_type V_Cons ty_renaming.
      have <- : int_type (hρ n A1 l) ξ' = int_type (ty_renaming (hρ n A1 l) (ren_S B Δ')) (V_Cons s ξ') by
        hauto l:on use:int_type_ren rew:db:V_Cons, ren_S.
      apply hρ'.
    }
    clear => h.
    apply propositional_extensionality.
    qauto l:on.
Qed.

Lemma ty_sem_preservation Δ A B k (h0 : TyWt Δ A k) (h1 : TyWt Δ B k) ξ :
  TyPar A B ->
  int_type h0 ξ  = int_type h1 ξ.
  move : B h1 ξ.
  elim : Δ A k /h0.
  - inversion 1. subst.
    dependent elimination h1.
    hauto lq:on rew:off use:lookup_unique.
  - move => Δ A k0 k1 hA ihA B hB ξ.
    dependent elimination hB; try solve [inversion 1].
    inversion 1; subst.
    simpl.
    extensionality s.
    simp int_type.
  - move => Δ B A k0 k1 hB ihB hA ihA T h1 ξ.
    simpl.
    inversion 1; subst.
    + dependent elimination h1.
      simpl.
      rename b into B'.
      rename a into A'.
      have [*] : Arr k4 k5 = Arr k0 k5 by qauto l:on use:kind_unique, ty_preservation. subst.
      suff : int_type hB ξ = int_type t0 ξ by hauto l:on use:int_type_irrel rew:db:int_type.
      by apply ihB.
    + rename A into a0.
      have hp : TyPar (TyAbs k b0) (TyAbs k b1) by hauto lq:on ctrs:TyPar.
      have hp' : TyWt Δ (TyAbs k b1) (Arr k0 k1)
        by hauto lq:on rew:off ctrs:TyWt, TyPar inv:TyPar use:ty_preservation.
      move : ihB (hp); repeat move/[apply].
      move /(_ hp' ξ). simp int_type.
      move => ->.
      dependent elimination hp'.
      simpl.
      have h : TyWt Δ a1 k3 by eauto using ty_preservation.
      have -> : int_type h1 ξ = int_type (ty_subst t h) ξ by hauto l:on use:int_type_irrel.
      simp int_type.
      apply int_type_morph.
      (* TODO: deduplicate *)
      move => i k l.
      dependent elimination l.
      * simp morph_ok_ext V_Cons.
      * simp morph_ok_ext V_Cons.
        by simpl.
  - move => Δ A B hA ihA hB ihB T h1 ξ.
    inversion 1; subst.
    dependent elimination h1.
    hauto l:on rew:db:int_type.
  - move => Δ k A hA ihA B hB ξ.
    inversion 1; subst.
    dependent elimination hB.
    simpl.
    extensionality a.
    simp int_type.
    have h : forall s, int_type hA (V_Cons s ξ) a = int_type t4 (V_Cons s ξ) a
        by hauto lq:on.
    apply propositional_extensionality.
    hauto l:on.
Qed.

Lemma ty_sem_preservation_star Δ A B k (h0 : TyWt Δ A k) (h1 : TyWt Δ B k) ξ :
  RTC A B ->
  int_type h0 ξ  = int_type h1 ξ.
Proof.
  induction 1.
  - hauto lq:on use:int_type_irrel.
  - have : TyWt Δ B k  by hauto l:on use:ty_preservation.
    hauto lq:on use:@ty_sem_preservation.
Qed.

Definition tm_val ρ Δ ξ Γ :=
  forall i A (l : Lookup i Γ A) (h : TyWt Δ A Star), int_type h ξ (ρ i).

Equations T_Nil {ρ Δ ξ} : tm_val ρ Δ ξ nil :=
  T_Nil i A !.

Check int_type.
Compute int_kind Star.

Equations T_Cons ρ Δ (ξ : ty_val Δ) A Γ a (h : TyWt Δ A Star)
  (hρ : tm_val ρ Δ ξ Γ) (ha : int_type h ξ a) : tm_val (a .: ρ) Δ ξ (A :: Γ) :=
  T_Cons ρ Δ ξ ?(A) ?(Γ) a h hρ ha ?(0) A (Here A Γ) h0
    with int_type_irrel h h0 ξ, int_type h ξ := { | eq_refl , _ := ha } ;
  T_Cons ρ Δ ξ ?(A) ?(Γ) a h hρ ha i A0 (There n Γ A0 A l) h0 := hρ n A0 l h0.

Lemma VO_Cons Δ ξ (h : ty_val_ok Δ ξ) k s :
  adequateP k s -> ty_val_ok (k :: Δ) (V_Cons s ξ).
Proof.
  move => hs.
  rewrite /ty_val_ok.
  move => i k0 l.
  dependent elimination l.
  - simp V_Cons.
  - simp adequateP V_Cons.
    apply h.
Qed.

Lemma lookup_map_inv {T U} (f : T -> U) i Γ A : Lookup i (map f Γ) A -> {b : T &  ( prod (Lookup i Γ b) (A = f b))}.
  move E : (list_map f Γ) => Δ h.
  move : Γ E.
  elim : i Δ A /h; sauto lq:on rew:off.
Defined.

Equations def_cand k : int_kind k :=
  def_cand Star := SN ;
  def_cand (Arr k0 k1) := const (def_cand k1).

Lemma def_cand_adequate k : adequateP _ (def_cand k).
  elim k => /=.
  - firstorder using red_props.CR_SN.
  - move => k0 hk0 k1 hk1.
    simp adequateP.
Qed.

Lemma adequacy Δ A k (h : TyWt Δ A k) ξ (hξ : ty_val_ok Δ ξ) :
  adequateP _ (int_type h ξ).
Proof.
  move : ξ hξ.
  elim : Δ A k / h.
  - move => Δ i k l ξ hξ. simp int_type. apply hξ.
  - hauto l:on use:VO_Cons rew:db:adequateP, int_type.
  - hauto l:on rew:db:int_type, adequateP.
  - hauto l:on use:red_props.CR_Prod rew:db:int_type, adequateP.
  - move => Δ k *.
    hauto lq:on use:(def_cand_adequate k), red_props.CR_Forall, VO_Cons
      rew:db:int_type, adequateP.
Qed.

Definition def_val Δ i k (l : Lookup i Δ k) := def_cand k.

Lemma def_val_adequate Δ : ty_val_ok Δ (def_val Δ).
Proof.
  rewrite /def_val /ty_val_ok.
  eauto using def_cand_adequate.
Qed.

Lemma var_tm_id Δ Γ : tm_val VarTm Δ (def_val Δ) Γ.
Proof.
  rewrite /tm_val.
  move => i A hA h.
  have : adequateP _ (int_type h (def_val Δ))
    by eauto using adequacy, def_val_adequate.
  simp adequateP. move /CR3.
  apply.
  apply S_Var.
Qed.

Lemma soundness Δ Γ a A (h : Wt Δ Γ a A) :
  forall ξ (hξ : ty_val_ok Δ ξ) ρ (hρ : tm_val ρ Δ ξ Γ),
    int_type (regularity h) ξ (subst_Tm ρ a).
Proof.
  elim : Δ Γ a A / h.
  - move => Δ Γ i A hΓ l ξ hξ ρ hρ.
    simp int_type regularity.
    by apply hρ.
  - move => Δ Γ A a B hA ha iha ξ hξ ρ hρ.
    simp int_type regularity.
    move => a0 ha0.
    have ha0' : adequateP _ (int_type hA ξ) by hauto l:on use:adequacy.
    have : adequateP _ (int_type (regularity ha) ξ) by hauto l:on use:adequacy.
    simp adequateP in *.
    move /CR2.
    apply => /=.
    apply S_AppAbs.
    by apply ha0'.
    asimpl.
    apply : iha => //.
    hauto l:on use:T_Cons.
  - move => Δ Γ a b A B ha iha hb ihb ξ hξ ρ hρ.
    simp int_type regularity.
    move E : (regularity hb) => S.
    dependent elimination S.
    simp regularity => /=.
    specialize iha with (1 := hξ) (2 := hρ).
    specialize ihb with (1 := hξ) (2 := hρ).
    rewrite E in iha ihb.
    simp int_type in ihb.
    apply : ihb.
    hauto lq:on use:int_type_irrel.
  - move => Δ Γ k a A ha iha ξ hξ ρ hρ.
    simp int_type regularity.
    move => s hs.
    apply iha.
    hauto l:on use:VO_Cons.
    rewrite /up_Basis /tm_val.
    move => i A0 hA0.
    have [A1 [hl ?]] : {b : Ty & prod (Lookup i Γ b) (A0 = ren_Ty S b)}
      by eauto using lookup_map_inv. subst.
    apply hρ in hl.
    move => h0.
    have h1 : TyWt Δ A1 Star by eauto using ty_antirenaming, ren_S'.
    specialize (hl h1).
    have : int_type h1 ξ = int_type (ty_renaming h1 (ren_S _ _)) (V_Cons s ξ).
    + hauto l:on use:int_type_ren rew:db:ren_S, V_Cons.
    + have -> : int_type (ty_renaming h1 (ren_S k Δ)) (V_Cons s ξ) = int_type h0 (V_Cons s ξ)
        by eauto using int_type_irrel.
      congruence.
  - move => Δ Γ k a A B hB ha iha ξ hξ ρ hρ.
    simp int_type regularity.
    move E : (regularity ha) => S.
    dependent elimination S.
    simp regularity.
    specialize iha with (1 := hξ) (2 := hρ).
    rewrite E in iha.
    simp int_type in iha.
    suff <- : int_type t4 (V_Cons (int_type hB ξ) ξ) = int_type (ty_subst t4 hB) ξ by hauto l:on use:adequacy.
    apply int_type_morph; intros i k l;
      dependent elimination l; by simp morph_ok_ext V_Cons.
  - move => Δ Γ a A B C ha iha hB hAC hBC ξ hξ ρ hρ.
    simp int_type regularity.
    specialize iha with (1 := hξ) (2 := hρ).
    suff : int_type (regularity ha) ξ = int_type hB ξ by congruence.
    have h1 : TyWt Δ C Star by eauto using ty_preservation_star.
    have -> : int_type hB ξ = int_type h1 ξ by hauto l:on use:ty_sem_preservation_star.
    hauto l:on use:ty_sem_preservation_star.
Qed.

Theorem f_omega_sn Δ Γ a A : Wt Δ Γ a A -> SN a.
Proof.
  move => h. have h0 := soundness.
  specialize h0 with (1 := def_val_adequate Δ) (2 := var_tm_id Δ Γ).
  specialize (h0 a A h).
  have : adequateP _ (int_type (regularity h) (def_val Δ)) by
    eauto using adequacy, def_val_adequate.
  simp adequateP.
  move /CR1. apply.
  by asimpl in h0.
Qed.

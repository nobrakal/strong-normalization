Set Implicit Arguments.
Require Import Coq.Arith.Arith_base.

Inductive type : Set :=
| Iota
| Arrow (x:type) (y:type).

(* Inductive lambda {A : Set} : type -> Set :=
| Var (t:type) (x:A) : lambda t
| Lam (t1:type) (x:A) {t2:type} (b:lambda t2) : lambda (Arrow t1 t2)
| App {t1 t2:type} (x:lambda (Arrow t1 t2)) (y:lambda t1) : lambda t2. *)

Require Import Coq.Sets.Ensembles.

(* Type of type *)
Fixpoint tot (t:type) : Type :=
  match t with
  | Iota => nat
  | Arrow x y => (tot x) -> (tot y) end.

Definition Fun {A B} (a: Ensemble A) (b: Ensemble B) : Ensemble (A -> B) :=
  fun f => forall x, a x -> b (f x).

Fixpoint comparet t : tot t -> tot t -> Prop :=
  match t as t return tot t -> tot t -> Prop with
  | Iota => lt
  | Arrow t1 t2 =>
    fun f g =>
      let it1 := interp t1 in
      let it2 := interp t2 in
      (((Fun it1 it2) f /\ (Fun it1 it2) g)) /\
      forall x, it1 x -> comparet t2 (f x) (g x)
  end
with interp t: Ensemble (tot t) :=
  match t as t return Ensemble (tot t) with
  | Iota => Full_set nat
  | Arrow t1 t2 =>
    fun f : tot (Arrow t1 t2) =>
      (Fun (interp t1) (interp t2)) f /\
      (forall v1 v2, (interp t1) v1 ->
                     (interp t1) v2 ->
                     comparet t1 v1 v2 -> comparet t2 (f v1) (f v2))
  end.

(* Prop 1 *)
Lemma comparet_trans (t:type): forall x y z,
    comparet t x y -> comparet t y z -> comparet t x z.
Proof.
  induction t.
  - exact lt_trans.
  - simpl; intros.
    decompose [and] H.
    intuition.
    specialize H5 with x0.
    specialize H6 with x0.
    specialize IHt2 with (x x0) (y x0) (z x0).
    intuition.
Qed.

Fixpoint plus (t:type) : tot t -> nat -> tot t :=
  match t as t return tot t -> nat -> tot t with
  | Iota => fun x k => x + k
  | Arrow t1 t2 =>
    fun f k =>
      fun x => plus t2 (f x) k end.

Lemma plus_arr t1 t2 : plus (Arrow t1 t2) = fun f k x => plus t2 (f x) k.
Proof. auto. Qed.

Lemma in_interp_arrow {t1 t2 v} : forall x, interp (Arrow t1 t2) v -> interp t1 x -> interp t2 (v x).
Proof.
  intros.
  simpl in H.
  destruct H as (H,_).
  unfold Fun in H.
  specialize H with x.
  exact (H H0).
Qed.

Require Import Lia.

Definition Plus_well_def (t:type) := forall x k, interp t x -> interp t (plus t x k).

Definition Compare_compat_plus (t:type) :=
  forall v1 v2 k,
    interp t v1 -> interp t v2 ->
    comparet t v1 v2 -> comparet t (plus t v1 k) (plus t v2 k).

Lemma prop_2 (t:type) : Plus_well_def t /\ Compare_compat_plus t.
Proof.
  unfold Plus_well_def; unfold Compare_compat_plus.
  induction t.
  - split.
    + intros.
      exact (Full_intro nat (x+k)).
    + intros; simpl. unfold comparet in H1.
      lia.
  - destruct IHt1 as (PWDt1,CPTt1).
    destruct IHt2 as (PWDt2,CPTt2).
    split.
    + intros.
      rewrite plus_arr; fold tot.
      simpl.
      split.
      * unfold Fun.
        intros.
        apply PWDt2.
        exact (in_interp_arrow x0 H H0).
      * intros.
        apply (CPTt2 (x v1) (x v2) k (in_interp_arrow v1 H H0) (in_interp_arrow v2 H H1)).
        simpl in H.
        destruct H as (_,H).
        intuition.
    + intros; simpl; intros.
      fold tot.
      split.
      * split.
        ** unfold Fun.
           intros.
           apply PWDt2.
           exact (in_interp_arrow x H H2).
        ** unfold Fun.
           intros.
           apply PWDt2.
           exact (in_interp_arrow x H0 H2).
      * intros.
        apply CPTt2.
        exact (in_interp_arrow x H H2).
        exact (in_interp_arrow x H0 H2).
        simpl in H1.
        intuition.
Qed.

Lemma plus_well_def (t:type) : Plus_well_def t.
Proof.
  exact (proj1 (prop_2 t)).
Qed.

Lemma compare_compat_plus (t:type) : Compare_compat_plus t.
Proof.
  exact (proj2 (prop_2 t)).
Qed.

(* Todo: realy necessary ? *)
Require Import Coq.Logic.FunctionalExtensionality.

(* Prop 3 *)
Lemma plus_0_neutral (t:type) : forall v, plus t v 0 = v.
Proof.
  intros.
  induction t.
  - auto.
  - simpl.
    fold tot.
    extensionality x.
    rewrite IHt2.
    easy.
Qed.

Lemma plus_assoc (t:type) : forall v k1 k2, plus t (plus t v k1) k2 = plus t v (k1 + k2).
Proof.
  intros.
  induction t.
  - simpl. lia.
  - simpl.
    fold tot.
    extensionality x.
    rewrite IHt2.
    easy.
Qed.

Lemma compare_plus_H (t:type) : forall v k1 k2, interp t v -> k1 < k2 -> comparet t (plus t v k1) (plus t v k2).
Proof.
  intros.
  induction t.
  - simpl. lia.
  - simpl. fold tot.
    simpl in H.
    destruct H as (H1,_).
    unfold Fun in H1.
    repeat split.
    * unfold Fun.
      intros.
      apply H1 in H.
      apply plus_well_def; easy.
    * unfold Fun.
      intros.
      apply H1 in H.
      apply plus_well_def; easy.
    * intros. exact (IHt2 (v x) (H1 x H)).
Qed.

Fixpoint star t: tot t :=
  match t as t return tot t with
  | Iota => 0
  | Arrow t1 t2 =>
    fun v => plus t2 (star t2) (collapse t1 v) end
with collapse t: tot t -> nat :=
  match t as t return tot t -> nat with
  | Iota => fun n => n
  | Arrow t1 t2 =>
    fun f =>
      collapse t2 (f (star t1)) end.

Lemma prop_4 t:
  (interp t (star t))
  /\ (forall v v',
         interp t v -> interp t v' -> comparet t v v' ->
         collapse t v < collapse t v').
Proof.
  induction t.
  - split.
    + simpl. exact (Full_intro nat 0).
    + intros; simpl; simpl in H1; assumption.
  - destruct IHt1; destruct IHt2.
    split.
    + simpl.
      fold tot.
      split.
      * unfold Fun.
        intros.
        apply plus_well_def.
        assumption.
      * intros.
        specialize H0 with v1 v2.
        apply compare_plus_H.
        exact H1.
        intuition.
    + intros.
      simpl.
      apply H2.
      exact (in_interp_arrow (star t1) H3 H).
      exact (in_interp_arrow (star t1) H4 H).
      simpl in H5.
      intuition.
Qed.

Lemma star_well_def t : interp t (star t).
Proof.
  exact (proj1 (prop_4 t)).
Qed.

Lemma collapse_spec t: forall v v',
    interp t v -> interp t v' -> comparet t v v' ->
    collapse t v < collapse t v'.
Proof.
  exact (proj2 (prop_4 t)).
Qed.

(* Prop 6 *)
Lemma collapse_star t : collapse t (star t) = 0.
Proof.
  induction t.
  - auto.
  - simpl. rewrite IHt1. rewrite plus_0_neutral. assumption.
Qed.

Lemma collapse_plus_compat t: forall v k, collapse t (plus t v k) = collapse t v + k.
Proof.
  intros.
  induction t.
  - auto.
  - simpl.
    exact (IHt2 (v (star t1))).
Qed.

Fixpoint le_t t : tot t -> tot t -> Prop :=
  match t as t return tot t -> tot t -> Prop with
  | Iota => le
  | Arrow t1 t2 =>
    fun f g =>
      let compare_t2 := comparet t2 in
      forall x, In (tot t1) (interp t1) x -> le_t t2 (f x) (g x) end.

Require Import Coq.Relations.Relation_Definitions.

Lemma le_t_refl t : reflexive (tot t) (le_t t).
Proof.
  unfold reflexive.
  induction t.
  - simpl. exact le_refl.
  - intros.
    simpl.
    intros.
    exact (IHt2 (x x0)).
Qed.

Lemma le_t_sym t : symmetric (tot t) (le_t t).
Proof.
  unfold symmetric.

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

Fixpoint interpt (t:type) : Type :=
  match t with
  | Iota => nat
  | Arrow x y => (interpt x) -> (interpt y) end.

Definition Restrict {A B} (f: A -> B) (e1 : Ensemble A) (e2 : Ensemble B):=
  forall x, In A e1 x -> In B e2 (f x).

Fixpoint interp_compare t : interpt t -> interpt t -> Prop :=
  match t with
  | Iota => lt
  | Arrow t1 t2 =>
    fun f g =>
      let compare_t2 := interp_compare t2 in
      let interp_t1 := interp_ens t1 in
      forall x, In (interpt t1) interp_t1 x -> compare_t2 (f x) (g x)
  end
with interp_ens t: Ensemble (interpt t) :=
  match t as t return Ensemble (interpt t) with
  | Iota => Full_set nat
  | Arrow t1 t2 =>
    let compare_t1 := interp_compare t1 in
    let compare_t2 := interp_compare t2 in
    let interp_t1 := interp_ens t1 in
    let interp_t2 := interp_ens t2 in
    fun f : interpt (Arrow t1 t2) =>
      Restrict f interp_t1 interp_t2 /\
      (forall v1 v2, In (interpt t1) (interp_ens t1) v1 ->
                     In (interpt t1) (interp_ens t1) v2 ->
                     compare_t1 v1 v2 -> compare_t2 (f v1) (f v2))
  end.

(* Prop 1 *)
Lemma interp_compare_trans (t:type): forall x y z,
    interp_compare t x y -> interp_compare t y z -> interp_compare t x z.
Proof.
  induction t.
  - exact lt_trans.
  - simpl; intros.
    specialize H with x0.
    specialize H0 with x0.
    specialize IHt2 with (x x0) (y x0) (z x0).
    intuition.
Qed.

Fixpoint plus (t:type) : interpt t -> nat -> interpt t :=
  match t as t return interpt t -> nat -> interpt t with
  | Iota => fun x k => x + k
  | Arrow t1 t2 =>
    fun f k =>
      fun x => plus t2 (f x) k end.

Lemma plus_arr t1 t2 : plus (Arrow t1 t2) = fun f k x => plus t2 (f x) k.
Proof. auto. Qed.

Definition InInterp t := In (interpt t) (interp_ens t).

Require Import Lia.

Lemma prop_2 (t:type) :
  (forall x, InInterp t x -> forall k, InInterp t (plus t x k))
  /\ (forall v1 v2, InInterp t v1 -> InInterp t v2 ->
    interp_compare t v1 v2 -> forall k, interp_compare t (plus t v1 k) (plus t v2 k)).
Proof.
  induction t.
  - split.
    + intros.
      exact (Full_intro nat (x+k)).
    + intros; simpl. unfold interp_compare in H1.
      lia.
  - destruct IHt1.
    destruct IHt2.
    split.
    + intros.
      rewrite plus_arr.
      fold interpt.
      unfold InInterp.
      simpl.
      unfold In at 1.
      unfold InInterp in H3.
      unfold In in H3.
      simpl in H3.
      destruct H3.
      unfold Restrict in H3.
      fold interpt in H3.
      split.
      * unfold Restrict.
        fold interpt.
        intros.
        apply (H3 x0) in H5.
        exact (H1 (x x0) H5 k).
      * intros.
        specialize H2 with (x v1) (x v2) k.
        specialize H4 with v1 v2.
        pose (H31 := H3 v1 H5).
        pose (H32 := H3 v2 H6).
        pose (FH := H4 H5 H6 H7).
        exact (H2 H31 H32 FH).
    + intros; simpl; intros.
      specialize H2 with (v1 x) (v2 x) k.
      unfold InInterp in H3; unfold In in H3; simpl in H3.
      unfold InInterp in H4; unfold In in H4; simpl in H4.
      destruct H3 as (H3,_).
      destruct H4 as (H4,_).
      unfold Restrict in H3; fold interpt in H3.
      unfold Restrict in H4; fold interpt in H4.
      pose (H3x := H3 x H6).
      pose (H4x := H4 x H6).
      simpl in H5.
      specialize H5 with x.
      pose (H66 := H5 H6).
      exact (H2 H3x H4x H66).
Qed.

Lemma plus_well_def (t:type) :
  (forall x, InInterp t x -> forall k, InInterp t (plus t x k)).
Proof.
  exact (proj1 (prop_2 t)).
Qed.

Lemma compare_compat_plus (t:type) :
  (forall v1 v2, InInterp t v1 -> InInterp t v2 ->
    interp_compare t v1 v2 -> forall k, interp_compare t (plus t v1 k) (plus t v2 k)).
Proof.
  exact (proj2 (prop_2 t)).
Qed.

(* Todo: realy necessary ? *)
Require Import Coq.Logic.FunctionalExtensionality.

Lemma plus_0_neutral (t:type) : forall v, plus t v 0 = v.
Proof.
  intros.
  induction t.
  - auto.
  - simpl.
    fold interpt.
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
    fold interpt.
    extensionality x.
    rewrite IHt2.
    easy.
Qed.


Lemma compare_plus_H (t:type) : forall v k1 k2, k1 < k2 -> interp_compare t (plus t v k1) (plus t v k2).
Proof.
  intros.
  induction t.
  - simpl. lia.
  - simpl; intros.
    exact (IHt2 (v x)).
Qed.

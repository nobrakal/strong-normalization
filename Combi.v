Require Import Coq.Structures.Equalities.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.Arith.
Require Import Lia.

Class Ord (A:Type) := cmp : A -> A -> Prop.
Infix "<<" := cmp (at level 70, no associativity).

(* Some order instances *)
(* Comparing functions by their graph *)
Instance ordfun A B `(Ord B) : Ord (A->B) :=
  fun f g => forall a, f a << g a.
(* The order on a sig is the order on the object *)
Instance ordsig A (P:A->Prop) `(Ord A) : Ord {a:A|P a} :=
  fun a a' => proj1_sig a << proj1_sig a'.

Definition Incr {A}{B}`(Ord A)`(Ord B) (f:A->B) :=
  forall a a', a << a' -> f a << f a'.

Inductive typ :=
| Iota
| Arrow (t1:typ) (t2:typ).

(* A record to hold both definitions, needed due to mutual recursion of the interpretation *)
Record pack := Pack { dom :> Type; ord : Ord dom }.

(* The interpretation of a type *)
Fixpoint interp (t:typ) : pack :=
  match t with
  | Iota => Pack nat lt
  | Arrow t1 t2 =>
    Pack { f : dom (interp t1) -> dom (interp t2) | Incr (ord (interp t1)) (ord (interp t2)) f }
         (ordsig _ _ (ordfun  _ _ (ord (interp t2))))
  end.

Instance ordpack (p:pack) : Ord p := p.(ord).

(* The order of the interpretation is transitive *)
Instance interp_ord_trans t : Transitive (ordpack (interp t)).
Proof.
  induction t.
  - intuition.
  - unfold ordpack, ord in *.
    simpl.
    unfold ordsig, Transitive, cmp, ordfun.
    intros.
    unfold Transitive in IHt2.
    apply IHt2 with (y:=proj1_sig y a); firstorder.
Qed.

(* A record to hold both definitions, needed to define plus on type *)
Record ppack t :=
  PPack { op : interp t -> nat -> interp t; plus_incr : forall x y k, x << y -> op x k << op y k}.

Program Fixpoint plust_pack t : ppack t :=
  match t as t return  ppack t with
  | Iota => PPack Iota (fun f k => f + k) _
  | Arrow t1 t2 =>
    PPack
      (Arrow t1 t2)
      (fun f k => exist _ (fun v => op t2 (plust_pack t2) (proj1_sig f v) k) _)
    _
  end.

Obligation 1.
unfold cmp in *. intuition.
Defined.

Obligation 2.
unfold Incr.
firstorder.
Defined.

Obligation 3.
unfold cmp, ordsig, proj1_sig, cmp, ordfun in *.
intros.
destruct (plust_pack t2).
unfold op.
firstorder.
Defined.

Definition plust {t} : interp t -> nat -> interp t := op t (plust_pack t).

Infix "+_" := plust (at level 50, no associativity).

(* Use equality of nat on Iota, and equality of images otherwise *)
Fixpoint eqt {t} : interp t -> interp t -> Prop :=
  match t with
  | Iota => fun x y => x = y
  | Arrow t1 t2 => fun f g => forall x, eqt (proj1_sig f x) (proj1_sig g x)
  end.

Infix "==" := eqt (at level 60, no associativity).

Instance eqtequiv t : Equivalence (@eqt t).
Proof.
  induction t.
  - split; simpl; intuition.
    unfold Transitive.
    intros.
    rewrite H0 in H. easy.
  - destruct IHt2; split; simpl; fold interp.
    * firstorder.
    * unfold Symmetric in *.
      intros.
      apply Equivalence_Symmetric.
      easy.
    * unfold Transitive in *.
      intros.
      apply Equivalence_Transitive with (y := proj1_sig y x0); easy.
Qed.

Lemma plust_0 t : forall (v:interp t), v +_ 0 == v.
Proof.
  intros.
  induction t; simpl; fold interp.
  - easy.
  - intros.
    apply IHt2.
Qed.

Lemma plust_assoc t : forall (v:interp t) k k', (v +_ k) +_ k' == v +_ (k + k').
Proof.
  intros.
  induction t; simpl; fold interp.
  - symmetry.
    apply plus_assoc.
  - intros.
    apply IHt2.
Qed.

Lemma plust_monotonic t : forall (v:interp t) k k', k < k' -> v +_ k << v +_ k'.
Proof.
  intros.
  induction t; simpl; fold interp; unfold cmp.
  - intuition.
  - unfold ordsig, cmp, ordfun.
    intros.
    apply IHt2.
Qed.

(* A record to well define collapse and define. *)
Record spack t :=
  SPack
    { witness' : interp t
      ; collapse' : interp t -> nat
      ; collapse'_ok : forall v v', v << v' -> collapse' v < collapse' v'}.

Program Fixpoint star_pack t : spack t :=
  match t with
  | Iota => SPack Iota 0 (fun n => n) _
  | Arrow t1 t2 => SPack
      (Arrow t1 t2)
      (exist _ (fun v => witness' t2 (star_pack t2) +_ collapse' t1 (star_pack t1) v) _)
      (fun f => collapse' t2 (star_pack t2) ((proj1_sig f (witness' t1 (star_pack t1)))))
      _
  end.

Obligation 2.
  fold interp.
  unfold Incr.
  intros.
  apply plust_monotonic.
  apply collapse'_ok1.
  easy.
Defined.

Definition witness t := witness' t (star_pack t).
Definition collapse {t} := collapse' t (star_pack t).

(* We need a witness to prove that the order of the interpretation is really an order. *)
Instance interp_ord_strictord t : StrictOrder (ord (interp t)).
Proof.
  induction t.
  - intuition.
  - split.
    * destruct IHt2.
      unfold Irreflexive, complement, Reflexive in *; simpl; unfold ordsig, ordfun, Incr.
      intros.
      unfold cmp in H.
      specialize H with (witness t1).
      apply StrictOrder_Irreflexive in H.
      easy.
    * apply interp_ord_trans.
Qed.

(* This allows to rewrite collapse with eqt *)
Instance collapse_proper : forall t, Proper (@eqt t ==> eq) (@collapse t).
Proof.
  intros.
  induction t.
  - easy.
  - simpl_relation.
    unfold collapse.
    simpl.
    unfold eqt in H.
    specialize H with (witness t1).
    apply IHt2 in H.
    easy.
Qed.

Lemma collapse_witness t : collapse (witness t) = 0.
Proof.
  induction t.
  - easy.
  - unfold collapse, witness in *.
    simpl.
    rewrite IHt1.
    rewrite plust_0.
    assumption.
Qed.

Lemma collapse_linear t: forall (v:interp t) k, collapse (v +_ k) = collapse v + k.
Proof.
  intros.
  induction t.
  - easy.
  - unfold collapse, plust in *.
    simpl.
    rewrite IHt2.
    easy.
Qed.

Fixpoint le_t {t} : Ord (interp t) :=
  match t as t return Ord (interp t) with
  | Iota => le
  | Arrow t1 t2 => ordsig _ _ (ordfun _ _ (@le_t t2)) end.

Infix "<<=" := le_t (at level 70, no associativity).

Instance le_t_preorder t : PreOrder (@le_t t).
Proof.
  induction t.
  - intuition.
  - split.
    * easy.
    * unfold Transitive.
      unfold le_t, ordsig, ordfun, cmp; fold (@le_t t2).
      intros x y z Hxy Hyz a.
      destruct IHt2.
      unfold Transitive in PreOrder_Transitive.
      apply PreOrder_Transitive with (y := proj1_sig y a).
      exact (Hxy a).
      exact (Hyz a).
Qed.

Instance le_t_antisym t : Antisymmetric (interp t) eqt (@le_t t).
Proof.
  unfold Antisymmetric.
  induction t; simpl; fold interp.
  - intuition.
  - intros.
    apply IHt2.
    apply H.
    apply H0.
Qed.

Lemma trans_cmp_le t: forall x y z : interp t, x << y -> y <<= z -> x <<= z.
Proof.
  induction t; unfold cmp, le_t; simpl; fold interp; intros.
  - lia.
  - unfold ordsig,cmp,ordfun in *.
    intros.
    apply IHt2 with (y:= proj1_sig y a); firstorder.
Qed.

Lemma trans_le_cmp t: forall x y z : interp t, x <<= y -> y << z -> x <<= z.
Proof.
  induction t; unfold cmp, le_t; simpl; fold interp; intros.
  - lia.
  - unfold ordsig,cmp,ordfun in *.
    intros.
    apply IHt2 with (y:= proj1_sig y a); firstorder.
Qed.

Lemma collapse_monotonic t: forall x y : interp t, x <<= y -> collapse x <= collapse y.
Proof.
  intros.
  induction t.
  - easy.
  - unfold collapse.
    simpl.
    apply IHt2.
    apply H.
Qed.

Lemma plust_monotonic_le_t t : forall (v v' : interp t) k k', v <<= v' -> k < k' -> v +_ k <<= v' +_ k' .
Proof.
  induction t; unfold cmp, le_t, plust; simpl; fold interp; intros.
  - lia.
  - unfold ordsig,cmp,ordfun in *.
    intros.
    specialize H with a.
    apply IHt2; easy.
Qed.

Lemma charac_cmp_le_t t : forall x y: interp t, x << y <-> x +_ 1 <<= y.
Proof.
  induction t; unfold cmp, le_t, plust; simpl; fold interp; intros.
  - lia.
  - unfold ordsig,cmp,ordfun in *.
    simpl.
    split; intros H a; specialize H with a; apply IHt2; apply H.
Qed.

Inductive typ :=
| Iota
| Arrow (t1:typ) (t2:typ).

Class Ord (A:Type) := cmp : A -> A -> Prop.
Infix "<<" := cmp (at level 70, no associativity).

(* Les quelques constructions d'ordres qui serviront après *)
Instance ordnat : Ord nat := lt.

Instance ordfun A B `(Ord B) : Ord (A->B) :=
 fun f g => forall a, f a << g a.
Instance ordsig A (P:A->Prop)`(Ord A) : Ord {a:A|P a} :=
 fun a a' => proj1_sig a << proj1_sig a'.

Definition Incr {A}{B}`(Ord A)`(Ord B) (f:A->B) :=
 forall a a', a << a' -> f a << f a'.

Record pack := Pack { dom :> Type; ord : Ord dom }.

(* NB: La projection dom peut être implicite (cf le :> ci-dessus)
   donc un pack peut être utilisé à la place d'un type Coq *)

Fixpoint interp (t:typ) : pack :=
 match t with
 | Iota => Pack nat _
 | Arrow t1 t2 =>
   Pack { f : dom (interp t1) -> dom (interp t2) | Incr (ord (interp t1)) (ord (interp t2)) f }
        (ordsig _ _ (ordfun  _ _ (ord (interp t2))))
 end.

(* Evidemment, le type dans un pack est ordonné *)
Instance ordpack (p:pack) : Ord p := p.(ord).

Require Import Coq.Arith.Arith.
Require Import Coq.Classes.RelationClasses.

Instance odrtrans t : Transitive (ordpack (interp t)).
Proof.
  induction t.
  - intuition.
  - unfold ordpack in *.
    unfold ord.
    simpl.
    unfold ordsig, Transitive, cmp, ordfun.
    intros.
    unfold Transitive in IHt2.
    apply IHt2 with (y:=proj1_sig y a); firstorder.
Qed.

Record ppack t := PPack { op : interp t -> nat -> interp t; plus_incr : forall x y k, x << y -> op x k << op y k}.

Program Fixpoint plust_pack t : ppack t :=
  match t as t return  ppack t with
  | Iota => PPack Iota (fun f k => f + k) _
  | Arrow t1 t2 => PPack
    (Arrow t1 t2)
    (fun f k => exist _ (fun v => op t2 (plust_pack t2) (proj1_sig f v) k) _)
    _
  end.

Obligation 1.
unfold cmp, ordnat in *. intuition.
Defined.

Obligation 2.
fold interp.
unfold Incr.
firstorder.
Defined.

Obligation 3.
fold interp.
unfold cmp, ordsig, proj1_sig, cmp, ordfun in *.
intros.
destruct (plust_pack t2).
unfold op.
firstorder.
Defined.

Definition plust {t} : interp t -> nat -> interp t := op t (plust_pack t).

Infix "+_" := plust (at level 50, no associativity).

(* Use equality of nat on Iota, and functional extensionality otherwise *)
Fixpoint eqt {t} : interp t -> interp t -> Prop :=
  match t with
  | Iota => fun x y => x = y
  | Arrow t1 t2 => fun f g => forall x, eqt (proj1_sig f x) (proj1_sig g x)
  end.

Infix "==" := eqt (at level 60, no associativity).

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
  - intros. apply IHt2.
Qed.

Lemma plust_monotonic t : forall (v:interp t) k k', k < k' -> v +_ k << v +_ k'.
Proof.
  intros.
  induction t; simpl; fold interp; unfold cmp.
  - unfold ordnat.
    intuition.
  - unfold ordsig, cmp, ordfun.
    intros.
    apply IHt2.
Qed.

Record spack t :=
  SPack
    { sbelow : interp t
      ; sabove : interp t -> nat
      ; sabove_ok : forall v v', v << v' -> sabove v < sabove v'}.

Program Fixpoint star_pack t : spack t :=
  match t with
  | Iota => SPack Iota 0 (fun n => n) _
  | Arrow t1 t2 => SPack
      (Arrow t1 t2)
      (exist _ (fun v => sbelow t2 (star_pack t2) +_ sabove t1 (star_pack t1) v) _)
      (fun f => sabove t2 (star_pack t2) ((proj1_sig f (sbelow t1 (star_pack t1)))))
      _
  end.

Obligation 2.
  fold interp.
  unfold Incr.
  intros.
  apply plust_monotonic.
  apply sabove_ok1.
  easy.
Defined.

Definition star_below t := sbelow t (star_pack t).
Definition star_above t := sabove t (star_pack t).

Require Import Coq.Classes.Morphisms.

Instance star_above_proper : forall t, Proper (@eqt t ==> eq) (star_above t).
Proof.
  intros.
  induction t.
  - easy.
  - simpl_relation.
    unfold star_above.
    simpl.
    unfold eqt in H.
    specialize H with (star_below t1).
    apply IHt2 in H.
    easy.
Qed.

Lemma star_above_below t : star_above t (star_below t) = 0.
Proof.
  induction t.
  - easy.
  - unfold star_above, star_below in *.
    simpl.
    rewrite IHt1.
    rewrite plust_0.
    assumption.
Qed.

Lemma star_above_linear t: forall v k, star_above t (v +_ k) = star_above t v + k.
Proof.
  intros.
  induction t.
  - easy.
  - unfold star_above, plust in *.
    simpl.
    rewrite IHt2.
    easy.
Qed.

Fixpoint le_t {t} : interp t -> interp t -> Prop :=
  match t as t return interp t -> interp t -> Prop with
  | Iota => fun x y => x <= y
  | Arrow t1 t2 => fun f g => forall v, le_t (proj1_sig f v) (proj1_sig g v) end. (* TODO facto *)

Infix "<<=" := le_t (at level 70, no associativity).

Require Import Lia.

Lemma trans_cmp_le t: forall x y z : interp t, x << y -> y <<= z -> x <<= z.
Proof.
  induction t; unfold cmp, le_t; simpl; fold interp; intros.
  - unfold ordnat in H. lia.
  - unfold ordsig in H.
    specialize H0 with v.
    apply IHt2 with (y:= proj1_sig y v).
    easy.
    easy.
Qed.

Lemma trans_le_cmp t: forall x y z : interp t, x <<= y -> y << z -> x <<= z.
Proof.
  induction t; unfold cmp, le_t; simpl; fold interp; intros.
  - unfold ordnat in H0. lia.
  - unfold ordsig in H0.
    specialize H with v.
    apply IHt2 with (y:= proj1_sig y v).
    easy.
    easy.
Qed.

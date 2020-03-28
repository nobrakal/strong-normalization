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
    unfold ordsig.
    unfold Transitive.
    unfold cmp.
    unfold ordfun.
    intros.
    unfold Transitive in IHt2.
    exact (IHt2 (proj1_sig x a) (proj1_sig y a) (proj1_sig z a) (H a) (H0 a)).
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
Fixpoint eq {t} : interp t -> interp t -> Prop :=
  match t with
  | Iota => fun x y => x = y
  | Arrow t1 t2 => fun f g => forall x, eq (proj1_sig f x) (proj1_sig g x)
  end.

Infix "==" := eq (at level 60, no associativity).

Lemma plus_0 t : forall (v:interp t), v +_ 0 == v.
Proof.
  intros.
  induction t; simpl; fold interp.
  - easy.
  - intros.
    apply IHt2.
Qed.

Lemma plus_assoc t : forall (v:interp t) k k', (v +_ k) +_ k' == v +_ (k + k').
Proof.
  intros.
  induction t; simpl; fold interp.
  - symmetry.
    apply plus_assoc.
  - intros. apply IHt2.
Qed.

Lemma plus_monotonic t : forall (v:interp t) k k', k < k' -> v +_ k << v +_ k'.
Proof.
  intros.
  induction t; simpl; fold interp; unfold cmp.
  - unfold ordnat.
    intuition.
  - unfold ordsig, cmp, ordfun.
    intros.
    apply IHt2.
Qed.

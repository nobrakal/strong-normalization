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

Fixpoint plus t : dom (interp t) -> nat -> dom (interp t) :=
  match t as t return dom (interp t) -> nat -> dom (interp t)  with
  | Iota => fun x y => x + y
  | Arrow t1 t2 =>
    fun f k => exist _ (fun v => plus t2 (proj1_sig f (proj1_sig v)) k)
  end.

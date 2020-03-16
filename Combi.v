Require Import Coq.Arith.Arith_base.

(* Inductive lambda {A : Set} : type -> Set :=
| Var (t:type) (x:A) : lambda t
| Lam (t1:type) (x:A) {t2:type} (b:lambda t2) : lambda (Arrow t1 t2)
| App {t1 t2:type} (x:lambda (Arrow t1 t2)) (y:lambda t1) : lambda t2. *)

(* Fixpoint tot t : Type :=
  match t with
  | Iota => nat
  | Arrow t1 t2 => (tot t1) -> (tot t2) end. *)

Definition lt' : {_: nat | True} -> {_:nat | True} -> Prop :=
  fun x y =>
  match x,y with
  | exist _ x _, exist _ y _ => lt x y end.

Inductive Interp : forall (T:Type) (P:T -> Prop), (sig P -> sig P -> Prop) -> Prop :=
| Iota : Interp nat (fun _ => True) lt'
| Arrow {t1 t2} {int1 int2} {c1 c2} (x:Interp t1 int1 c1) (y:Interp t2 int2 c2) :
    Interp (sig int1 -> sig int2) (fun f => forall v v', c1 v v' -> c2 (f v) (f v'))
           (fun f g => forall v, c2 (proj1_sig f v) (proj1_sig g v)).

Definition tot {T P cmp} (t:Interp T P cmp) : Type := T.
Definition interp {T P cmp} (t:Interp T P cmp) : T -> Prop := P.
Definition cmp {T P cmp} (t:Interp T P cmp) : sig P -> sig P -> Prop := cmp.

Require Import Coq.Relations.Relation_Definitions.

Lemma lt'_spec : forall x y, lt' x y <-> lt (proj1_sig x) (proj1_sig y).
Proof.
  intros.
  destruct x.
  destruct y.
  intuition.
Qed.

Lemma cmp_trans {T P C} (t:Interp T P C) : transitive (sig P) C.
Proof.
  unfold transitive.
  intros.
  induction t.
  - destruct x. destruct y. destruct z.
    simpl; simpl in H; simpl in H0.
    exact (lt_trans x x0 x1 H H0).
  - intros.
    apply IHt2 with (y := (proj1_sig y v)).
    intuition. intuition.
Qed.

Fixpoint plus {T P C} (t:Interp T P C) : sig P -> nat -> sig P :=
  match t with
  | Iota => fun x k => exist (fun _ => True) (proj1_sig x + k) I
  | Arrow x y =>
    fun f k =>
      let f' := fun v => plus y (proj1_sig f v) k in
      sexist (fun f => forall v v', (cmp x) v v' -> cmp y (f v) (f v'))
  end.

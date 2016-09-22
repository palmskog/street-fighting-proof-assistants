Require Import List.
Require Import String.
Open Scope string_scope.

Require Import StructTactics.

Inductive expr : Set :=
| Var : string -> expr
| App : expr -> expr -> expr
| Lam : string -> expr -> expr.

Coercion Var : string >-> expr.

Notation "X @ Y" := (App X Y) (at level 49).
Notation "\ X , Y" := (Lam X Y) (at level 50).

Check (\"x", \"y", "x").
Check (\"x", \"y", "y").
Check ((\"x", "x" @ "x") @ (\"x", "x" @ "x")).

(** e1[e2/x] *)
Fixpoint subst (e : expr) (from : string) (to : expr)  : expr :=
  match e with
  | Var x => if string_dec from x then to else e
  | App e1 e2 => App (subst e1 from to) (subst e2 from to)
  | Lam x e => if string_dec from x then e else Lam x (subst e from to)
  end.

(**
Call By Name
<<
       e1 --> e1'
  ---------------------
    e1 e2 --> e1' e2

  -----------------------------
    (\x. e1) e2 --> e1[e2/x]
>>
*)

Inductive step_cbn : expr -> expr -> Prop :=
| CBN_crunch:
    forall e1 e1' e2,
      step_cbn e1 e1' ->
      step_cbn (App e1 e2) (App e1' e2)
| CBN_subst:
    forall x e1 e2,
      step_cbn (App (Lam x e1) e2) (subst e1 x e2).

Notation "e1 ==> e2" := (step_cbn e1 e2) (at level 51).

Lemma step_cbn_det:
  forall e e1,
  e ==> e1 ->
  forall e2,
  e ==> e2 ->
  e1 = e2.
Proof.
  induction 1; intros.
  - invc H0.
    + f_equal. apply IHstep_cbn; auto.
    + invc H.
  - invc H.
    + invc H3.
    + reflexivity.
Qed.

(**
Call By Value
<<

v ::= \ x . e

       e1 --> e1'
  ---------------------
    e1 e2 --> e1' e2

       e2 --> e2'
  ---------------------
    v e2 --> v e2'

  -----------------------------
    (\x. e1) v --> e1[v/x]
>>
*)

Inductive value : expr -> Prop :=
| VLam :
    forall x e,
      value (Lam x e).

Inductive step_cbv : expr -> expr -> Prop :=
| CBV_crunch_l:
    forall e1 e1' e2,
      step_cbv e1 e1' ->
      step_cbv (App e1 e2) (App e1' e2)
| CBV_crunch_r:
    forall v e2 e2',
      value v ->
      step_cbv e2 e2' ->
      step_cbv (App v e2) (App v e2')
| CBV_subst:
    forall x e1 v,
      value v ->
      step_cbv (App (Lam x e1) v) (subst e1 x v).

Notation "e1 --> e2" := (step_cbv e1 e2) (at level 51).

Inductive star (step: expr -> expr -> Prop) :
  expr -> expr -> Prop :=
| star_refl:
    forall s,
      star step s s
| star_step:
    forall s1 s2 s3,
      step s1 s2 ->
      star step s2 s3 ->
      star step s1 s3.

Notation "e1 ==>* e2" := (star step_cbn e1 e2) (at level 51).
Notation "e1 -->* e2" := (star step_cbv e1 e2) (at level 51).

Lemma cbv_cbn_can_step:
  forall e1 e2,
    e1 --> e2 ->
    exists e3, e1 ==> e3.
Proof.
  induction 1.
  - destruct IHstep_cbv as [e3 He3].
    exists (e3 @ e2). constructor; auto.
  - inv H. eexists. apply CBN_subst.
  - eexists. apply CBN_subst.
Qed.

(** is the other way true? *)

(** * Church Encodings *)

(** generally assume no free vars! *)

Definition lcTrue :=
  \"x", \"y", "x".

Definition lcFalse :=
  \"x", \"y", "y".

Definition lcCond (c t f: expr) :=
  c @ t @ f.

(** <<

lcCond lcTrue e1 e2 -->* e1

>> *)

Definition lcNot :=
  \"b", "b" @ lcFalse @ lcTrue.

Definition lcAnd :=
  \"a", \"b", "a" @ "b" @ lcFalse.

Definition lcOr :=
  \"a", \"b", "a" @ lcTrue @ "b".

Definition lcMkPair :=
  \"x", \"y",
    (\"s", "s" @ "x" @ "y").

Definition lcFst :=
  \"p", "p" @ (\"x", \"y", "x").

Definition lcSnd :=
  \"p", "p" @ (\"x", \"y", "y").

(** <<

lcSnd (lcFst (lcMkPair (lcMkPair e1 e2) e3)) -->* e2

lcFst = \"p", "p" @ lcTrue

lcSnd = \"p", "p" @ lcFalse

>> *)

Definition lcNil :=
  lcMkPair @ lcFalse @ lcFalse.

Definition lcCons :=
  \"h", \"t", lcMkPair @ lcTrue @ (lcMkPair @ "h" @ "t").

Definition lcIsEmpty :=
  lcFst.

Definition lcHead :=
  \"l", lcFst @ (lcSnd @ "l").

Definition lcTail :=
  \"l", lcSnd @ (lcSnd @ "l").

(** <<

Note that lcTail lcNil does some weird stuff,
but then so does dereferencing null in C or
following null.next() in Java.

>> *)

Definition lc0 :=
  \"s", \"z", "z".

Definition lc1 :=
  \"s", \"z", "s" @ "z".

Definition lc2 :=
  \"s", \"z", "s" @ ("s" @ "z").

Definition lc3 :=
  \"s", \"z", "s" @ ("s" @ ("s" @ "z")).

Definition lc4 :=
  \"s", \"z", "s" @ ("s" @ ("s" @ ("s" @ "z"))).

(** <<

Number "n" composes first arg with itself n times,
starting with the second arg.

>> *)

Definition lcSucc :=
  \"n", \"s", \"z", "s" @ ("n" @ "s" @ "z").

Definition lcAdd :=
  \"n", \"m",
    (\"s", \"z", "n" @ lcSucc @ "m").

Definition lcMul :=
  \"n", \"m",
    (\"s", \"z", "n" @ (lcAdd @ "m") @ lc0).

Definition lcIsZero :=
  \"n",
    "n" @ (\"x", lcFalse) @ lcTrue.

(** <<
  Can keep going to get pred, minus, div, is_equal, ...
>> *)

Definition lcPred :=
  (** TODO : define pred on Church numerals *)
  "x".

(** only works for CBN! *)
Definition lcY :=
  \"f",
    (\"x", "f" @ ("x" @ "x")) @
    (\"x", "f" @ ("x" @ "x")).

(** <<

Y F
  -->* (\f, (\x, f (x x)) (\x, f (x x))) F
  -->* (\x, F (x x)) (\x, F (x x))
  -->* F ((\x, F (x x)) (\x, F (x x)))
  -->* F (Y F)

>> *)

Definition lcFactAux :=
  \"f", \"n",
  lcCond (lcIsZero @ "n")
         lc1
         (lcMul @ "n" @ ("f" @ (lcPred @ "n"))).

Definition lcFact :=
  lcY @ lcFactAux.

(** <<

lcFact 3 -->* 6

>> *)

Definition lcLet v e1 e2 :=
  (\v, e2) @ e1.

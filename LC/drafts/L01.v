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

Set Implicit Arguments.

Require Import List.
Require Import Program.
Require Import FunctionalExtensionality.

Ltac rewrites E :=
  (intros; simpl; try rewrite E;
    repeat (match goal with | [H:context [eq _ _] |- _] => rewrite H end);
      auto).

Ltac ExtVar :=
  match goal with
    [ |- eq ?X ?Y ] =>
    (apply (@functional_extensionality_dep _ _ X Y);
      let t := fresh "t" in intro t;
        apply functional_extensionality;
          let v := fresh "v" in intro v;
            dependent destruction v; auto)
  end.

Section Terms.

Inductive type : Type :=
| base : type
| arr  : type -> type -> type.

Inductive variable : list type -> type -> Type :=
| varZ : forall l t, variable (t::l) t
| varS : forall l t t', variable l t -> variable (t'::l) t.

Inductive term G : type -> Type :=
| var : forall t,
  variable G t ->
  term G t
| lam : forall t1 t2,
  term (t1::G) t2 ->
  term G (arr t1 t2)
| app : forall t1 t2,
  term G (arr t1 t2) ->
  term G t1 ->
  term G t2.

End Terms.

Section Sem.

Hypothesis Base : Set.

Fixpoint ty_sem (t : type) : Set :=
  match t with
    | base      => Base
    | arr t1 t2 => ty_sem t1 -> ty_sem t2
  end.

Fixpoint ctxt_sem (G : list type) : Set :=
  match G with
    | nil    => unit
    | t :: G => (ty_sem t * ctxt_sem G)%type
  end.

Fixpoint var_sem (G : list type) (ty : type) (v : variable G ty) : ctxt_sem G -> ty_sem ty :=
  match v with
    | varZ _ _     => fun env => fst env
    | varS _ _ _ v => fun env => var_sem v (snd env)
  end.

Fixpoint tm_sem G ty (t : term G ty) : ctxt_sem G -> ty_sem ty :=
  match t with
    | var _ v =>
      fun env => var_sem v env
    | lam _ _ t =>
      fun env => fun x => tm_sem t (x, env)
    | app _ _ t1 t2 =>
      fun env => (tm_sem t1 env) (tm_sem t2 env)
  end.

Hypothesis P : Base -> Set.

Fixpoint ty_pred (ty : type) : ty_sem ty -> Set :=
  match ty with
    | base      => fun x => P x
    | arr t1 t2 => fun f => forall a, ty_pred t1 a -> ty_pred t2 (f a)
  end.

Fixpoint ctxt_pred (G : list type) : ctxt_sem G -> Set :=
  match G with
    | nil     => fun env => unit
    | ty :: G => fun env => (ty_pred ty (fst env) * ctxt_pred G (snd env))%type
  end.

Lemma fundamental :
  forall G ty (t : term G ty) env,
    ctxt_pred G env -> ty_pred ty (tm_sem t env).
intros G ty t. induction t.
 (* var *)
 induction v; simpl; intros.
  destruct H. assumption.
  apply IHv. destruct H. assumption.
 (* lam *)
 simpl. intros. apply IHt. split; assumption.
 (* app *)
 simpl. intros. apply IHt1.
  apply H.
  apply IHt2. apply H.
Save.
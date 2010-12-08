Definition lt : nat -> nat -> Set.
intros x.
induction x.
 intro y. destruct y.
  exact False.
  exact True.
 intros y. destruct y.
  exact False.
  apply IHx. apply y.
Defined.

Lemma trans : forall a b c,
  lt a b -> lt b c -> lt a c.
induction a.
 destruct b.
  contradiction.
  destruct c.
   contradiction.
   trivial.
 destruct b.
  contradiction.
  destruct c.
   contradiction.
   simpl. apply IHa.
Save.

Lemma foo : forall a b c,
  lt a b -> lt b (S c) -> lt a c.
intros a. induction a.
 destruct b; destruct c; try contradiction.
  destruct b; contradiction.
  trivial.
 destruct b; destruct c; try contradiction.
  destruct b; contradiction.
  intuition (simpl; eauto).
Save.

Print foo.
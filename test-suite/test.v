Require Setoid.
Require Import Completion.Completion.

Variable A : Set.
Variable op : A -> A -> A.
Axiom ax : forall a b c, op (op a b) (op b c) = b.

Complete ax : cgroupoid sig op.

Goal forall a b c, op (op (op a b) (op b c)) (op (op b c) c) = op b c.
intros.
autorewrite with cgroupoid.
reflexivity.
Qed.

Variable G : Set.
Variable mul : G -> G -> G.
Variable e : G.
Variable i : G -> G.
Axiom assoc : forall a b c, mul (mul a b) c = mul a (mul b c).
Axiom inv : forall a, mul (i a) a = e.
Axiom iden : forall a, mul e a = a.
Axiom comm : forall a b, mul a b = mul b a.

Complete inv iden, AC (mul, assoc, comm) : group sig e mul i.

Goal forall a b c, mul (mul b c) (mul a (mul (i c) b)) = mul a (mul b b).
intros.
autorewrite_ac group sig e mul i.
reflexivity.
Qed.

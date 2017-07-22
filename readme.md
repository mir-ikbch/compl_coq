# ComplCoq   Knuth-Bendix Completion on Coq Hint Rewrite DBs

# Build
```
  $ export COQBIN=your_path_to_coq_bin
  $ export COQLIB=your_path_to_coq_lib
  $ coq_makefile -f Make -o Makefile
  $ make
  $ make install
```

# Example
```
  Coq < Parameter A : Set.
  Coq < Parameter op : A -> A -> A.
  Coq < Axiom ax : forall a b c, op (op a b) (op b c) = b.
  Coq < Complete ax : dbname sigs op.
  Coq < Print Rewrite HintDb dbname.

  Coq < Parameter G : Set.
  Coq < Parameter e : G.
  Coq < Parameter mul : G -> G -> G.
  Coq < Parameter i : G -> G.
  Coq < Axiom assoc : forall x y z, mul (mul x y) z = mul x (mul y z).
  Coq < Axiom inv : forall x, mul (i x) x = e.
  Coq < Axiom iden : forall x, mul e x = x.
  Coq < Axiom comm : forall x y, mul x y = mul y x.
  Coq < Complete inv iden, AC (mul, assoc, comm) : dbname sigs e mul i.
  Coq < Print Rewrite HintDb dbname2.
```

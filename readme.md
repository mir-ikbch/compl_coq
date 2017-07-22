# Build
```
  $ export COQSOURCEBIN=your_path_to_coq_source/bin/
  $ export COQSOURCELIB=your_path_to_coq_source/
  $ coq_makefile -f Make -o Makefile
  $ make
```
In ``tcsh``:
```
  $ setenv PATH your_path_to_installed_coq:$PATH
  $ setenv COQSOURCEBIN your_path_to_coq_source/bin/
  $ setenv COQSOURCELIB your_path_to_coq_source/
  $ coq_makefile -f Make | make -f -
```
# Debug
```
  $ $COQSOURCEBIN/coqtop.byte
  Coq < Add LoadPath "path_to_compl_coq" as Completion.
  Coq < Add ML Path "path_to_compl_coq/src".
  Coq < Require Import Completion.Completion.
  Coq < Drop.
  # #use "include";;
```
Alternatively,
```
  $ coqtop.byte -R theories/ Completion -I ./src -require Completion.Completion
  Coq < Drop.
  # #use "include";;
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

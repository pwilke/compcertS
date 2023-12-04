Definition print {A B: Type} (f: A -> unit) (a: A) (b: B) : B :=
  let unused := f a in
  b.

Notation "[ A  a ] ; B" := (print A a B) (no associativity,
                                           at level 200,
                                           A at level 0,
                                           B at level 100,
                                           a at level 200).

Extract Constant print =>
"fun (f: 'a -> unit) (a: 'a) (b: 'b) -> f a; b".
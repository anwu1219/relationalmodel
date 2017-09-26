Require Import Hahn.
From RelationAlgebra Require Import kat normalisation rewriting kat_tac rel.
Set Implicit Arguments.


Canonical Structure bool_algebra: lattice.ops := {|
  car := (nat -> Prop);
  leq := set_subset;
  weq := set_equiv;
  cup := fun s s' => set_union s s';
  cap := fun s s' => set_inter s s';
  bot := set_empty;
  top := set_full;
  neg := fun s => set_compl s;
|}.


Canonical Structure partial_order: lattice.ops := {|
  car := relation nat;
  leq := inclusion;
  weq := same_relation;
  cup := fun r r' => union r r';
  cap := fun r r' => inter_rel r r';
  bot := ∅₂;
  top := fun _ _ => True;
  neg := fun r => (fun _ _ => True) \ r 
|}.


 
Canonical Structure kleene_algebra: monoid.ops := {|
  ob := relation nat;
  mor n m := partial_order;
  dot n m p := fun r r' => seq r r';
  one n := fun x y => x = y;
  itr n := fun r => clos_trans r;
  str n := fun r => clos_refl_trans r;
  cnv n m := fun r => transp r;
  ldv n m p := fun x y => ld x y;
  rdv n m p := fun x y => rd x y
|}.


Canonical Structure kleene_algebra_with_test: kat.ops := {|
  kar := kleene_algebra;
  tst n := bool_algebra;
  inj n := fun x => eqv_rel x
|}.


Notation prog' := (kleene_algebra_with_test tt tt).
Notation test := (@tst kleene_algebra_with_test tt).

Local Ltac u :=
  unfold set_union, set_inter, set_minus, set_compl,
         set_equiv, set_subset, set_empty, set_full,
         reflexive, transitive in *;
  ins; try solve [tauto | firstorder].


(* Boolean algebra is a lattice *)
Instance expr_lattice_laws: lattice.laws BL bool_algebra.
Proof.
  constructor; try eauto; ins; u.
Qed.

(* Kleene algebra is a monoid *)
Instance prog_monoid_laws: monoid.laws BKA kleene_algebra. 
Proof.
  constructor; try ins; eauto.
  - admit.
  - 
  
Qed.


Instance prog_kat_laws: kat.laws kleene_algebra_with_test.
Proof.
  constructor; simpl; eauto with typeclass_instances. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit. 
Qed.




Lemma r_seq_in_r_trans_clos (r: relation nat): (r ⨾  r) ⊆ r ⁺.
Proof. 

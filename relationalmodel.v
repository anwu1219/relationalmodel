Require Import Hahn.
From RelationAlgebra Require Import kat normalisation rewriting kat_tac rel.
Set Implicit Arguments.


Canonical Structure bool_algebra (A: Type): lattice.ops := {|
  car := (A -> Prop);
  leq := set_subset;
  weq := set_equiv;
  cup := set_union (A:=A);
  cap := @set_inter _;
  bot := set_empty;
  top := set_full;
  neg := @set_compl _;
|}.


Canonical Structure partial_order (A: Type): lattice.ops := {|
  car := relation A;
  leq := inclusion;
  weq := same_relation;
  cup := @union _;
  cap := @inter_rel _;
  bot := ∅₂;
  top := fun _ _ => True;
  neg := fun r => (fun _ _ => True) \ r 
|}.

(* 
Left and right division are defined such that
  left_div: R <= P // Q iff R ; Q <= P 
  right_div: R <= P \\ Q iff P ; R <= Q
*)

Definition div_l := fun A (P Q : relation A) => P ⨾  (Q ⁻¹).
Definition div_r := fun A (P Q : relation A) => (P⁻¹) ⨾  Q .

Notation "P // Q" := (div_l P Q) (at level 44).
Notation "P \\ Q" := (div_r P Q) (at level 44).
 
Canonical Structure kleene_algebra A: monoid.ops := {|
  ob := relation A;
  mor n m := partial_order A;
  dot n m p := @seq A;
  one n := <| fun _ : A => True |>(*fun x y => x = y*);
  itr n := @clos_trans _;
  str n := @clos_refl_trans _;
  cnv n m := @transp _;
  ldv n m p := @div_l _;
  rdv n m p := @div_r _
|}.


Canonical Structure kleene_algebra_with_test A: kat.ops := {|
  kar := kleene_algebra A;
  tst n := bool_algebra A;
  inj n := @eqv_rel A
|}.


Local Ltac u :=
  unfold set_union, set_inter, set_minus, set_compl,
         set_equiv, set_subset, set_empty, set_full,
         reflexive, transitive in *;
  ins; try solve [tauto | firstorder].


(* Boolean algebra is a lattice *)
Instance expr_lattice_laws A: lattice.laws BL (bool_algebra A).
Proof.
  constructor; try eauto; ins; u.
Qed.

Instance prog_lattice_laws A: lattice.laws BKA (partial_order A).
Proof.
  constructor; try eauto; ins; u.
Qed. 

(* Kleene algebra is a monoid *)
Instance prog_monoid_laws A: monoid.laws BKA (kleene_algebra A). 
Proof.
  constructor; try ins; eauto; u. 
  all: rels.
  - by right; ins; apply seq_id_r.
  - unfold seq, inclusion in *; ins; desf.
    induction H1; eauto.
  - right; right; ins.
    unfold seq, inclusion in *; ins; desf.
    induction H2; eauto.
Qed.


Instance prog_kat_laws A: kat.laws (kleene_algebra_with_test A).
Proof.
  constructor; simpl; eauto with typeclass_instances. 
  split; ins.
  by rewrite H. 
  by rewrite H.
  by rewrite id_union.
  by unfold eqv_rel; split; red; ins; desf.
  by unfold set_inter, eqv_rel, seq, same_relation, inclusion; split; ins; desf; eauto.
Qed.


Notation ra_nat_relation := (kleene_algebra_with_test nat).

Lemma r_seq_in_r_trans_clos x (r: ra_nat_relation x x): (r * r) <== r ^+.
Proof. 
kat.
Qed.



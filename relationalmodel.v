Require Import Hahn.
From RelationAlgebra Require Import kat normalisation rewriting kat_tac rel.
Set Implicit Arguments.

(* kat consists of a boolean algebra and a kleene algebra *)
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
  ob := unit;
  mor n m := partial_order A;
  dot n m p := @seq A;
  one n := (* <| fun _ : A => True |> *) fun x y => x = y;
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

(* Proving laws of kat holds *)

(* Boolean algebra is a lattice *)
Instance expr_lattice_laws A: lattice.laws BL (bool_algebra A).
Proof.
  constructor; try eauto; ins; u.
Qed.

(* Partial order is a lattice *)
Instance prog_lattice_laws A: lattice.laws BKA (partial_order A).
Proof.
  constructor; try eauto; ins; u.
Qed. 

(* Kleene algebra is a monoid *)
Instance prog_monoid_laws A: monoid.laws BKA (kleene_algebra A). 
Proof.
  constructor; try ins; eauto; u. 
  all: rels.
  - red; split; u.
    red; ins; red in H; desf.
  - right. ins. red; split; u. 
    red; ins; red in H; desf.
  - unfold seq, inclusion in *; ins; desf; u.
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
  - by rewrite H. 
  - by rewrite H.
  - by rewrite id_union.
  - by unfold eqv_rel; split; red; ins; desf.
  - by unfold set_inter, eqv_rel, seq, same_relation, inclusion; split; ins; desf; eauto.
  - ins.
    red; split.
    * unfold eqv_rel; do 2 red; ins. eexists; split; split; desf; red in H0; desf.
    * unfold eqv_rel; red; ins; split; red in H; desf.
Qed.


(* Tactics for converting a Hahn query into a ra library query *)
Ltac conv_term t k := 
  let rec conv_loop t k := 
  match t with 
  | ∅₂ => constr:(0)
  | ?a⁺ => conv_loop a ltac:(fun a' => k constr:(a' ^+))
  | ?a＊ =>  conv_loop a ltac:(fun a' => k uconstr:(a' ^*))
  | ?a⁻¹ =>  conv_loop a ltac:(fun a' => k constr:(a' `))
  | ?a ^? => conv_loop a ltac:(fun a' => k constr: (1 + a'))
  | ⦗ ?a ⦘ => conv_loop a ltac:(fun a' => k constr:( [a']))
  | ?a ⊆ ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' <== b')))
  | ?a ≡ ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' == b')))
  | ?a ⨾  ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' * b')))
  |  ?a ∪ ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' + b')))
  | ?a ∩ ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' ^ b')))
  | ?a // ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' -o b')))
  | ?a \\ ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(a' o- b')))
  |  pow_rel ?a O => k uconstr:(1)
  |  pow_rel ?a (S ?n) =>
        conv_loop (a ^^ n) ltac:(fun an' => conv_loop a ltac:(fun a' => k constr:(an' * a')))
  (*| ?f ?a ?b => 
      conv_loop a ltac:(fun a' => conv_loop b ltac:(fun b' => k constr:(f a' b'))) *)
  | _ => k t
  end in
  conv_loop t k.


Ltac conv := 
  change (relation) with (fun A => car (@mor (@kar (kleene_algebra_with_test A)) tt tt)) in *;
  match goal with 
  | |- ?a =>
     conv_term a ltac:(fun b => change a with b)
  end.

Ltac conv_all :=
  repeat match goal with 
  | H: ?A -> Prop |- _ => progress (change (A -> Prop) with (car (@tst (kleene_algebra_with_test A) tt)) in H)
  end;
  change (relation) with (fun A => car (kleene_algebra_with_test A tt tt)) in *;
  repeat match goal with 
  | H: ?a |- _ => progress (conv_term a ltac:(fun b => change a with b in H))
  | |- ?a => progress (conv_term a ltac:(fun b => change a with b))
  end.

Ltac kat_solve := ins; conv_all; kat.

Lemma bla3 A (b: A -> Prop) (q: relation A): ⦗ b ⦘ ;; q == q;; ⦗ b⦘ -> ⦗ b⦘;;q＊ == ⦗ b⦘;;(q;;⦗ b⦘)＊.
Proof.
  ins.
  conv_all.
Admitted.


(* Same examples *)

Lemma r_trans_comm A (r: relation A): (r⁺ ;; r) ≡ r ;; r⁺.
Proof.
  conv. ka.
Qed.

Lemma r_seq_trans_clos A (r: relation A): (r ;; r) ⊆ r⁺.
Proof.
  conv. ka.
Qed.



Lemma bla A (r: relation A): r^? ⊆ r＊.
Proof.
  kat_solve.
Qed.


Lemma bla1 A (x y: relation A):  x ;; y == x ;; y ;; x -> x ⊆ x ;; (y ;; x)＊.
Proof.
  kat_solve.
Qed.


Lemma bla2 A (x y: relation A):  x ;; y == x ;; y ;; x -> 
    (x ;; y)＊ ;; (x ;; y ;; x) ⊆ (x ;; y)＊ ;; x.
Proof.
  kat_solve.
Qed.









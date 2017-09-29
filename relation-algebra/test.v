Require Import Hahn.
Require Import RelationAlgebra.kat RelationAlgebra.normalisation RelationAlgebra.rewriting RelationAlgebra.kat_tac.
Set Implicit Arguments.



Lemma r_seq_in_r_trans_clos A (r: relation A): (r ⨾  r) ⊆ r ⁺.
Proof. 
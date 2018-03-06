Require Import synth.
Require Export Bauer. 
Require Import List.


Import ListNotations.
Open Scope bool_scope.

Definition instance := Graph.
Definition solution := vertex_list.

Definition metric := unit.
Definition eval (S : solution) := tt.
Definition better (m1 m2 : metric) := true.

Definition verifier (I : instance) (S : solution) := 
let v_list := S.elements (V I) in 
path I S /\
forall v, (In v v_list -> In v S).

Fixpoint checker (I : instance) (S : solution) := 
let v_set := S.elements (V I) in 
pathb I S &&
forallb (fun v => existsb (fun v' => v' =? v) S) v_set.

Definition gen_space := fun I => all_perm (S.elements (V I)).
Definition Hp_brute_force := synthesize instance solution metric checker eval better gen_space.

Compute (Hp_brute_force (K 5)).
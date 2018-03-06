Require Import synth.
Require Export Bauer. 
Require Import List.


Import ListNotations.
Open Scope bool_scope.

Definition instance := Graph.
Definition solution := vertex_list.

Definition metric := nat.
Definition eval (S : solution) := length S.
Definition better (m1 m2 : metric) := m1 <=? m2.

Definition verifier (I : instance) (S : solution) := 
let v_list := S.elements (V I) in 
path I S /\
forall v, (In v v_list -> In v S).

Fixpoint checker (I : instance) (S : solution) := 
let v_set := S.elements (V I) in 
pathb I S &&
forallb (fun v => existsb (fun v' => v' =? v) S) v_set.

Definition gen_space := fun I => all_perm (S.elements (V I)).
Definition Tsp_brute_force := synthesize instance solution metric checker eval better gen_space.

Compute (Tsp_brute_force (K 10)).
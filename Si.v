Require Import synth.
Require Export Bauer. 
Require Import List.
Require Import Coq.Logic.FinFun.
Require Import Coq.Init.Specif.



Import ListNotations.
Open Scope bool_scope.

Record g_vertex (g : Graph) : Type := {
  v :> vertex;
  v_g : S.In v (V g)
}.

Check g_vertex.

Check sigT.
Definition instance := prod Graph Graph.
Definition solution := sigT (fun g0 : Graph => 
  sigT (fun g' : Graph => (g_vertex g0) -> (g_vertex g')
  )
).

Definition metric := unit.
Definition eval (S : solution) := tt.
Definition better (m1 m2 : metric) := true.

Fixpoint checker (I : instance) (S : solution) := 
match (I,S) with 
| ((G,H),pf) => 
let G0 := projT1 pf in 
let G' := projT1 (projT2 pf) in 
let f := projT2 (projT2 pf) in 
H = G' /\ subgraph G0 G = true /\ Bijective f
end.

Definition gen_space := fun I =>
match I with 
| (G,H) => 
let (vH, eH) := (V H, E H) in
let v_set := filter (fun v => S.cardinal =? S.cardinal vH) (all_subset (S.elements (V I))) in 
let e_set := all_list (S.elements 
end.

Definition Hp_brute_force := synthesize instance solution metric checker eval better gen_space.

Compute (Hp_brute_force (K 5)).
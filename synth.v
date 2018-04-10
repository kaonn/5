Require Import List.
Require Import MSets Arith.
Require Import Coq.Numbers.NaryFunctions.
From Template Require Import All.
Import ListNotations MonadNotation.
Require Export Coq.Strings.String.
Require Import Ascii.
Extraction Language Haskell.
Require Import FMaps.
Require Import ExtLib.Data.HList.


Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

Run TemplateProgram (t <- tmQuoteInductive "nat";; tmPrint t).
Run TemplateProgram (r <- tmQuote nat;; tmPrint r).


Inductive a : Type := 
| A : a.

Inductive b : Type := 
| B : b
| Ba : a -> b
| Baa : a -> b -> b.

Inductive prod3 (A B C : Type) : Type := 
pair3 : A -> B -> prod3 A B C
| pair3' : B -> prod3 A B C
| pair3'' : C -> prod3 A B C.

Print sum.
Definition rec (F : Type -> Type -> Type) (A : Type) : Type := forall X, (F X A -> X) -> X.

Definition snat := rec (fun X _ => sum unit X) unit.

Definition szero : snat := fun x f => f (inl tt).
Definition sone : snat := fun x f => f (inr (szero x f)).

Definition twice (sn : snat) : snat := fun x f => 
sn x (fun body => 
match body with
| inl tt => f (inl tt)
| inr n' => f (inr (f (inr (n'))))
end).

Definition ss (sn : snat) : snat := fun x f => f (inr (sn x f)).

Definition list' := rec (fun X A => sum unit (prod A X)).


Goal ss szero = sone.
Proof.
compute. reflexivity.
Qed.

Check (fun t1 t2 => prod (list t1) (list (list t2))).
Inductive TyOp : Type := 
| tfunctor : forall (F : Type -> Type), TyOp
| tprod : TyOp -> TyOp -> TyOp
| tsum : TyOp -> TyOp -> TyOp.



Section var.
Variable var : (Type -> Type) -> Type.


Inductive Species : (Type -> Type) -> Type := 
| zero : Species (fun _ => Empty_set)
| one : Species (fun x => unit)
| singleton : Species (fun x => x)
| cprod : forall {F G}, Species F -> Species G -> Species (fun x => prod (F x) (G x))
| ssum : forall {F G}, Species F -> Species G -> Species (fun x => sum (F x) (G x))
| srec : forall F, (forall A, (var (F A) -> Species (F A))) -> Species (rec F)
| svar : forall F, var F -> Species F.
End var.

Check Species.

Definition var1 := fun _ : Type -> Type => unit.
Definition F1 := (fun A X => sum unit (prod A X)).
Definition Id := fun X : Type => X.


Definition s1 := (srec var1 F1 (fun A v => ssum var1 (one var1) (cprod var1 (singleton var1) (svar var1 Id v)))).

Definition split_i {X : Type} (i : nat) (l : list X) := (firstn i l, skipn i l).

Fixpoint tabulate_list {X : Type} (f : nat -> X) n := 
match n with 
| 0 => []
| S n => cons (f n) (tabulate_list f n)
end.

Check 4::[].

Definition varType n' n bound (T1 T2 : Type) : Type := 
match existsb (fun e => e =? n') bound with 
  | false => T1
  | _ => 
    match n' =? n with 
    | true => T2
    | _ => T1
    end
  end.

Definition varExp {T1 T2} n' n bound (E1 : T1) (E2 : T2) : varType n' n bound T1 T2 :=
match existsb (fun e => e =? n') bound as r return 
match r with 
|false => T1
| _ => match n' =? n with 
        | true => T2
        | _ => T1 end
end
with 
  | false => E1
  | _ => 
    match n' =? n as r' return 
    match r' with 
    | true => T2
    | _ => T1
    end
   with 
    | true => E2
    | _ => E1
    end
  end.

Fixpoint squash var T (s : Species (Species var) T) : Species var T :=
match s with 
| zero _ => zero _
| one _ => one _
| singleton _ _ => singleton _ _
| cprod _ T1 T2 => cprod _ (squash var _ T1) (squash var _ T2)
| ssum _ T1 T2 => ssum _ (squash var _ T1) (squash var _ T2)
| srec _ F f => srec _ F (fun A v => squash var _ (f A (svar var (F A) v)))
| svar _ F v => v
end.

Definition Species1 (t1 t2 : Type -> Type) := forall v, v t1 -> Species v t2.

Definition Subst {var} (t1 t2 : Type -> Type) (T : Species1 t1 t2) (T' : Species var t1) : Species var t2 :=  
squash var _ (T (Species var) T').

Fixpoint enumerate A S s labels := 
let fix enum (A : Type) {var} {S : Type -> Type} (s : Species var S) (labels : list A) : list (S A) := 
match s with
| zero _ => []
| (one _) => match labels with [] => [tt ] | _ => [] end
| singleton _ => match labels with [x] => [x] | _ => [] end
| cprod _  s1 s2 => 
  let all_splits := map (fun i => split_i i labels) (tabulate_list (fun i => i) (List.length labels)) in 
  concat (map (fun e => match e with (l,r) => list_prod (enum A s1 l) (enum A s2 r) end) all_splits)
| ssum _ s1 s2 => app (map inl (enum A s1 labels)) (map inr (enum A s2 labels))
| srec _ F f => 
  let body := Subst _ _ (f A) s 
  in enum A (F A) body labels
| svar _ F v => []
end
in 
enum A S s labels.

Compute enumerate nat (rec (fun t => t) (fun x =>
match x with
| interp F => ssum one (cprod singleton (var F))
end)) [1;2]. 

Compute enumerate nat (cprod (ssum singleton singleton) (ssum singleton singleton)) [1;2].

Print list.

Run TemplateProgram (t <- tmQuoteRec (list nat);; r <- tmEval all t;; tmPrint r).

Run TemplateProgram (t<- (tmQuote (nat -> nat));; t <- tmUnquoteTyped Set t;; tmPrint t).

Definition str_eq s1 s2 := match string_dec s1 s2 with left _ => true | _ => false end. 
Definition ascii_eq c1 c2 := match ascii_dec c1 c2 with left _ => true | _ => false end. 

Fixpoint map_ {A B} (f : A -> TemplateMonad B) (l : list A) : TemplateMonad (list B) :=
match l with 
| [] => tmReturn []
| x::xs => r <- f x ;; rs <- map_ f xs ;; tmReturn (r::rs)
end.

Fixpoint split_until (f : ascii -> bool) s :=
match s with 
| EmptyString => (EmptyString, EmptyString)
| String c xs => 
  if f c then (String c EmptyString, xs)
  else
  let (a,b) := split_until f xs in 
  (String c a,b)
end.

Compute split_until (ascii_eq ".") "fd.a".
Fixpoint strip s dummy {struct dummy} := 
let (a,b) := split_until (ascii_eq ".") s in
match b with 
| EmptyString => s
| _ => match dummy with 
  | 0 => EmptyString
  | S n' => strip b n'
  end
end.

Compute strip "Coq.Init.Datatypes.nat" 100.
 
Check fold_left.

Print prod.

Fixpoint enumerate (ind : Type) (n : nat) : TemplateMonad (list ind) := 
tm <- tmQuote ind;; match tm with 
| tInd ind' _ => 
let qualified := inductive_mind ind' in
let indName := strip qualified (length qualified) in
decl <- tmQuoteInductive indName ;;
indBody <- 
  match find (fun body => str_eq (ind_name body) indName) (ind_bodies decl) with 
  | Some e => tmReturn e
  | _ => tmFail (append "fail" indName)
  end;;
let find_base := (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => true | _ => false end) cstrs)
in
let find_ind := 
  (fun body => 
  let cstrs := ind_ctors body in 
  filter (fun cstr => match cstr with (_,_,0) => false | _ => true end) cstrs)
in 
(match n with 
| 0 => map_ (fun cstr => match cstr with (tn,_,_) => tmUnquoteTyped ind (tConstruct (mkInd indName 0) 0 [])  end) 
    (find_base indBody)
| S n' => 
  let cstrs := find_ind indBody in 
  let flatten := fix f tm' := 
    match tm' with 
    | tRel _ => [tm]
    | tInd ind _ => tm'
    | tProd _ tm1 tm2 => f tm1 ++ f tm2
    end
  in
  let get_args l := removelast (flatten l) in
  map_ (fun acc cstr => match cstr with 
    | (name, tm, arity) => 
      all_args <- map_ (fun arg => ty <- tmUnquote arg;; enumerate (projT2 ty) n') (get_args tm);;
      let combined := map (fun args => 
          
    end) cstrs 
end)
| _ => tmFail "non inductive type"
end.
  
Check enumerate.
Run TemplateProgram (r <- enumerate nat 0;; tmPrint r).

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Class Ord A `{Eq A} : Type :=
  {
    le : A -> A -> bool
  }.

Module S := Make Nat_as_OT.

Module SP := WPropertiesOn Nat_as_OT S.

Module SF := WFactsOn Nat_as_OT S.

Fixpoint tabulate f n := 
match n with 
| 0 => S.empty
| S n => S.add (f n) (tabulate f n)
end.

Definition list_max {X : Type} (f : X -> X -> bool) l d := fold_left (fun acc e => if f acc e then acc else e) l d.

Fixpoint all_subset (s : S.t) := 
S.fold (fun e subsets => subsets ++ (map (fun s => S.add e s) subsets)) s [S.empty].



Fixpoint all_perm {X : Type} (l : list X) :=
match l with 
| [] => [[]]
| [x] => [[x]]
| x::xs => 
  let perms := all_perm xs in 
  fold_left (fun ps perm => 
    let perms' :=  
      tabulate_list (fun i => 
       let (a,b) := split_i i perm in a ++ [x] ++ b
      ) (1 + length perm)
    in ps ++ perms') perms []
end.

Definition algorithm (instance solution metric : Type) f 
 (verifier : instance -> solution -> Prop)
 (eval : solution -> metric) 
 (better : metric -> metric -> Prop) := 
forall (I : instance) (Sol Cand : solution), 
  (f I = Some Sol -> verifier I Sol /\ ((verifier I Cand) -> better (eval Sol) (eval Cand)))
/\
  (f I = None -> ~exists Cand', verifier I Cand').

Definition synthesize (instance : Type) (solution : Type) (metric : Type)
(checker : instance -> solution -> bool) 
(eval : solution -> metric) 
(better : metric -> metric -> bool) 
(gen_space : instance -> list solution) 
: instance -> option solution := 
fun I => 
let candidates := filter (checker I) (gen_space I) in 
let ranks := map (fun cand => (eval cand, cand)) candidates in 
match ranks with 
| [] => None
| x::xs => Some (snd (list_max (fun e1 e2 => match e1, e2 with | (s1,_), (s2,_) => better s1 s2 end) xs x))
end.
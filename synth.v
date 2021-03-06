Require Import List.
Require Import MSets Arith.
Require Import Coq.Numbers.NaryFunctions.
From Template Require Import All.
Import ListNotations MonadNotation.
Require Export Coq.Strings.String.
Require Import Ascii.
Extraction Language Haskell.
Require Import FMaps.

Require Import DepList.

Definition printInductive (name  : ident): TemplateMonad unit :=
  (tmBind (tmQuoteInductive name) tmPrint).

Run TemplateProgram (t <- tmQuoteInductive "nat";; tmPrint t).
Run TemplateProgram (r <- tmQuote nat;; tmPrint r).


Definition split_i {X : Type} (i : nat) (l : list X) := (firstn i l, skipn i l).

Fixpoint tabulate_list {X : Type} (f : nat -> X) n : List.list X := 
match n with 
| 0 => []
| S n => List.cons (f n) (tabulate_list f n)
end.


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

Definition var1 := fun _ : Type -> Type => unit.

Definition Id := fun X : Type => X.

Inductive tlist : list Type -> Type :=
| Hnil : tlist nil
| Hcons : forall (T : Type) {TS}, list T -> tlist TS -> tlist (T :: TS).

Check Hcons nat [1;2;3] Hnil.

Check HFirst.

Check sigT.
Check sigT list.
Check existT list nat [1;2].

Definition tget' T TS : member T TS  -> Type := fun _ => T.
Fixpoint tget {TS : list Type} {T} (hs : tlist TS)
: member T TS ->  list T :=
  match hs in tlist TS return member T TS -> list T with
    | Hnil =>
      fun x => match x in member _ Z return match Z with
                                           | nil => list T
                                           | _ :: _ => Type * list unit
                                         end
               with
                 | HFirst => (unit, [tt])
                 | HNext _ _ _ => (unit, [tt])
               end
    | Hcons T' x hs =>
      fun m => match m in member _ Z
                     return match Z with
                              | nil => list T
                              | x :: y => list x -> (member T y -> list T) -> list T
                            end
               with
                 | HFirst => fun x' _ => x'
                 | HNext _ _ m' => fun _ f => f m'
               end x (@tget _ T hs)
  end.

Definition h1 := Hcons string ["a";"b";"c"] (Hcons nat [1;2;3] Hnil).
Definition i1 : member string [string;nat] := HFirst.
Check i1.
Compute tget h1 i1.

Definition Nfunctor := list Type -> Type.

Definition nrec (F : Type -> Type): Type := forall X, (F X-> X) -> X.

Definition rfold F  : forall X, (F X -> X) -> (nrec F) -> X := 
fun X k t => t X k.

Class Functor (F : Type -> Type) : Type := 
{
   liftF : forall {X Y}, (X -> Y) -> (F X -> F Y)
}.

Instance Maybe : Functor (fun X => sum unit X) :=
{
  liftF := fun X Y => fun f => fun x => 
  match x with 
  | inl tt => inl tt
  | inr y => inr (f y)
  end
}.

Definition rin F `{Functor (F)} : F (nrec F) -> nrec F :=
fun s => fun X k => k ((liftF (rfold F X k)) s). 

Definition rout F `{Functor (F)} : nrec F -> F (nrec F) :=
rfold F (F (nrec F)) (liftF (rin F )).


Section s.
Variable ts : list Type.
Inductive Species : list Type -> Type -> Type := 
| zero : forall C, Species C (Empty_set)
| one :  forall C {x} (m : member x ts), Species C ( unit)
| singleton :  forall C {x} (m : member x ts), Species C ( tget' _ ts m)
| cprod : forall C {F G}, Species C F -> Species C G -> Species C ( prod F G)
| pprod : forall C {F G}, Species C F -> Species C G -> Species C ( prod F G)
| ssum : forall C {F G}, Species C F -> Species C G -> Species C (sum F G)
| srec : forall C F `{Functor (F)}, Species ((nrec F)::C) (F (nrec F)) -> 
  Species C (nrec F) 
| svar : forall C F, member F C -> Species C F.
End s.


Fixpoint insertAt A (t : A) (G : list A) (n : nat) {struct n} : list A :=
match n with
| O => t :: G
| S n' => match G with
| nil => t :: G 
| t' :: G' => t' :: insertAt A t G' n'
end
end.

Fixpoint liftVar A t G (x : member t G) t' n : member t (insertAt A t' G n) :=
match x with
| HFirst => match n return member t (insertAt A t' (t :: _) n) with
| O => HNext t' (t::_) HFirst
| _ => HFirst
end
| HNext t'' G'' x' => 
match n return member t (insertAt A t' (t''::G'') n) with
| O => HNext _ _ (HNext _ _ x')
| S n' => HNext _ _ (liftVar A _ _ x' t' n')
end
end.

Fixpoint lift' k C t' n t (s : Species k C t) : Species k (insertAt _ t' C n) t := 
match s with 
| zero _ C => zero _ (insertAt _ t' C n)
| one _ C i => one _ (insertAt _ t' C n) i
| singleton _ C _ => singleton _ (insertAt _ t' C n) _
| cprod _ C S1 S2 => cprod _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| pprod _ C S1 S2 => pprod _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| ssum _ C S1 S2 => ssum _ (insertAt _ t' C n) (lift' k C t' n _ S1) (lift' k C t' n _ S2)
| srec _ C F S' => srec _ (insertAt _ t' C n) F (lift' k _ t' (S n) _ S')
| svar _ C F x => svar _ _ _ (liftVar _ _ _ x t' n)
end.

Definition lift k C t' t (e : Species k C t) : Species k (t' :: C) t := lift' k C t' O t e.


Fixpoint subst {k} C t (s : Species k C t) C' : hlist (Species k C') C -> Species k C' t :=
match s with 
| zero _ C => fun _ => zero _ _
| one _ C i => fun _ => one _ _ i
| singleton _ C _ => fun _ => singleton _ _ _
| cprod _ C S1 S2 => fun s =>  cprod _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| pprod _ C S1 S2 => fun s =>  pprod _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| ssum _ C S1 S2 => fun s => ssum _ _ (subst C _ S1 _ s) (subst C _ S2 _ s)
| srec _ _ F S' => fun s => srec _ _ F (subst _ _ S' _ (svar _ (_::C') _ (HFirst) ::: hmap (fun f =>  lift k C' _ f) s))
| svar _ C F x => fun s => hget s x
end.

Fixpoint convert {n A} (l : ilist A n) : list (fin n) := [].

(*fun tls h => 
  let C'' := nrec ts F :: C' in 
  let s'' := subst C'' _ s' C' (HCons s h) in 
  enum s'' tls*)

Fixpoint part {T} (ls : list T) :=
match ls with
| [] => [([],[])]
| x::xs => 
  let r := part xs in 
  let add_l := fun p => match p with (l,r) => (x::l,r) end in
  let add_r := fun p => match p with (l,r) => (l,x::r) end in
  List.app (map add_l r) (map add_r r)
end.


Fixpoint partition {ts} (tls : tlist ts) : list (tlist ts * tlist ts) :=
match tls with 
| Hnil => [(Hnil,Hnil)]
| Hcons T ls tls' => 
  let tlspart := partition tls' in 
  let lpart := part ls in 
  concat (map (fun tlp => match tlp with 
  (l,r) => map (fun p => match p with (l',r') => (Hcons T l' l, Hcons T r' r) end) lpart 
  end) tlspart)
end.

Check list_prod.

(* (x,y) = [x,y) *)
Definition interval := prod nat nat.

Definition inside '(i,n) :=
match i with 
| (x,y) => 
 (x <=? n) && (n <? y)
end.

Definition intersection (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (max x1 x2, min y1 y2)
end.

Definition iadd (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (x1 + x2, y1 + y2)
end.

Definition union (i1 : interval) (i2 : interval) := 
match i1,i2 with 
| (x1,y1), (x2,y2) => (min x1 x2, max y1 y2)
end.

Fixpoint make_list {A l X} {x : A} (m : member x l) (t : X) (e : X) : list _ := 
match m with 
| HFirst => t :: tabulate_list (fun _ => e) ((List.length l) - 1) : list X
| HNext x l' m' => e :: (make_list m' t e)
end.

Check HNext.
Definition H : member 3 [1;2;3] := HNext 1 [2;3] (HNext 2 [3] (HFirst )).
Compute make_list (H) 5 0.

 Fixpoint zip {A B C} (f : A -> B -> C) (l : list A) (l' : list B) : list C :=
      match l,l' with
        | x::tl, y::tl' => (f x y)::(zip f tl tl')
        | _, _ => nil
      end.
Definition int_max := 10000.
Check make_list.
Fixpoint bound {ts K F} (s : Species ts K F) : list interval := 
match s with 
| zero _ _ => tabulate_list (fun _ => (0,0)) (List.length ts)
| one _ _ m => make_list m (0,1) (0,int_max)
| singleton  _ _ m => make_list m (1,2) (0, int_max)
| cprod _ _ s1 s2 => zip intersection (bound s1) (bound s2)
| pprod _ _ s1 s2 => zip iadd (bound s1) (bound s2)
| ssum _ _ s1 s2 => zip union (bound s1) (bound s2)
| srec _ _ _  s' => bound s'
| svar _ _ _ _ => tabulate_list (fun _ => (int_max,int_max)) (List.length ts)
end.

Fixpoint lengths {ts} (tls : tlist ts) :=
match tls with 
| Hnil => []
| Hcons _ l tlss => (List.length l) :: lengths tlss
end.

Check forallb.
Definition enumerate (n : nat) {ts : list Type} {F} {K} (s : Species ts K F) : 
forall tls : tlist ts, hlist (Species ts K) K -> list (F). 
refine(
(fix enum n {ts : list Type} {F} {K} (s : Species ts K F) : forall tls : tlist ts, hlist (Species ts K) K -> list (F) := 
match n with 
| 0 => fun _ _ => []
| S n' => 
match s in Species _ KK F return forall (s : Species _ KK F) (tls : tlist ts), hlist (Species ts KK) KK -> list (F) with
| zero _ C => fun _ tls _ => []
| one _ _ m => fun _ tls _ => 
  match tget tls m with [] => [tt] | _ => [] end
| singleton _ _ m => fun _ tls _ => 
  match tget' _ ts m with 
  | T => match tget tls m in list _ return list T with 
      | ls => match ls with [x] => [x] | _ => [] end
      end
  end
| pprod _ C' s1 s2 => fun _ tls _ => 
  let sizes := lengths tls in 
  let bounds := bound s in 
  let sb := combine bounds sizes in 
  if forallb inside sb then
  let parts : list (tlist ts * tlist ts) := partition tls in 
   concat (map (fun part => match part with (l,r) => list_prod (enum n' s1 l _) (enum n' s2 r _) end) parts)
  else []
| cprod _ _ s1 s2 => fun _ tls _ => list_prod (enum n' s1 tls _) (enum n' s2 tls _)
| ssum _ _ s1 s2 => fun _ tls  _ => app (map inl (enum n' s1 tls _)) (map inr (enum n' s2 tls _))
| srec _ C' F s' => fun _ tls _ => 
  let sizes := lengths tls in 
  let bounds := bound s in 
  let sb := combine bounds sizes in 
  if forallb inside sb then _
  else []
| svar _ _ F v => fun _ tst _ => []
end s
end) n ts F K s).
- exact h.
- exact h.
- exact h.
- exact h.
- exact h. 
- exact h.  
- intros.
  pose ( C'' := nrec F :: C').
  pose (s'' := subst C'' _ s' C' (HCons s1 h)).
  pose (r := enum n' _ _ _  s'' tls h).
  exact (map (rin _  ) r).
Defined.

Extraction Language Ocaml.


(* lists *)

Definition ts : list Type := [nat : Type].
Definition F1 := (fun X => sum unit (prod (tget' _ ts HFirst) X)).
Instance F1F : Functor F1 := 
{
  liftF := fun X Y f x => 
  match x with 
  | inl tt => inl tt
  | inr (a,x') => inr (a, f x')
  end
}.
Definition C1 := [nrec F1].
Definition s := srec ts []  F1 (ssum ts C1 (one ts C1 HFirst) (pprod ts C1 (singleton ts C1 HFirst) (svar ts C1 (nrec F1) (HFirst)))).
Definition tls : tlist ts := Hcons nat [1;2;3] Hnil.
Definition C0 : hlist (Species ts []) [] := HNil.

Definition e := enumerate 1000 s tls C0.
Parameter int : Type. (* This is the Ocaml int type. *)
Extract Inlined Constant int => "int". (* so, extract it that way! *)
Parameter ltb: int -> int -> bool. (* This is the Ocaml (<) operator. *)
Extract Inlined Constant ltb => "(<)". (* so, extract it that way! *)

Parameter int2Z: int -> nat.
Axiom ltb_lt : forall n m : int, ltb n m = true <-> int2Z n < int2Z m.

Compute bound s.
Compute e.

Extraction "enum.ml" e.


(* multi-sorted product *)
Definition ts2 : list Type := [nat : Type; string : Type].
Definition tls2 : tlist ts2 := Hcons nat [1;2] (Hcons string ["a";"b";"c"] Hnil).
Definition s2 := pprod ts2 [] (ssum ts2 [] (singleton ts2 [] HFirst) (singleton ts2 [] (HNext nat [string] HFirst))) (singleton ts2 [] HFirst).
Definition C2 : hlist (Species ts2 []) [] := HNil.
Compute enumerate 100 s2 tls2 C2.
Compute (List.length (enumerate 3 s2 tls2 C2)).

(* rose trees *)
Definition rlistF A := (fun X => sum unit (prod A X)).
Instance rlistFF : forall A, Functor (rlistF A) :=
{
  liftF := fun X Y f m => 
   match m with 
   | inl tt => inl tt
   | inr (a,x) => inr (a, f x)
   end
}.
Definition rlist A := nrec (rlistF A).
Check @liftF.
Definition sizet {A} (m : A) := 0.
Definition rnil {A} : rlist A := fun X f => f (inl tt).
Definition rcons {A} (a : A) (l : rlist A) : rlist A := fun X f => f (inr (a, l X f)).
Definition l1 := rcons nat (rcons string rnil).
Fixpoint k  {X Y : Type} (f : X -> Y) (m : rlist X) (d : nat)  : rlist Y :=
  match d with 
  | 0 => rnil
  | S d' => 
  let out := rout (rlistF X) m in
  match out with
  | inl tt => rin (rlistF Y) (inl tt)
  | inr (a, x) => rin (rlistF Y) (inr (f a, k f x d'))
  end
  end.

Compute k (fun X => sum unit X) l1 100.

Instance ListF : Functor (rlist) := 
{
  liftF := fun X Y f m => 
  let out := rout (rlistF X) m in
  match out with
  | inl tt => rin (rlistF Y) (inl tt)
  | inr (a, x) => rin (rlistF Y) (inr (f a, k f x 1000))
  end
}.

Definition F3 := (fun X => sum unit (prod (tget' _ ts HFirst) (rlist X))).
Instance F3F : Functor F3 := 
{
  liftF := fun X Y f x => 
  match x with 
  | inl tt => inl tt
  | inr (a, xl) => inr (a, liftF f xl)
  end
}.
Definition C3 := [nrec F3].
Definition C3' := [rlist (nrec F3) ;nrec F3].
Definition ts3 : list Type := [nat : Type].
Definition tls3 : tlist ts3 := Hcons nat [1;2] Hnil.
Definition t : member (nrec F3) C3' := HNext _ _ HFirst.
Definition s3 := srec ts3 []  F3 (ssum ts3 C3 (one ts3 C3 (HFirst)) 
  (pprod ts3 C3 (singleton ts3 C3 HFirst) 
    (srec ts3 C3 (rlistF (nrec F3)) (ssum ts3 C3' (one ts3 C3' HFirst) (pprod ts3 C3' ((svar ts3 C3' (nrec F3) (t))) ((svar ts3 C3' (rlist (nrec F3)) HFirst)) ) ) )
  )).


Definition Empty : hlist (Species ts3 []) [] := HNil.

Check enumerate 20 s3 tls3 Empty. 

Extraction "enum.ml" e.

Fixpoint all_perm {X : Type} (l : list X) :=
match l with 
| [] => [[]]
| [x] => [[x]]
| x::xs => 
  let perms := all_perm xs in 
  fold_left (fun ps perm => 
    let perms' :=  
      tabulate_list (fun i => 
       let (a,b) := split_i i perm in List.app (List.app a  [x])  b
      ) (1 + List.length perm)
    in List.app ps perms') perms []
end.

Compute all_perm [1;2;3;4;5;6;7].

(* end; ignore below *)
Run TemplateProgram (t <- tmQuoteRec (list nat);; r <- tmEval all t;; tmPrint r).

Check tmQuote (list).
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

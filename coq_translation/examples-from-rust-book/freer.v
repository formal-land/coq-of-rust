Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope string_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.

Export List.ListNotations.

Module Notation.
  (** A class to represent the notation [e1.e2]. This is mainly used to call
      methods, or access to named or indexed fields of structures.
      The kind is either a string or an integer. *)
  Class Dot {Kind : Set} (name : Kind) {T : Set} : Set := {
    dot : T;
  }.
  Arguments dot {Kind} name {T Dot}.

  (** A class to represent associated functions (the notation [e1::e2]). The
      kind might be [Set] functions associated to a type, or [Set -> Set] for
      functions associated to a trait. *)
  Class DoubleColon {Kind : Type} (type : Kind) (name : string) {T : Set} :
    Set := {
    double_colon : T;
  }.
  Arguments double_colon {Kind} type name {T DoubleColon}.

  (* Add parent type somehow? like option (Dot "p1" Rectangle) ? *)
  (* Class Update {Kind : Type} (name : Kind) {T A : Set} : Set := { *)
  (*   update : T -> A -> T; *)
  (* }. *)
  (* Arguments update {Kind} name {T A Update} _ _. *)
End Notation.

(** A method is also an associated function for its type. *)
Global Instance AssociatedFunctionFromMethod
  (type : Set) (name : string) (T : Set)
  `(Notation.Dot (Kind := string) name (T := type -> T)) :
  Notation.DoubleColon type name (T := type -> T) := {
  Notation.double_colon := Notation.dot name;
}.

Definition defaultType (T : option Set) (Default : Set) : Set :=
  match T with
  | Some T => T
  | None => Default
  end.

Parameter sequence : forall {A B : Set}, A -> B -> B.

Notation "e1 ;; e2" := (sequence e1 e2)
  (at level 61, right associativity).



Definition f64 : Set := Z.

Definition ref (A : Set) : Set := A.
Definition mut_ref : Set -> Set := ref.

Definition deref {A : Set} (r : ref A) : A := r.

(** The functions on [Z] should eventually be replaced by functions on the
    corresponding integer types. *)
Global Instance Method_Z_abs : Notation.Dot "abs" := {
  Notation.dot := (Z.abs : Z -> Z);
  }.

Module Add.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        add : Self -> Rhs -> Output;
      }.

      Global Instance Method_add `(Trait) : Notation.Dot "add" := {
        Notation.dot := add;
      }.
    End Add.

    Module AddAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        add_assign : mut_ref Self -> Rhs -> unit;
      }.

      Global Instance Method_add_assign `(Trait) : Notation.Dot "add_assign" := {
        Notation.dot := add_assign;
      }.
    End AddAssign.

 Module Sub.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        sub : Self -> Rhs -> Output;
      }.

      Global Instance Method_sub `(Trait) : Notation.Dot "sub" := {
        Notation.dot := sub;
      }.
    End Sub.

    Module SubAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        sub_assign : mut_ref Self -> Rhs -> unit;
      }.

      Global Instance Method_sub_assign `(Trait) : Notation.Dot "sub_assign" := {
        Notation.dot := sub_assign;
      }.
    End SubAssign.

    Module Mul.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        mul : Self -> Rhs -> Output;
      }.

      Global Instance Method_mul `(Trait) : Notation.Dot "mul" := {
        Notation.dot := mul;
      }.
    End Mul.

    Module MulAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        mul_assign : mut_ref Self -> Rhs -> unit;
      }.

      Global Instance Method_mul_assign `(Trait) : Notation.Dot "mul_assign" := {
        Notation.dot := mul_assign;
      }.
    End MulAssign.

    (* The trait implementations for [Z] are convenient but should be replaced
       by the implementations for the native types eventually. *)
    Module Impl_Add_for_Z.
      Definition add : Z -> Z -> Z := Z.add.

      Global Instance Method_add : Notation.Dot "add" := {
        Notation.dot := add;
      }.

      Global Instance Add_for_Z : Add.Trait Z None := {
        add := add;
      }.
    End Impl_Add_for_Z.

    Module Impl_AddAssign_for_Z.
      Parameter add_assign : mut_ref Z -> Z -> unit.

      Global Instance Method_add_assign : Notation.Dot "add_assign" := {
        Notation.dot := add_assign;
      }.

      Global Instance AddAssign_for_Z : AddAssign.Trait Z None := {
        add_assign := add_assign;
      }.
    End Impl_AddAssign_for_Z.

     Module Impl_Sub_for_Z.
      Definition sub : Z -> Z -> Z := Z.sub.

      Global Instance Method_sub : Notation.Dot "sub" := {
        Notation.dot := sub;
      }.

      Global Instance Sub_for_Z : Sub.Trait Z None := {
        sub := sub;
      }.
    End Impl_Sub_for_Z.

    Module Impl_SubAssign_for_Z.
      Parameter sub_assign : mut_ref Z -> Z -> unit.

      Global Instance Method_sub_assign : Notation.Dot "sub_assign" := {
        Notation.dot := sub_assign;
      }.

      Global Instance SubAssign_for_Z : SubAssign.Trait Z None := {
        sub_assign := sub_assign;
      }.
    End Impl_SubAssign_for_Z.

    Module Impl_Mul_for_Z.
      Definition mul : Z -> Z -> Z := Z.mul.

      Global Instance Method_mul : Notation.Dot "mul" := {
        Notation.dot := mul;
      }.

      Global Instance Mul_for_Z : Mul.Trait Z None := {
        mul := mul;
      }.
    End Impl_Mul_for_Z.

    Module Impl_MulAssign_for_Z.
      Parameter mul_assign : mut_ref Z -> Z -> unit.

      Global Instance Method_mul_assign : Notation.Dot "mul_assign" := {
        Notation.dot := mul_assign;
      }.

      Global Instance MulAssign_for_Z : MulAssign.Trait Z None := {
        mul_assign := mul_assign;
      }.
    End Impl_MulAssign_for_Z.



Class Functor (f : Set -> Set) : Set := {
    fmap : forall {a b : Set}, (a -> b) -> f a -> f b
  }.

Inductive Lan (g : Set -> Set) (a : Set) : Set := CLan x : g x -> (x -> a) -> Lan g a.

Arguments CLan {g a x} _ _.

Global Instance Functor_Lan g : Functor (Lan g) := {
    fmap := fun _ _ f '(CLan gx h) => CLan gx (fun x => f (h x))
  }.

Definition lan {g : Set -> Set} {a : Set} : g a -> Lan g a := fun ga => CLan ga (@id a).

Inductive FFree (g : Set -> Set) (a : Set) : Set :=
| FPure : a -> FFree g a
| FImpure x : g x -> (x -> FFree g a) -> FFree g a.

Arguments FPure {g a} _.
Arguments FImpure {g a x} _ _.

Fixpoint myfmap {g : Set -> Set} {a b : Set} (f : a -> b) (ffa : FFree g a) : FFree g b :=
  match ffa with
  | FPure a => FPure (f a)
  | FImpure gx h => FImpure gx (fun x => myfmap f (h x))
  end.

Global Instance Function_FFree g : Functor (FFree g) := {
    fmap := (@myfmap g)
  }.

Require Import Coq.Program.Basics.
Require Import FunctionalExtensionality.

Lemma myfmap_id : forall (a : Set) g, myfmap (@id a) = (@id (FFree g a)).
Proof.
  intros a g.
  apply functional_extensionality; intro x.
  induction x; [reflexivity|].
  simpl. unfold id.
  apply f_equal.
  apply functional_extensionality.
  intros. rewrite H. reflexivity.
Qed.

Open Scope program_scope.

Lemma myfmap_comp : forall (g : Set -> Set) (a b c : Set) (f : b -> c) (h : a -> b),
    myfmap (g := g) f ∘ myfmap h = myfmap (f ∘ h).
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  induction x; [reflexivity|].
  unfold "∘".
  simpl. apply f_equal.
  apply functional_extensionality.
  intros.
  rewrite <- H.
  reflexivity.
Qed.

Fixpoint bind {g a b} (m : FFree g a) (k : a -> FFree g b) : FFree g b :=
  match m with
  | FPure v => k v
  | FImpure gx f => FImpure gx (fun x => bind (f x) k)
  end.

Notation "m >>= k" := (bind m k) (at level 40).
Notation "'return' x" := (FPure x) (at level 40).

Lemma monad_law_1 {g : Set -> Set} {a b : Set} (x : a) (k : a -> FFree g b) : return x >>= k = k x.
Proof. reflexivity. Qed.

Lemma monad_law_2 {g a} (m : FFree g a) : m >>= (fun x => return x) = m.
Proof.
  induction m; [reflexivity|].
  simpl. apply f_equal. apply functional_extensionality.
  apply H.
Qed.

Lemma monad_law_3 {g a b c}
  (m : FFree g a) (k1 : a -> FFree g b) (k2 : b -> FFree g c) :
  (m >>= k1) >>= k2 = m >>= (fun x => (k1 x >>= k2)).
Proof.
  induction m; [reflexivity|].
  simpl. apply f_equal. apply functional_extensionality.
  apply H.
Qed.

Definition etaF {g : Set -> Set} {a : Set} : g a -> FFree g a := (flip FImpure) FPure.

Module State.
  Record t s a := Build { unState : s -> a * s }.

  Definition get {s} : t s s :=
    {| unState := fun s => (s, s) |}.

  Definition put {s} (v : s) : t s unit :=
    {| unState := fun _ => (tt, v) |}.

  Definition runState {s a} : t s a -> s -> a * s := unState s a.
End State.
Definition State := State.t.

Inductive StateEff : Set -> Set -> Set :=
| Get {s} : StateEff s s
| Put {s : Set} : s -> StateEff s unit.

Definition EffState s := FFree (StateEff s).

Definition getEff {s} : EffState s s := etaF Get.
Definition putEff {s : Set} : s -> EffState s unit := etaF ∘ Put.

Axiom axiom : forall A : Type, A.

Definition unStateEff {s a} (m : StateEff s a) : s -> a * s :=
  match m in StateEff s a return s -> a * s with
  | Get => fun s => (s, s)
  | Put v => fun _ => (tt, v)
  end.

Fixpoint runEffState {s a} (m : EffState s a) (st : s) : a * s :=
  match m with
  | FPure v => (v, st)
  | FImpure gx f =>
      let '(v, st') := unStateEff gx st in
      runEffState (f v) st'
  end.

Definition increase (inc : Z) : EffState Z unit :=
  getEff >>= (fun current => putEff (current + inc)).

Compute (runEffState (increase 8) 12).

CoInductive Stream : Set := Seq : nat -> Stream -> Stream.
CoFixpoint from (n:nat) : Stream := Seq n (from (S n)).

Inductive Tree A := empty | node : (Tree A) -> A -> (Tree A) -> Tree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

Notation "e1 ;; e2" := (@bind _ _ _ e1 (fun _ => e2))
    (at level 61, right associativity).

Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).

Notation "' pat <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => match x with pat => c2 end))
                                 (at level 61, pat pattern, c1 at next level, right associativity).

Definition var := nat.

Module exp.
  Inductive t : Set :=
  | Const : Z -> t
  | Var : var -> t
  | Plus : t -> t -> t.
End exp.
Definition exp := exp.t.

Definition vars := var -> option exp.
Definition set (vs : vars) (v : var) (e : exp) : vars :=
  fun v' => if Nat.eqb v v' then Some e else vs v'.

Require Import Coq.Strings.String.
Open Scope string_scope.

Definition Assign (v : var) (e : exp) : EffState vars unit :=
  vs <- getEff ;;
  putEff (set vs v e).

Definition Plus (e1 e2 : exp) : exp := exp.Plus e1 e2.

Definition Const (n : Z) : exp := exp.Const n.

Definition Var (v : var) : exp := exp.Var v.

Definition A := 1%nat.
Definition B := 2%nat.
Definition C := 3%nat.
Definition D := 4%nat.

Definition RustProgram := EffState vars exp.

Definition smallProgram : RustProgram :=
  Assign A (Const 3) ;;
  Assign B (Const 2) ;;
  Assign C (Plus (Var A) (Var B)) ;;
  Assign D (Var C) ;;
  return (Var D).

(* Compute (runEffState smallProgram (fun _ => None)). *)

Module Point.
  Record t := {
      x: f64;
      y: f64;
    }.

  Global Instance Get_x : Notation.Dot "x" := {
    Notation.dot := x
    }.

  Global Instance Get_y : Notation.Dot "y" := {
    Notation.dot := y;
    }.

  Definition set_x f (p : t) :=
    let 'Build_t x y := p in Build_t (f x) y.

  Definition set_y f (p : t) :=
    let 'Build_t x y := p in Build_t x (f y).

    Global Instance Update_x : Notation.Dot "x" := {
      Notation.dot '(Build_t x y) x' := Build_t x' y;
      }.

    Global Instance Update_xf : Notation.Dot "x" := {
      Notation.dot '(Build_t x y) f := Build_t (f x) y;
      }.

    Global Instance Update_fx : Notation.Dot "x" := {
      Notation.dot f '(Build_t x y) := Build_t (f x) y;
      }.

    Global Instance Update_y : Notation.Dot "y" := {
      Notation.dot '(Build_t x y) y' := Build_t x y';
    }.

    Global Instance Update_yf : Notation.Dot "y" := {
      Notation.dot '(Build_t x y) f := Build_t x (f y);
    }.

  (* Global Instance Update_x : Notation.Update "x" := { *)
  (*     Notation.update '(Build_t x y) x' := Build_t x' y; *)
  (*   }. *)

  (*   Global Instance Update_y : Notation.Update "y" := { *)
  (*     Notation.update '(Build_t x y) y' := Build_t x y'; *)
  (*   }. *)
End Point.
Definition Point := Point.t.

Module ImplPoint.
  Definition Self := Point.
  
  Definition origin (_ : unit) : Point :=
    {| Point.y := 0 (* 0.0 *); Point.x := 1 (* 1.0 *); |}.
  
  Global Instance AssociatedFunction_origin :
    Notation.DoubleColon Self "origin" := {
    Notation.double_colon := origin;
  }.
  
  Definition new (x : f64) (y : f64) : Point :=
    {| Point.x := x; Point.y := y; |}.
  
  Global Instance AssociatedFunction_new : Notation.DoubleColon Self "new" := {
    Notation.double_colon := new;
  }.
End ImplPoint.

(* Notation "e x | .. | y ':=u' v" := *)
(*   (Notation.dot y (.. (Notation.dot x e v)..)) (at level 10). *)

Definition testPoint := {| Point.x := 1 ; Point.y := 2 |}.
Module Rectangle.
  Record t := {
      p1 : Point;
      p2 : Point;
    }.

  Global Instance Get_p1 : Notation.Dot "p1" := {
    Notation.dot '(Build_t x0 _) := x0;
    }.
  
  Global Instance Get_p2 : Notation.Dot "p2" := {
    Notation.dot '(Build_t _ x1) := x1;
    }.

  Definition set_p1 f (r : t) :=
    let 'Build_t p1 p2 := r in Build_t (f p1) p2.

  Definition set_p2 f (r : t) :=
    let 'Build_t p1 p2 := r in Build_t p1 (f p2).

    Global Instance Update_p1 : Notation.Dot "p1" := {
      Notation.dot '(Build_t _ p2) p1' := Build_t p1' p2;
      }.
    Global Instance Update_p1f : Notation.Dot "p1" := {
      Notation.dot '(Build_t p1 p2) f := Build_t (f p1) p2;
    }.

    Global Instance Update_p2 : Notation.Dot "p2" := {
      Notation.dot '(Build_t p1 _) p2' := Build_t p1 p2';
      }.
    
    Global Instance Update_p2f : Notation.Dot "p2" := {
      Notation.dot '(Build_t p1 p2) f := Build_t p1 (f p2);
      }.

    Global Instance Update_p2fg : Notation.Dot "p2" := {
      Notation.dot r (f : t -> t) := f r;
      }.

    (* Global Instance Update_p1_x : Notation.Dot "x" := { *)
    (*   Notation.dot '{| Point.x := x ; Point.y := y |} x' := Build_t {| Point.x := x'; Point.y := y |} testPoint; *)
    (*   }. *)

    Set Printing Implicit.
    Global Instance Update_p2_x : @Notation.Dot _ "p2" (forall xx : t, Point -> t) := {
      Notation.dot '(Build_t p1 p2) p := Build_t p1 p;
      }.
       
           
End Rectangle.
Definition Rectangle : Set := Rectangle.t.

Notation "e '.[' x ']' ':=u' v" :=
  (Notation.dot x e v) (at level 0, right associativity).
  
(** Note that we revert the arguments in this notation. *)
Notation "e1 .[ e2 ]" := (Notation.dot e2 e1)
  (at level 0).

Notation "e1 ::[ e2 ]" := (Notation.double_colon e1 e2)
                           (at level 0).

(* Definition testPoint := {| Point.x := 1 ; Point.y := 2 |}. *)


Definition testRect :=
  {|
    Rectangle.p1 := testPoint ;
    Rectangle.p2 := testPoint.["y"] :=u 33 ;
  |}.

Definition test_update_point (p : Point) : Point :=
  Point.set_x (const 22) p.

Definition test_update_point2 (p : Point) : Point :=
  p.["x"] :=u 22.

Definition test_update_rect (r : Rectangle) : Rectangle :=
  Rectangle.set_p1 (const testPoint) r.

Set Printing Implicit.

Definition test_update_rect_inner2 (r : Rectangle) : Rectangle :=
  Rectangle.set_p1 (Point.set_x (const 44)) r.

Definition test_update_rect_inner (r : Rectangle) : Rectangle :=
  r.["p1"] :=u (Point.set_x (const 44)).

Definition test_update_rect_inner3 (r : Rectangle) : Rectangle :=
  r.["p2"] :=u (Point.set_x (const 44)).

(*
Definition test_update_rect_inner3 (r : Rectangle) : Rectangle :=
  r.["p1"].["x"] :=u 44.
*)

Check ((Notation.dot "x" (testRect.["p1"]) 22) : Rectangle).

Set Printing Implicit.


           
(* Compute test_update testPoint. *)


Module ImplRectangle.
  Definition Self := Rectangle.
  
  Definition get_p1 (self : ref Self) : Point := self.["p1"].
  
  Global Instance Method_get_p1 : Notation.Dot "get_p1" := {
    Notation.dot := get_p1;
  }.
  
  Definition area (self : ref Self) : f64 :=
    let '{| Point.x := x1; Point.y := y1; |} := self.["p1"] in
    let '{| Point.x := x2; Point.y := y2; |} := self.["p2"] in
    ((x1.["sub"] x2).["mul"] (y1.["sub"] y2)).["abs"].
  
  Global Instance Method_area : Notation.Dot "area" := {
    Notation.dot := area;
  }.
  
  Definition perimeter (self : ref Self) : f64 :=
    let '{| Point.x := x1; Point.y := y1; |} := self.["p1"] in
    let '{| Point.x := x2; Point.y := y2; |} := self.["p2"] in
    2 (* 2.0 *).["mul"]
      ((x1.["sub"] x2).["abs"].["add"] (y1.["sub"] y2).["abs"]).
  
  Global Instance Method_perimeter : Notation.Dot "perimeter" := {
    Notation.dot := perimeter;
    }.

 
  Definition translate (x : f64) (y : f64) : EffState Self unit :=
    self <- getEff ;;
    putEff (self.["p1"] :=u (Point.set_x (fun v => v + x))) ;;
    self <- getEff ;;
    putEff (self.["p2"] :=u (Point.set_x (fun v => v + x))) ;;
    self <- getEff ;;
    putEff (Rectangle.set_p1 (Point.set_y (fun v => v + y)) self) ;;
    self <- getEff ;;
    putEff (Rectangle.set_p2 (Point.set_y (fun v => v + y)) self).

  Global Instance Method_translate : Notation.Dot "translate" := {
      Notation.dot := translate;
    }.
End ImplRectangle.

Module Identity.
  Record t (a : Set) : Set := {runIdentity : a}.
  Arguments runIdentity {a} _.

  Definition pure {a : Set} (v : a) : t a := {| runIdentity := v |}.
  Definition bind {a b : Set} (ma : t a) (f : a -> t b) : t b :=
    f (runIdentity ma).
  
End Identity.
Definition Identity a := @Identity.t a.

Module LoopT.
  Record t (m : Set -> Set) (a : Set) : Set :=
    {runLoopT : forall {r}, (a -> m r -> m r -> m r) -> m r -> m r -> m r}.

  Arguments runLoopT {m} {a} t {r} _ _ _.

  Definition LoopT m a := LoopT.t m a.

  Definition Loop (a : Set) := LoopT Identity a.

  Global Instance Functor_LoopT m : Functor (LoopT m) := {
      fmap :=
        fun _ _ f ls  =>
          {| LoopT.runLoopT := fun _ fb => LoopT.runLoopT ls (fb ∘ f) |}      
    }.

  Definition pure {m : Set -> Set} {a : Set} (x : a) : LoopT m a :=
    {| LoopT.runLoopT := fun _ f => f x |}.

  Definition bind {m a b} (lma : LoopT m a) (k : a -> LoopT m b) : LoopT m b :=
    {| LoopT.runLoopT :=
        fun _ fb nxtb brkb =>
          LoopT.runLoopT lma
            (fun a nxta brka => LoopT.runLoopT (k a) fb nxta brka) nxtb brkb |}.

  Axiom maxiom : forall (A : Set) (M : Set -> Set), M A.
  Inductive A : Set.
  
  Unset Guard Checking.
  (* init cond adv nxt *)
  (* '{| LoopT.runLoopT := *)
  (*      fun _ yield nxt brk => *)
  (*        if cond init then *)
  (*          yield init nxt brk *)

foldr :: (a -> b -> b) -> b -> t a -> b
(<<<) :: Category cat => cat b c -> cat a b -> cat a c 


f a :: a -> a
(f a <<<) :: cat a a -> cat a a -> cat a a

next :: m (a -> a)
inner :: m (a -> a)
foldr :: ((a -> a) -> (a -> a) -> a -> a) -> (a -> a) -> m (a -> a) -> (a -> a)

instance (Applicative m, Foldable m) => Foldable (LoopT m) where
    {-# INLINE foldr #-}
    foldr f r xs = foldr (<<<) id inner r
      where
        yield a next _ = (f a <<<) <$> next
        inner = runLoopT xs yield (pure id) (pure id)

    {-# INLINE foldl' #-}
    foldl' f r xs = foldl' (!>>>) id inner r
      where
        (!>>>) h g = h >>> (g $!)
        yield a next _ = (flip f a >>>) <$> next
        inner = runLoopT xs yield (pure id) (pure id)

instance (Applicative m, Foldable m) => Traversable (LoopT m) where
    {-# INLINE sequenceA #-}
    sequenceA = foldr (liftA2 cons) (pure continue_)


Definition forLoop
    {M : Set -> Set}
    (init0 : A)
    (cond : A -> bool)
    (adv : A -> A) {struct init}: LoopT M A :=
  let fix go (a : A) (nxt : M A) (brk : M A) : M A :=
    let loop :=
    if cond init then
      forLoop (adv init) cond adv
    else
      {| LoopT.runLoopT := fun _ _ _ brk => brk |}
  in
  LoopT.runLoopT loop
    (fun a nxt brk => if cond a then nxt else brk) (pure init) (pure init).



    
    let fix go (a0 : A) : M A :=
      if cond a0
      then
        
      else next in
    {| LoopT.runLoopT :=
        fun _ fa next brk => |}.

nestedList' :: [(Int, Int)]
nestedList' = toList $ loop $ do  -- 'loop' is just an aid to type inference
    i <- for 0 (<= 3) (+ 1)
    j <- for 0 (<= i) (+ 1)
    return (i, j)
          
    for 0 (<= 3) (+ 1) >>= \i ->
    for 0 (<= i) (+ 1) >>= \j -> return (i, j)

for unroll = \a0 cond adv -> LoopT $ \yield next _ ->
    let go a = unrollFor (fromTypeLit unroll) a cond adv yield go next
    in if cond a0 then go a0 else next
                                      

-- | Iterate forever (or until 'break' is used).
iterate
    :: Unrolling (UnTL n)
    => Unroll n   -- ^ Unrolling factor
    -> a          -- ^ Starting value of iterator
    -> (a -> a)   -- ^ Advance the iterator
    -> LoopT m a
{-# INLINE iterate #-}
iterate unroll = \a0 adv -> LoopT $ \yield next _ ->
    let go a = unrollIterate (fromTypeLit unroll) a adv yield go next
    in go a0

-- | Loop forever without yielding (interesting) values.
forever :: Unrolling (UnTL n) => Unroll n -> LoopT m ()
{-# INLINE forever #-}
forever unroll = iterate unroll () id


for
    :: Unrolling (UnTL n)
    => Unroll n     -- ^ Unrolling factor
    -> a            -- ^ Starting value of iterator
    -> (a -> Bool)  -- ^ Termination condition. The loop will terminate the
                    -- first time this is false. The termination condition
                    -- is checked at the /start/ of each iteration.
    -> (a -> a)     -- ^ Advance the iterator
    -> LoopT m a
{-# INLINE for #-}
for unroll = \a0 cond adv -> LoopT $ \yield next _ ->
    let go a = unrollFor (fromTypeLit unroll) a cond adv yield go next
    in if cond a0 then go a0 else next

instance Unrolling n => Unrolling (S n) where
    {-# INLINE unrollFor #-}
    unrollFor unroll a cond adv yield next brk =
        yield a descend brk
      where
        a' = adv a
        descend | cond a' = unrollFor (predUnroll unroll) a' cond adv yield next brk
                | otherwise = brk

    unrollIterate unroll a adv yield next brk =
        yield a descend brk
      where
      descend = unrollIterate (predUnroll unroll) (adv a) adv yield next brk


class Unrolling (n :: Nat) where
    unrollFor
        :: UnrollInd n
        -> a -> (a -> Bool) -> (a -> a)  -- for parameters
        -> (a -> m r -> m r -> m r) -> (a -> m r) -> m r -> m r  -- un-newtyped LoopT

    unrollIterate
        :: UnrollInd n  -- unrolling factor
        -> a -> (a -> a)  -- iterate parameters
        -> (a -> m r -> m r -> m r) -> (a -> m r) -> m r -> m r  -- un-newtyped LoopT
                                                                        
  Fixpoint iterate 

  Fixpoint loopSum100 (n : nat) : LoopT Identity nat :=
    {| LoopT.runLoopT :=
        fun _ fn nxt brk =>
          (fun a nxta brka =>
             if (a <=? 99)%nat
             then nxta
             else brk) nxt brk .

  

                          
   {runLoopT : (LoopT b m), (m r -> m r -> m r) -> m r -> m r -> m r}.
                         
  LoopT.runLoopT := fun _ fb nxt brk => brk
                        
End LoopT.




Inductive LoopEff

(** to remove *)

Inductive StateEff : Set -> Set -> Set :=
| Get {s} : StateEff s s
| Put {s : Set} : s -> StateEff s unit.

Definition EffState s := FFree (StateEff s).

Definition getEff {s} : EffState s s := etaF Get.
Definition putEff {s : Set} : s -> EffState s unit := etaF ∘ Put.

Axiom axiom : forall A : Type, A.

Definition unStateEff {s a} (m : StateEff s a) : s -> a * s :=
  match m in StateEff s a return s -> a * s with
  | Get => fun s => (s, s)
  | Put v => fun _ => (tt, v)
  end.

Fixpoint runEffState {s a} (m : EffState s a) (st : s) : a * s :=
  match m with
  | FPure v => (v, st)
  | FImpure gx f =>
      let '(v, st') := unStateEff gx st in
      runEffState (f v) st'
  end.

(** /to remove *)


Fixpoint treeLabelWith {A : Set} (t : Tree A) : EffState Stream (Tree (nat * A)) :=
  match t with
  | empty => FPure empty
  | node tl v tr =>
      left_labelled <- treeLabelWith tl ;;
      '(Seq x rest) <- getEff ;;
      putEff rest ;;
      right_labelled <- treeLabelWith tr ;;    
      FPure (node left_labelled (x, v) right_labelled)
  end.


(*
Fixpoint evalExp (vs : vars) (e : exp) {struct e}: option nat :=
  match e with
  | exp.Const n => Some n
  | exp.Var x =>
      match vs x with
      | Some vx => evalExp vs vx
      | None => None
      end
  | exp.Plus e1 e2 =>
      match evalExp vs e1, evalExp vs e2 with
      | Some v1, Some v2 => Some (v1 + v2)
      | _, _ => None
      end
  end.
 *)

Module cmd.
  Inductive t : Type :=
  | Assign : var -> exp -> t
  | Seq : t -> t -> t.
End cmd.
Definition cmd := cmd.t.

Inductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign vars v e : evalCmd vars (cmd.Assign v e) (set vars v e)
| EvalSeq vars1 vars12 vars2 c1 c2 :
  evalCmd vars1 c1 vars12 ->
  evalCmd vars12 c2 vars2 ->
  evalCmd vars1 (cmd.Seq c1 c2) vars2.

Inductive evalExp : vars -> exp -> Z -> Prop :=
| EvalConst vars n : evalExp vars (exp.Const n) n
| EvalVar vars n v e :
  vars v = Some e ->
  evalExp vars e n ->
  evalExp vars (exp.Var v) n
| EvalPlus1 vars n1 n2 e1 e2 :
  evalExp vars e1 n1 ->
  evalExp vars e2 n2 ->
  evalExp vars (Plus e1 e2) (n1 + n2).


Definition testTree : Tree string :=
  node
    (node (node empty "Jim" empty) "Fred" (node empty "Sheila" empty))
    "Alice"
    (node empty "Bob" (node empty "Eve" empty)).

Compute (fst (runEffState (treeLabelWith testTree) (from 1))).

Definition var := nat.

Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if Nat.eqb v v' then n else vs v'.

Inductive tm : Type :=
| C : nat -> tm (* Constant *)
| P : tm -> tm -> tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

Reserved Notation " t '==>' n " (at level 50, left associativity).
Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)
where " t '==>' n " := (eval t n).

Module SimpleArith1.
  Reserved Notation " t '-->' t' " (at level 40).
  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').

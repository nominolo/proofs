(** * Software Foundations, Formally   
      Benjamin C. Pierce
      Version of 9/12/2007

   Before handing in this file with your homework solutions,
   please fill in the names of all members of your group:

     FILL IN HERE

*)

(* ============================================================== *)
(** * LECTURE 1 *)

(** This file develops basic concepts of functional programming,
    logic, operational semantics, lambda-calculus, and
    static type systems, using the Coq proof assistant.  It
    is intended to be "read" in an interactive session with
    Coq under a development environment -- either CoqIDE or
    Proof General.
*)

(** Coq can be seen as a combination of two things:
       - A simple but very expressive PROGRAMMING LANGUAGE
       - A set of tools for stating LOGICAL ASSERTIONS
         (including assertions about the behavior of
         programs) and for assembling evidence of their
         truth.

    We will spend a few lectures with the programming
    language and then begin looking seriously at the logical
    aspects of the system.

    In Coq's programming language, almost nothing is built
    in -- not even numbers!  Instead, it provides powerful
    tools for defining new types of data and functions that
    process and transform them.
*)

(* -------------------------------------------------------------- *)
(** * Days of the week *)

(** Let's start with a very simple example.  The following
    definition tells Coq that we are defining a new set of
    data values.  The set is called [day] and its members
    are [monday], [tuesday], etc.  The lines of the
    definition can be read "[monday] is a [day], [tuesday]
    is a [day], etc." *)
Inductive day : Set :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** Having defined this set, we can write functions that 
    operate on its members. *)
Definition next_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(** There are three ways of "executing" programs written 
    in Coq's programming language... *)

(* First, we can run them interactively: *)
Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday (next_weekday saturday))).

(* Second, we can make an assertion about their results: *)
Lemma check_next_weekday1: 
  (next_weekday (next_weekday (next_weekday saturday)))
  = wednesday.
Proof. simpl. reflexivity. Qed.
(* For now, let's not worry about the details of what's
   going on here.  Roughly, though, we are...
      - making an assertion (that the third weekday after
        saturday is wednesday),
      - giving it a name (check_next_weekday1) in case we
        want to refer to it later, and
      - telling Coq that it can be verified by
        "simplification".
*)

(* Third, we can ask Coq to "extract", from a Definition, a
   program in some other, more mainstream, programming
   language (OCaml or Haskell).  

   This facility is very interesting, since it gives us a
   way to construct FULLY CERTIFIED programs in mainstream
   languages.  This is actually one of the main purposes for
   which Coq has been developed.  However, exploring it
   would take us too far from the main topics of this
   course, so we will say no more about it here.
*)

(* -------------------------------------------------------------- *)
(** * Yes/no answers *)

(** Here is an even simpler type declaration, corresponding 
    to the built-in type of booleans in most programming
    languages.  We will use it heavily in what follows. *)
Inductive yesno : Set :=
  | yes : yesno
  | no : yesno.

Definition swap_yesno (b:yesno) : yesno :=
  match b with
  | yes => no
  | no => yes
  end.

Definition both_yes (b1:yesno) (b2:yesno) : yesno :=
  match b1 with
  | yes => b2
  | no => no
  end.

(* Note that functions like [swap_yesno] are also a data
   values, just like [yes] and [no].  Their types are called
   "function types." 

   The type of [swap_yesno], written [yesno->yesno], is
   pronounced "[yesno] arrow [yesno]."  It can be thought of
   like this: "Given an input of type [yesno], this function
   produces an output of type [yesno]."
*)
Check (swap_yesno).
(* The [Check] command just instructs Coq to print the type
   of an expression. *)

(* The type of [both_yes], written [yesno->yesno->yesno],
   can be thought of like this: "Given two inputs, both of
   type [yesno], this function produces an output of type
   [yesno]." *)
Check (both_yes).

(* EXERCISE: Uncomment and then complete the definitions of
   the following functions, making sure that the assertions
   below each can be verified by Coq. *)

(* This function should return [yes] if either or both of
   its inputs are [yes]. *)
Definition one_yes (b1:yesno) (b2:yesno) : yesno :=
(* SOLUTION *)
  match b1 with
  | yes => yes
  | no => b2
  end.

Lemma check_one_yes1: 
  (one_yes yes no) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_one_yes2: 
  (one_yes no no) = no.
Proof. simpl. reflexivity. Qed.
Lemma check_one_yes3: 
  (one_yes no yes) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_one_yes4: 
  (one_yes yes yes) = yes.
Proof. simpl. reflexivity. Qed.

Definition all3_yes (b1:yesno) (b2:yesno) (b3:yesno) : yesno :=
(* SOLUTION *)
  match b1 with
  | yes => 
      match b2 with
      | yes => b3
      | no => no
      end
  | no => no
  end.

Lemma check_all3_yes1: 
  (all3_yes yes yes yes) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_all3_yes2: 
  (all3_yes no yes yes) = no.
Proof. simpl. reflexivity. Qed.
Lemma check_all3_yes3: 
  (all3_yes yes no yes) = no.
Proof. simpl. reflexivity. Qed.
Lemma check_all3_yes4: 
  (all3_yes yes yes no) = no.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** * Numbers *)

(* The types we defined above are octen called "enumerated
   types" because their definitions explicitly enumerate a
   finite collection of elements. 

   A more interesting way of defining a type is to give a
   collection of INDUCTIVE RULES describing its elements.
   For example, we can define the natural numbers as
   follows:
*)
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

(* This definition can be read: 
     - [O] is a natural number (note that this is the letter
       "O", not the numeral "0")
     - [S] is a CONSTRUCTOR that takes a natural number and
       yields another one -- that is, if [n] is a natural
       number, then [S n] is too.

   The names [nat], [O], and [S] introduced by the
   definition are completely up to us -- there is nothing
   special or built in about these three. *)

(* We can write simple functions that pattern match on
   natural numbers just as we did above: *)
Definition pred (m : nat) : nat :=
  match m with
    | O => O
    |  S m' => m'
  end.

Definition minustwo (m : nat) : nat :=
  match m with
    | O => O
    | S O => O
    | S (S m') => m'
  end.

Eval simpl in (minustwo (S (S (S (S O))))).

(* Note that the constructor [S] has the same type as
   functions like [pred] and [minustwo]... *)
Check pred.
Check minus.
Check S.
(* ...because they can all be applied to a number to yield a
   number.  However, there is a fundamental difference:
   [pred] and [minustwo] come with COMPUTATION RULES --
   e.g., the definition of [pred] says that [pred n] can be
   replaced with [match n with | O => O | S m' => m' end] --
   while [S] has no such behavior attached.  Although it is
   a function in the sense that it can be applied to an
   argument, it does not "do" anything at all!

   What's going on here is that every inductively defined
   set (like [nat], [yesno], and all the others we'll see
   below) is actually a set of EXPRESSIONS.  The definition
   of [nat] says how expressions in the set [nat] can be
   constructed:
      - the expression [O] belongs to the set [nat];
      - if [n] is an expression belonging to the set [nat],
        then [S n] is also an expression belonging to the
        set [nat]; and
      - expressions formed in these two ways are the only
        ones belonging to the set [nat].
   These three conditions are the precise force of the
   [Inductive] declaration.  They imply that
      - [O]
      - [S O]
      - [S (S O)]
      - [S (S (S O))]
      - etc.
   belong to the set [nat], while other expressions like
   [yes] and [S (S no)] do not. *)
 
(** ** Fixpoint definitions *)

(* For most function definitions over numbers, pure pattern
   matching is not enough: we need recursion.  For example,
   to check that a number [n] is even, we may need to
   "recursively" check whether [n-2] is even.  To write such
   functions, we use the keyword [Fixpoint]. *)
Fixpoint even (n:nat) {struct n} : yesno := 
  match n with
  | O        => yes
  | S O      => no
  | S (S n') => even n'
  end.
(* One important thing to note about this definition is the
   declaration [{struct n}] on the first line.  This tells
   Coq to check that we are performing a "structural
   recursion" over the argument [n] -- i.e., that we make
   recursive calls only on strictly smaller values of [n].
   This allows Coq to check that all calls to [even] will
   eventually terminate. *)

Definition odd (n:nat) : yesno := 
  swap_yesno (even n).

Lemma check_odd1: 
  (odd (S O)) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_odd2: 
  (odd (S (S (S (S O))))) = no.
Proof. simpl. reflexivity. Qed.

(* Of course, we can also define multi-argument functions by
   recursion. *)
Fixpoint plus (m : nat) (n : nat) {struct m} : nat :=
  match m with
    | O => n
    | S m' => S (plus m' n)
  end.

(* Adding three to two gives us five, as we'd expect: *)
Eval simpl in (plus (S (S (S O))) (S (S O))).

(* Here's how to visualize the simplification that Coq performs:
      plus (S (S (S O))) (S (S O))
    = S (plus (S (S O)) (S (S O)))    by the second clause of the match
    = S (S (plus (S O) (S (S O))))    by the second clause of the match
    = S (S (S (plus O (S (S O)))))    by the second clause of the match
    = S (S (S (S (S O))))             by the first clause of the match
*)

(* A notational convenience: If two or more arguments have
   the same type, they can be written together.  Here,
   writing [(m n : nat)] is just the same as if we had
   written [(m : nat) (n : nat)]. *)
Fixpoint times (m n : nat) {struct m} : nat :=
  match m with
    | O => O
    | S m' => plus (times m' n) n
  end.

Fixpoint minus (m n : nat) {struct n} : nat :=
  match n with
    | O => m
    | S n' => minus (pred m) n'
  end.

Fixpoint exp (base power : nat) {struct power} : nat :=
  match power with
    | O => S O
    | S p => times base (exp base p)
  end.

Lemma check_times1: 
    (times (S (S (S O))) (S (S (S O))) 
  = (S (S (S (S (S (S (S (S (S O)))))))))).
Proof. simpl. reflexivity. Qed.

(* Such examples are getting a little hard to read!  We could 
   help matters by adding some [Definition]s -- e.g., like this:

      Definition zero  := O.
      Definition one   := (S O).
      Definition two   := (S (S O)).
      Definition three := (S (S (S O))).
      Definition four  := (S (S (S (S O)))).
      Definition five  := (S (S (S (S (S O))))).
      Definition six   := (S (S (S (S (S (S O)))))).

  This would make it easier to ENTER expressions involving
  numbers.  For example, we could now write

      Lemma check_times1': 
          (times three two) 
        = six.

  However, we'd like a little more -- we'd also like for Coq
  to PRINT expressions involving numbers using our short
  names, whenever possible.  We can instruct it to do so by
  using the keyword [Notation] instead of [Definition].
*)
Notation zero  := O.
Notation one   := (S O).
Notation two   := (S (S O)).
Notation three := (S (S (S O))).
Notation four  := (S (S (S (S O)))).
Notation five  := (S (S (S (S (S O))))).
Notation six   := (S (S (S (S (S (S O)))))).
Notation seven := (S (S (S (S (S (S (S O))))))).
Notation eight := (S (S (S (S (S (S (S (S O)))))))).
Notation nine  := (S (S (S (S (S (S (S (S (S O))))))))).
Notation ten   := (S (S (S (S (S (S (S (S (S (S O)))))))))).
Notation eleven:= (S (S (S (S (S (S (S (S (S (S (S O))))))))))).
Notation twelve:= (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))).

Lemma check_times' : 
    (times three two)
  = six.
Proof. simpl. reflexivity. Qed.

(* These notations make it much less painful to see what is
   going on in larger examples: *)
Eval simpl in (exp two three).

(* EXERCISE: Recall that the factorial function is defined
   like this in mathematical notation:
        factorial(0) = 1
        factorial(n) = n * (factorial(n-1))    if n>0
   Translate this into Coq's notation. *)

Fixpoint factorial (n:nat) {struct n} : nat :=
(* SOLUTION *)
  match n with
  | O => one
  | S n' => times n (factorial n')
  end.

Lemma check_factorial1: 
  (factorial three) = six.
Proof. simpl. reflexivity. Qed.
Lemma check_factorial2: 
  (factorial five) = (times ten twelve).
Proof. simpl. reflexivity. Qed.

(* When we say that Coq comes with nothing built-in, we
   really mean it!  Even equality testing has to be
   defined. *)
Fixpoint eqnat (m n : nat) {struct m} : yesno :=
  match m with 
  | O =>
      match n with 
      | O => yes
      | S n' => no
      end
  | S m' =>
      match n with
      | O => no
      | S n' => eqnat m' n'
      end
  end.

(* EXERCISE: Complete the definitions of the following
   comparison functions. *)
Fixpoint lenat (m n : nat) {struct m} : yesno :=
(* SOLUTION *)
  match m with 
  | O =>
    yes
  | S m' =>
      match n with
      | O => no
      | S n' => lenat m' n'
      end
  end.

Lemma check_lenat1: 
  (lenat two two) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_lenat2: 
  (lenat two four) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_lenat3: 
  (lenat four two) = no.
Proof. simpl. reflexivity. Qed.

Definition ltnat (m n : nat) :=
(* SOLUTION *)
  (lenat (S m) n).

Lemma check_ltnat1: 
  (ltnat two two) = no.
Proof. simpl. reflexivity. Qed.
Lemma check_ltnat2: 
  (ltnat two four) = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_ltnat3: 
  (ltnat four two) = no.
Proof. simpl. reflexivity. Qed.


(* -------------------------------------------------------------- *)
(** * Pairs of numbers *)

(* Coq provides a sophisticated module system, to aid in
   organizing large and complex developments.  In this
   course, we won't need most of its features, but one is
   useful: if we enclose a collection of declarations
   between [Module X] and [End X] markers, then, in the
   remainder of the file after the [End], all these
   definitions will be referred to by names like [X.foo]
   instead of just [foo].  This means we are free to define
   the unqualified name [foo] later, which would otherwise
   be an error (a name can only be defined once in a given
   scope).  

   Here, we wrap the definitions for pairs and lists of
   numbers in a module so that, later, we can use the same
   names for generic versions of the same operations. *)
Module NatList.

(* Each constructor of an inductive type can take any number
   of parameters -- none (as with [yes] and [O]), one (as
   with [S]), or more than one: *)
Inductive prodnat : Set :=
  pair : nat -> nat -> prodnat.

(* This declaration can be read: "There is just one way to
   construct a pair of numbers: by applying the constructor
   [pair] to two arguments of type [nat]." *)

(* Some simple function definitions illustrating pattern
   matching on two-argument constructors *)
Definition fst (p : prodnat) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : prodnat) : nat := 
  match p with
  | pair x y => y
  end.
Definition swap_pair (p : prodnat) : prodnat := 
  match p with
  | pair x y => pair y x
  end.

(* It would be nice to be able to use the more standard
   mathematical notation [(x,y)] instead of [pair x y].  We
   can tell Coq we intend to do this with a [Notation]
   declaration. *)
Notation "( x , y )" := (pair x y).

Eval simpl in (fst (three,four)).

Definition fst' (p : prodnat) : nat := 
  match p with
  | (x , y) => x
  end.
Definition snd' (p : prodnat) : nat := 
  match p with
  | (x , y) => y
  end.
Definition swap_pair' (p : prodnat) : prodnat := 
  match p with
  | (x,y) => (y,x)
  end.

(* -------------------------------------------------------------- *)
(** * Lists of numbers *)

(* Generalizing the definition of pairs a little, we can
   describe the type of lists of numbers like this: "A list
   can be either the empty list or else a pair of a number
   and another list." *)
Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* A three-element list: *)
Definition l123 := cons one (cons two (cons three nil)).

(* As with pairs, it is more convenient to write lists in
   familiar mathematical notation.  These two declarations
   allow us to use :: as an infix-cons operator and square
   brackets as an "outfix" notation for constructing
   lists. *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* It is not necessary to deeply understand the [at level
   60, right associativity] part of the first declaration,
   but in case you are interested, here is roughly what's
   going on.  The [right associativity] part tells Coq how
   to parenthesize sequences of uses of [::].  The next
   three declarations mean exactly the same thing. *)
Definition l123'   := one :: (two :: (three :: nil)).
Definition l123''  := one :: two :: three :: nil.
Definition l123''' := [one,two,three].
(* The [at level 60] part tells Coq how to parenthesize
   expressions that involve both :: and some other infix
   operator.  For example, we'll define ++ below as infix
   notation for the [append] function, at level 59.  This
   means that [one :: [two] ++ [three]] will be parsed as
   [one :: ([two] ++ [three])] rather than [(one :: [two])
   ++ [three]]. *)

(* Here are several useful functions for constructing,
   querying, and manipulating lists... *)

Definition hd (l:natlist) : nat :=
  match l with
  | nil => zero  (* arbitrarily *)
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Fixpoint repeat (n count : nat) {struct count} : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) {struct l} : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint nonzeros (l:natlist) {struct l} : natlist :=
  match l with
  | nil => nil 
  | h :: t =>
      match h with
      | O => nonzeros t
      | S h' => h :: (nonzeros t)
      end
  end.

Fixpoint oddmembers (l:natlist) {struct l} : natlist :=
  match l with
  | nil => nil 
  | h :: t =>
      match (odd h) with
      | yes => h :: (oddmembers t)
      | no => oddmembers t
      end
  end.

Fixpoint append (l1 l2 : natlist) {struct l1} : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (append t l2)
  end.

Notation "x ++ y" := (append x y) (at level 59).

Lemma check_append1: 
  [one,two,three] ++ [four,five] = [one,two,three,four,five].
Proof. simpl. reflexivity. Qed.
Lemma check_append2: 
  nil ++ [four,five] = [four,five].
Proof. simpl. reflexivity. Qed.
Lemma check_append3: 
  [one,two,three] ++ nil = [one,two,three].
Proof. simpl. reflexivity. Qed.

(* EXERCISE: Complete the following definitions. *)
Fixpoint countoddmembers (l:natlist) {struct l} : nat :=
(* SOLUTION *)
  match l with
  | nil => O
  | h :: t =>
      match (odd h) with
      | yes => S (countoddmembers t)
      | no => (countoddmembers t)
      end
  end.

Lemma check_countoddmembers1: 
  countoddmembers [one,zero,three,one,four,five] = four.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers2: 
  countoddmembers [zero,two,four] = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers3: 
  countoddmembers nil = zero.
Proof. simpl. reflexivity. Qed.

(* The following exercise illustrates the fact that it
   sometimes requires a little extra thought to satisfy
   Coq's requirement that all Fixpoint definitions be
   "obviously terminating."  There is an easy way to write
   the [alternate] function using just a single
   [match...end], but Coq will not accept it as obviously
   terminating.  Look for a slightly more verbose solution
   with two nested [match...end] constructs.  (Note that
   each [match] must be terminated by an [end].) *)
Fixpoint alternate (l1 l2 : natlist) {struct l1} : natlist :=
(* SOLUTION *)
  match l1 with
  | nil => l2
  | h1 :: t1 =>
      match l2 with
      | nil => l1
      | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
      end
  end.

Lemma check_alternate1: 
  alternate [one,two,three] [four,five,six] 
  = [one,four,two,five,three,six].
Proof. simpl. reflexivity. Qed.
Lemma check_alternate2: 
  alternate [one] [four,five,six] 
  = [one,four,five,six].
Proof. simpl. reflexivity. Qed.
Lemma check_alternate3: 
  alternate [one,two,three] [four] 
  = [one,four,two,three].
Proof. simpl. reflexivity. Qed.

(* SOLUTION *)
Fixpoint snoc (l:natlist) (v:nat) {struct l} : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint reverse (l:natlist) {struct l} : natlist := 
(* SOLUTION *)
  match l with
  | nil    => nil
  | h :: t => snoc (reverse t) h
  end.

Lemma check_reverse1: 
  reverse [one,two,three] = [three,two,one].
Proof. simpl. reflexivity. Qed.
Lemma check_reverse2: 
  reverse nil = nil.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** * EXERCISE: Bags via lists *)

(* EXERCISE: A BAG (often called a MULTISET) is a set where
   each element can appear any finite number of times.  One
   reasonable implementation of bags is to represent a bag
   of numbers as a LIST of numbers.

   Uncomment and complete the definitions. *)

Definition bag := natlist.  

Fixpoint count (v:nat) (s:bag) {struct s} : nat := 
(* SOLUTION *)
  match s with
  | nil => zero
  | h :: t => 
      match eqnat h v with
      | no => count v t
      | yes => S (count v t)
      end
  end.

Lemma check_count1: 
  count one [one,two,three,one,four,one] = three.
Proof. simpl. reflexivity. Qed.
Lemma check_count2: 
  count six [one,two,three,one,four,one] = zero.
Proof. simpl. reflexivity. Qed.

Definition union := 
(* SOLUTION *)
  append.

Lemma check_union1: 
  count one (union [one,two,three] [one,four,one]) = three.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := 
(* SOLUTION *)
  v :: s.

Lemma check_add1: 
  count one (add one [one,four,one]) = three.
Proof. simpl. reflexivity. Qed.
Lemma check_add2: 
  count five (add one [one,four,one]) = zero.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : yesno := 
(* SOLUTION *)
  swap_yesno (eqnat (count v s) zero).

Lemma check_member1: 
  member one [one,four,one] = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_member2: 
  member two [one,four,one] = no.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) {struct s} : bag :=
(* SOLUTION *)
  match s with
  | nil => nil
  | h :: t => 
      match eqnat h v with
      | yes => t
      | no => h :: (remove_one v t)
      end
  end.

Lemma check_remove_one1: 
  count five (remove_one five [two,one,five,four,one]) = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_one2: 
  count five (remove_one five [two,one,four,one]) = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_one3: 
  count four (remove_one five [two,one,four,five,one,four]) = two.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_one4: 
  count five (remove_one five [two,one,five,four,five,one,four]) = one.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) {struct s} : bag :=
(* SOLUTION *)
  match s with
  | nil => nil
  | h :: t => 
      match eqnat h v with
      | yes => remove_all v t
      | no => h :: (remove_all v t)
      end
  end.

Lemma check_remove_all1: 
  count five (remove_all five [two,one,five,four,one]) = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_all2: 
  count five (remove_all five [two,one,four,one]) = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_all3: 
  count four (remove_all five [two,one,four,five,one,four]) = two.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_all4: 
  count five (remove_all five [two,one,five,four,five,one,four]) = zero.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) {struct s1} : yesno :=
(* SOLUTION *)
  match s1 with 
  | nil => yes
  | h1 :: t1 => 
      both_yes (member h1 s2)
               (subset t1 (remove_one h1 s2))
  end.

Lemma check_subset1: 
  subset [one,two] [two,one,four,one] = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_subset2: 
  subset [one,two,two] [two,one,four,one] = no.
Proof. simpl. reflexivity. Qed.

(* ============================================================== *)
(** * LECTURE 2 *)

(* Administrivia:

     - Please send email to cis500@seas, not to me or Leonid
       individually; it is easier for us to respond that way.

     - Is everyone here receiving messages on
       CIS500-002-07C?  If not, please send mail to
       cis500@seas and we will add you.

     - Change of BCP office hours:
          -- This week: tomorrow from 11:30 to 1
          -- Future weeks: TBA
*)

(* Any comments or questions about the material so far? *)

(* -------------------------------------------------------------- *)
(** * Options *)

(* Here is another type definition that is quite useful in
   day-to-day functional programming: *)
Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.  

(* We can use [natoption] as a way of returning "error
   codes" from functions.  For example, suppose we want to
   write a function that returns the nth element of some
   list.  If we give it type [nat->natlist->nat], then we'll
   have to return some number when the list is too short! *)
Fixpoint nth_lessgood (n : nat) (l : natlist) {struct l} : nat :=
  match l with
  | nil => twelve  (* arbitrary! *)
  | a :: l' => if eqnat n O then a else nth_lessgood (pred n) l'
  end.

(* If we give it type [nat->natlist->natoption], then we can
   return [None] when the list is too short and [Some m]
   when the list has enough members and [m] is the one at
   position [n]. *)
Fixpoint nth (n : nat) (l : natlist) {struct l} : natoption :=
  match l with
  | nil => None 
  | a :: l' => if eqnat n O then Some a else nth (pred n) l'
  end.

Lemma check_nth1 :
  nth zero [four,five,six,seven] = Some four.
Proof. simpl. reflexivity. Qed.
Lemma check_nth2 :
  nth three [four,five,six,seven] = Some seven.
Proof. simpl. reflexivity. Qed.
Lemma check_nth3 :
  nth ten [four,five,six,seven] = None.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** * Higher-order functions *)

(* A HIGHER-ORDER function is one that returns a function as
   its result or takes a function as a parameters -- i.e.,
   it treats functions as data. *)

(* In fact, the multiple-argument functions we have already
   seen are simple examples of higher-order functions.  For
   instance, the type of [plus] is [nat->nat->nat]. *)
Check plus.
(* Since [->] associates to the right, this type can also be
   written [nat -> (nat->nat)] -- i.e., the type can be read
   as saying that "[plus] is a one-argument function that
   takes a [nat] and returns a one-argument function that
   takes another [nat] and returns a [nat]."  In the examples
   above, we have always applied [plus] to both of its
   arguments at once, but if we like we can supply just the
   first.  This is called "partial application." *)
Definition plus3 : nat->nat := plus three.

Lemma check_plus3 :
  plus3 four = seven.
Proof. simpl. reflexivity. Qed.

(* More novel are functions that take other functions as
   parameters.  Here is a simple one. *)
Definition doitthreetimes (f:nat->nat) (n:nat) := f (f (f n)).

Lemma check_doitthreetimes1: 
  doitthreetimes minustwo nine = three.
Proof. simpl. reflexivity. Qed.
Lemma check_doitthreetimes2: 
  doitthreetimes plus3 two = eleven.
Proof. simpl. reflexivity. Qed.

(* Here is a more useful one... *)
Fixpoint filter (f: nat->yesno) (l: natlist) {struct l} : natlist :=
  match l with 
  | nil => nil
  | h::t => 
      match f h with
      | yes => h :: (filter f t)
      | no => filter f t
      end
  end.

Lemma check_filter1 :
  filter even [four,five,six,seven] = [four,six].
Proof. simpl. reflexivity. Qed.

(* This gives us, for example, a more concise way to define
   the [countoddmembers] function we saw before. *)
Definition countoddmembers' (l:natlist) : nat := length (filter odd l).

Lemma check_countoddmembers'1: 
  countoddmembers' [one,zero,three,one,four,five] = four.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers'2: 
  countoddmembers' [zero,two,four] = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers'3: 
  countoddmembers' nil = zero.
Proof. simpl. reflexivity. Qed.

(* EXERCISE: Complete the following definition.
Definition countzeros (l:natlist) : nat := 
FILL IN HERE

Lemma check_countzeros1: 
  countzeros [one,zero,three,zero,four,five] = two.
Proof. simpl. reflexivity. Qed.
*)

(* Another very handy higher-order function is [map]. *)
Fixpoint map (f:nat->nat) (l:natlist) {struct l} : natlist := 
  match l with
  | nil    => nil 
  | h :: t => (f h) :: (map f t)
  end.

Lemma check_map1: 
  map minustwo [one,two,three,four,five] = [zero,zero,one,two,three].
Proof. simpl. reflexivity. Qed.
Lemma check_map2: 
  map (plus three) [one,two,three,four] = [four,five,six,seven].
Proof. simpl. reflexivity. Qed.
Lemma check_map3: 
  map S [one,two,three,four] = [two,three,four,five].
Proof. simpl. reflexivity. Qed.

(** ** Anonymous functions *)  

(* Functions in Coq are ordinary data values.  In fact, it
   is possible to construct a function "on the fly" without
   declaring it at the top level and giving it a name; this
   is analogous to the notation we've been using for writing
   down constant lists, etc. *)
Eval simpl in (map (fun n => times n n) [two,zero,three,one]).
(* The expression [fun n => times n n] here can be read "The
   function that, given a number [n], returns [times n n]." *)

Lemma check_doitthreetimes4: 
  doitthreetimes (fun n => minus (times n two) one) two = nine.
Proof. simpl. reflexivity. Qed.

(* ** A different implementation of bags *)

(* Higher-order functions can be used to give an alternate
   implementation of bags.  In this version, a bag is a
   function from numbers to numbers: *)
Definition bagf := nat -> nat.  

(* When applied to an argument n, this function tells you
   how many times n occurs in the bag. *)
Definition countf (v:nat) (s:bagf) : nat := 
  s v.

(* The empty bagf returns zero when queried for the count of
   any element. *)
Definition emptybagf : bagf := (fun n => zero).

Lemma check_emptybagf1: 
  countf three emptybagf = zero.
Proof. simpl. reflexivity. Qed.  

(* As another example, let us construct, by hand, a bagf
   containing the numbers five (once) and six (twice): *)
Definition bagf566 : bagf := 
  fun n =>
    match eqnat n five with
    | yes => one
    | no =>
        match eqnat n six with
        | yes => two
        | no => zero
        end
    end.

Lemma check_bagf566_1: 
  countf five bagf566 = one.
Proof. simpl. reflexivity. Qed.  
Lemma check_bagf566_2: 
  countf six bagf566 = two.
Proof. simpl. reflexivity. Qed.  
Lemma check_bagf566_3: 
  countf seven bagf566 = zero.
Proof. simpl. reflexivity. Qed.  

(* To add an element to a bagf [b], we build a function
   that, when queried for the count for some element [n],
   first asks [b] for its count and then either adds one or
   not, as appropriate. *)
Definition addf (m:nat) (b:bagf) := 
  fun (n:nat) => 
    match eqnat m n with 
    | no => b n
    | yes => S (b n)
    end.

Lemma check_addf1: 
  countf three (addf three emptybagf) = one.
Proof. simpl. reflexivity. Qed.  

(* Here is a function that converts from the old
   representation of bags to the new one. *)
Fixpoint bag2bagf (b:bag) {struct b} : bagf :=
  match b with
  | nil => emptybagf
  | h::t => addf h (bag2bagf t)
  end.

Lemma check_bag2bagf1: 
  countf one (bag2bagf [one,two,three,one,four,one]) = three.
Proof. simpl. reflexivity. Qed.  
Lemma check_bag2bagf2: 
  countf five (bag2bagf [one,two,three,one,four,one]) = zero.
Proof. simpl. reflexivity. Qed.  

(* EXERCISE: Complete the following definitions for this new
   implementation of bags 

Definition unionf (b1 b2 : bagf) := 
  FILL IN HERE

Lemma check_unionf1: 
  countf one (unionf (bag2bagf [one,two,three]) (bag2bagf [one,four,one])) 
  = three.
Proof. simpl. reflexivity. Qed.

Definition remove_onef (v:nat) (s:bagf) : bagf :=
  FILL IN HERE

Lemma check_remove_onef1: 
  countf five (remove_onef five (bag2bagf [two,one,five,four,one])) 
  = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_onef2: 
  countf five (remove_onef five (bag2bagf [two,one,four,one])) 
  = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_onef3: 
  countf four (remove_onef five (bag2bagf [two,one,four,five,one,four])) 
  = two.
Proof. simpl. reflexivity. Qed.
Lemma check_remove_onef4: 
  countf five (remove_onef five (bag2bagf [two,one,five,four,five,one,four])) 
  = one.
Proof. simpl. reflexivity. Qed.

(* THOUGHT PROBLEM (not to be handed in): Can you write a
   [subset] function for this variant of bags? *)
*)

End NatList.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphism *)

(* It happens very common that we need different variants of
   a given function with different type annotations.  As a
   trivial example, we might want a doitthreetimes function
   that works with yesno values instead of numbers. *)
Definition doitthreetimes_yn (f:yesno->yesno) (n:yesno) : yesno := 
  f (f (f n)).

(* Defining all these different variants explicitly is
   annoying and error-prone.  Many programming languages --
   including Coq -- allow us to give a single
   POLYMORPHIC (or GENERIC) definition: *)
Definition doitthreetimes (X:Set) (f:X->X) (n:X) : X := 
  f (f (f n)).

(* This definition adds an extra parameter to the function,
   telling it what SET to expect its third argument to come
   from (and its second argument [f] to accept and return).
   To use [doitthreetimes], we must now apply it an
   appropriate set in addition to its other arguments. *)

Lemma check_doitthreetimes1: 
  doitthreetimes nat minustwo nine = three.
Proof. simpl. reflexivity. Qed.
Lemma check_doitthreetimes2: 
  doitthreetimes nat (plus three) two = eleven.
Proof. simpl. reflexivity. Qed.
Lemma check_doitthreetimes3: 
  doitthreetimes yesno swap_yesno yes = no.
Proof. simpl. reflexivity. Qed.

(* Let's have a look at the type Coq assigns to the generic
   [doitthreetimes]: *)
Check doitthreetimes.
(* The prefix [forall X : Set] corresponds to the first
   parameter [X].  The whole type

      [forall X : Set, (X -> X) -> X -> X]

   can be thought of as a more refined version of the type

      [Set -> (X -> X) -> X -> X]
      
   (that is, it tells us that [doitthreetimes] takes three
   arguments, the first of which is a Set, the second a
   function, etc.); the difference is that the [forall X]
   prefix BINDS the variable [X] in the rest of the type,
   telling us that the second parameter must be a function
   from the set given as the the first parameter to itself,
   etc.  Following this intuition, we might be tempted to
   write it like this

      [X:Set -> (X -> X) -> X -> X]
      
   but you'll find Coq's [forall] notation becomes very
   natural with a little familiarity. *)

(* ---------------------------------------------------------------------- *)
(** ** Polymorphic lists *)

Inductive list (X:Set) : Set :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Definition l123 := cons nat one (cons nat two (cons nat three (nil nat))).

(* It is annoying to have to write all the "nat"s in expressions like
   this, since it seems obvious how to fill them in.  This motivates
   implicit arguments... *)
Definition l123' := cons _ one (cons _ two (cons _ three (nil _))).

(* We can use an implicit argument to define an infix notation for
   cons, as we did above. *)
Notation "x :: y" := (cons _ x y) (at level 60, right associativity).

Definition l000 := zero :: zero :: zero :: nil _.

(* EXERCISE: Fill in the implicit arguments here (i.e., replace all
   occurrences of _ by explicit types): *)
Definition l000l000 := cons _ l000 (cons _ l000 (nil _)).

Notation "[ x , .. , y ]" := (cons _ x .. (cons _ y (nil _)) ..).
Eval simpl in [one,two,three].

(* Side remark: While we're talking about writing less type
   information, we should also mention that Coq can usually
   infer the result types of [Definition]s and
   [Fixpoint]s -- just leave off the result type and the
   colon.  In what follows, we'll generally continue to show
   result types explicitly, for the sake of
   documentation. *)

(* Here is a polymorphic version of the [map] function we
   saw before. *)
Fixpoint map (X:Set) (Y:Set) (f:X->Y) (l:list X) {struct l} : (list Y) := 
  match l with
  | nil    => nil Y
  | h :: t => (f h) :: (map X Y f t)
  end.

Lemma check_map1: 
  map nat nat (plus three) [two,zero,two] = [five,three,five].
Proof. simpl. reflexivity. Qed.
Lemma check_map2: 
  map nat yesno odd [two,one,two,five] = [no,yes,no,yes].
Proof. simpl. reflexivity. Qed.

(* Polymorphic versions of some other useful list processing
   functions... *)
Fixpoint length (X:Set) (l:list X) {struct l} : nat := 
  match l with
  | nil => zero
  | h :: t => S (length X t)
  end.

Fixpoint append (X : Set) (l1 l2 : list X) {struct l1} : (list X) := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (append X t l2)
  end.

Notation "x ++ y" := (append _ x y) (at level 59).

Fixpoint mapappend (X:Set) (Y:Set) (f:X -> list Y) (l:list X) {struct l} 
                   : (list Y) := 
  match l with
  | nil    => nil Y
  | h :: t => (f h) ++ (mapappend X Y f t)
  end.

Lemma check_mapappend1: 
  mapappend nat nat (fun n => [n,n,n]) [one,five,four]
  = [one, one, one, five, five, five, four, four, four].
Proof. simpl. reflexivity. Qed.

Fixpoint snoc (X:Set) (l:list X) (v:X) {struct l} : (list X) := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc _ t v)
  end.

Fixpoint reverse (X:Set) (l:list X) {struct l} : list X := 
  match l with
  | nil    => (nil _)
  | h :: t => snoc _ (reverse _ t) h
  end.

(* EXERCISE: Complete the following function definitions.
   Make sure you understand what is going on in all the test
   cases! Fixpoint filter (X:Set) (test: X->yesno) (l:list X) {struct l} : (list X) :=
  FILL IN HERE

Lemma check_filter1: 
  filter nat even [one,two,three,four] = [two,four].
Proof. simpl. reflexivity. Qed.
Lemma check_filter2: 
  filter (list nat) (fun l => eqnat (length nat l) one) 
         [ [one, two], [three], [four], [five,six,seven], (nil _), [eight] ]
  = [ [three], [four], [eight] ].
Proof. simpl. reflexivity. Qed.
  
Fixpoint repeat (X : Set) (n : X) (count : nat) {struct count} : list X := 
  FILL IN HERE

Lemma check_repeat1: 
  repeat yesno yes five = [yes,yes,yes,yes,yes].
Proof. simpl. reflexivity. Qed.
Lemma check_repeat2: 
  map nat (list yesno) (fun n => repeat yesno no n) [two,one,three] 
  = [ [no,no], [no], [no,no,no] ].
Proof. simpl. reflexivity. Qed.
*)


(* ---------------------------------------------------------------------- *)
(** ** Polymorphic pairs *)
Inductive prod (X Y : Set) : Set :=
  pair : X -> Y -> prod X Y.

Notation "X * Y" := (prod X Y) : type_scope.
Notation "( x , y )" := (pair _ _ x y).

Definition fst (X Y : Set) (p : X * Y) : X := 
  match p with
  | (x, y) => x
  end.

Definition snd (X Y : Set) (p : X * Y) : Y := 
  match p with
  | (x, y) => y
  end.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphic options *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Fixpoint nth (X : Set) (n : nat)
             (l : list X) {struct l} : option X :=
  match l with
  | nil => None _
  | a :: l' => if eqnat n O then Some _ a else nth _ (pred n) l'
  end.

(* Side note: Coq comes with a large "standard library" of
   useful types (and functions over them), including
   booleans, natural numbers, (polymorphic) pairs, lists,
   sets, options, etc.  We're building everything ourselves
   here, for the sake of seeing exactly how it is done, but
   of course expert Coq programmers don't need to start from
   scratch like this every time! *)

(* ---------------------------------------------------------------------- *)
(** * Example: Permutations of a list *)

(* Here is a more serious example of functional programming in Coq.
   The goal is to produce a function [perm] that, given a list,
   returns a list containing all of the permutations of the input
   list.  See if you can understand how it works by starting with the
   [perm] function and then looking at the two auxiliary functions
   that implement its "inner loops." *)

Fixpoint inserteverywhere (X:Set) (v:X) (l:list X) {struct l} 
                          : (list (list X)) := 
  match l with
  | nil => [[v]]
  | h :: t =>
         (v :: l) ::
         (map (list X) (list X) (cons X h) (inserteverywhere X v t))
  end.

Lemma check_inserteverywhere1: 
  inserteverywhere nat three l000 
  = [[three, zero, zero, zero], [zero, three, zero, zero],
     [zero, zero, three, zero], [zero, zero, zero, three]].
Proof. simpl. reflexivity. Qed.

Definition inserteverywhereall (X:Set) (v:X) (l:list (list X)) 
                               : (list (list X)) :=  
  mapappend (list X) (list X) (inserteverywhere X v) l.

Lemma check_inserteverywhereall1: 
  inserteverywhereall nat three l000l000
  = [[three, zero, zero, zero], [zero, three, zero, zero],
     [zero, zero, three, zero], [zero, zero, zero, three],
     [three, zero, zero, zero], [zero, three, zero, zero],
     [zero, zero, three, zero], [zero, zero, zero, three]].
Proof. simpl. reflexivity. Qed.

Fixpoint perm (X: Set) (l:list X) {struct l} : (list (list X)) := 
  match l with
  | nil => [nil X]
  | h :: t =>
      inserteverywhereall X h (perm X t)
  end.

Lemma check_perm1: 
  perm nat l123
  = [[one, two, three], [two, one, three], [two, three, one],
     [one, three, two], [three, one, two], [three, two, one]].
Proof. simpl. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** * Example: Currying and uncurrying *)


Definition curry (X Y Z : Set) (f : X * Y -> Z) : X -> Y -> Z :=
  fun x => fun y => f (x,y).

Definition uncurry (X Y Z : Set) (f : X -> Y -> Z) : (X * Y) -> Z :=
  fun p => 
    match p with
      (x,y) => f x y
    end.

Check curry.
Check uncurry.



(* ---------------------------------------------------------------------- *)
(** * Non-structural recursion *)

(* Note: This section was not covered in class.  We may come back to
   it later. *)

(* Notes:
     - the termination parameter is the auxiliary 'c'
       argument ('c' for counter)
     - the annotation for the result type is needed because
       of the way that all_interleavings_aux is called in
       the body -- it's a little too complicated for Coq to
       work out what the result type must be
*)
Fixpoint all_interleavings_aux 
            (c:nat) (X:Set) (l1 : list X) (l2 : list X) {struct c} 
            : list (list X) :=
  match c with
  | O => nil _  (* If out of steam, return something silly *)
  | S c' =>
    match l1 with
    | nil => l2 :: (nil _)
    | h1 :: t1 =>
        match l2 with
        | nil => l1 :: (nil _)
        | h2 :: t2 => 
              (map _ _ (cons _ h1) (all_interleavings_aux c' _ t1 l2))
           ++ (map _ _ (cons _ h2) (all_interleavings_aux c' _ l1 t2))
        end
    end
  end.

Definition all_interleavings (X:Set) (l1 : list X) (l2 : list X) : (list (list X)) :=
  all_interleavings_aux
    (length _ (l1 ++ l2))
    X
    l1
    l2.

Lemma check_all_interleavings1: 
  all_interleavings _ [one,two] [three,four]
  = [[one, two, three, four], [one, three, two, four],
     [one, three, four, two], [three, one, two, four],
     [three, one, four, two], [three, four, one, two]].
Proof. simpl. reflexivity. Qed.


(* ============================================================== *)
(** * LECTURE 3 *)

(* We've now seen quite a bit of Coq's facilities for functional
   programming.  It is time to start looking at how we can REASON in
   Coq about the programs we've written. *)

(* ---------------------------------------------------------------------- *)
(** * Reasoning by "partial evaluation" *)

(* Some facts about functions can be proved simply by unfolding their
   recursive definitions. *)

(* For example, the fact that zero is a neutral element for plus on
   the left can be proved just by observing that [plus zero n] reduces
   to [n] no matter what [n] is, since the definition of [plus] is
   recursive in its first argument. *)
Lemma zero_plus : forall n:nat, 
  plus zero n = n.
Proof.
  simpl. reflexivity. 
Qed.

(* Here are some more facts that can be proved by the same "partial
   evaluation" technique... *)
Lemma one_plus : forall n:nat, 
  plus one n = S n.
Proof.
  simpl. reflexivity. 
Qed.

Lemma zero_times : forall n:nat, 
  times zero n = zero.
Proof.
  simpl. reflexivity.
Qed.

Lemma one_times : forall n:nat, 
  times one n = n.
Proof.
  simpl. reflexivity.
Qed.

Lemma two_times : forall n:nat, 
  times two n = plus n n.
Proof.
  simpl. reflexivity.
Qed.

Lemma nil_append : forall X:Set, forall l:list X, 
  append _ (nil _) l = l.
Proof.
  simpl. reflexivity.
Qed.

Lemma const_append : forall l:list nat, 
  append nat [three,four] l = three :: four :: l.
Proof.
  simpl. reflexivity.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** The [intros] and [rewrite] tactics *)

(* It will often happen that the goal we're trying to prove
   begins with some kind of quantifier (e.g., "for all
   numbers n, ...") or hypothesis ("assuming m=n, ...").  

   In such situations, it is convenient to be able to move
   the "left-hand part" out of the way and concentrate on
   the "right-hand part."  The [intros] tactic permits us to
   do this, by moving a quantifier or hypothesis from the
   goal to a "context" of current assumptions.

   For example, here is a slightly different -- perhaps
   slightly clearer -- proof of one of the facts we proved a
   minute ago.
*)
Lemma zero_plus' : forall n:nat, 
  plus zero n = n.
Proof.
  intros n. simpl. reflexivity. 
Qed.

(* Here is a more interesting proof that involves moving a
   hypothesis into the context and then APPLYING this
   hypothesis to rewrite the rest of the goal. *)
Lemma plus_id_common : forall m n:nat, 
  m = n -> plus m n = plus n m.    (* -> is pronounced "implies" *)
Proof.
  intros m n.     (* move both quantifiers into the context at once *)
   intros eq.     (* move the hypothesis into the context *)
   rewrite <- eq. (* Rewrite the goal according to the hypothesis *)
   reflexivity. 
Qed.

(* The [->] annotation in [rewrite ->] tells Coq to apply the rewrite
   from left to right.  To rewrite from right to left, you can use
   [rewrite <-].  Try this in the above proof and see what changes.

   Note that this has nothing to do with the use of the symbol [->] to
   denote implication in the statement of the lemma. *)

Lemma plus_id_exercise : forall m n o : nat, 
  m = n -> n = o -> plus m n = plus n o.
Proof.
  intros m n o.
  intros H H'.
  rewrite H.  rewrite H'.
  reflexivity.
Qed.

(* We can also use the [rewrite] tactic with a previously proved lemma
   instead of a hypothesis from the context. *)
Lemma times_zero_plus : forall m n : nat, 
  times (plus zero n) m = times n m.
Proof.
  intros m n. 
   rewrite -> zero_plus'. reflexivity.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Case analysis *)

(* Of course, not everything can be proved by simple calculation: In
   general, unknown, hypothetical values (arbitrary numbers, yesno
   values, lists, etc.) can show up in the "head position" of
   functions that we want to reason about, blocking simplification.
   For example, if we try to prove the following fact using the
   [simpl] tactic as above, we get stuck.
 *)
Lemma plus_one_neq_zero_firsttry : forall n,
  eqnat (plus n one) zero = no.
Proof.
  intros n. simpl.  (* does nothing! *)
Admitted.
(* The [Admitted] command tells Coq that we want to give up trying to
   prove this lemma and just accept it as a given.  This can be useful
   for developing longer proofs, since we can state subsidiary facts
   that we believe will be useful for making some larger argument, use
   [Admitted] to accept them on faith for the moment, and continue
   thinking about the larger argument until we are sure it is working;
   then we can go back and fill in the proofs we skipped.  Be careful,
   though: Every time you say [Admitted] you are leaving a door open
   for total nonsense to enter your nice rigorous formally checked
   world! *)

(* What we need is to be able to consider the possible forms of [n]
   separately: if it is [O], then we can calculate the final result of
   [eqnat (plus n one) zero] and check that it is, indeed, [no].  And
   if [n = S(n')] for some [n'], then, although we don't know exactly
   what number [plus n one] yields, we can calculate that, at least,
   it begins with one [S], and this is enough to calculate that,
   again, [eqnat (plus n one) zero] will yield [no]. 

   The tactic that tells Coq to consider the cases where [n = O] and
   where [n = S n'] separately is called [destruct].  It generates TWO
   subgoals, which we must then prove, separately, in order to get Coq
   to accept the Lemma as proved.  (There is no special command for
   moving from one subgoal to the other.  When the first subgoal has
   been proved, it just disappears and we are left with the other "in
   focus.") *)
Lemma plus_one_neq_zero : forall n,
  eqnat (plus n one) zero = no.
Proof.
  intros n. destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma swap_swap : forall b : yesno,
  swap_yesno (swap_yesno b) = b.
Proof.
  intros b. destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma bothyes_ex : forall b : yesno,
  both_yes b no = no.
Proof.
  intro b. destruct b ; simpl ; reflexivity.
Qed.

Lemma all3_spec : forall b c : yesno,
    one_yes 
      (both_yes b c) 
      (one_yes (swap_yesno b)
               (swap_yesno c))
  = yes.
Proof.
  intros b c.
  destruct c; destruct b; simpl; reflexivity.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Induction on numbers *)

(* We proved above that zero is a neutral element for plus on the left
   using a simple partial evaluation argument.  The fact that it is
   also a neutral element on the RIGHT cannot be proved in the same
   simple way... *)
Lemma plus_zero_firsttry : forall n:nat, 
  plus n zero = n.
Proof.
  intros n.
   simpl. (* Does nothing! *) 
Admitted.  

(* Case analysis gets us a little further, but not all the way. *)
Lemma plus_zero_secondtry : forall n:nat, 
  plus n zero = n.
Proof.
  intros n. destruct n.
    simpl. reflexivity. (* so far so good... *)
    simpl.              (* ...but here we are stuck again *)
Admitted.  

(* To prove such facts -- indeed, to prove most interesting facts
   about numbers, lists, and other inductively defined sets -- we need
   a more powerful reasoning principle: INDUCTION.

   Recall (from high school) the principle of induction over
   natural numbers:

     If [P(n)] is some proposition involving a natural number n, and
     we want to show that P holds for ALL numbers n, we can reason
     like this:

        - show that [P(O)] holds
        - show that, if [P(n)] holds, then so does [P(S n)]
        - conclude that [P(n)] holds for all n.

   In Coq, the style of reasoning is "backwards": we begin with the
   goal of proving [P(n)] for all n and break it down (by applying the
   [induction] tactic) into two separate subgoals: first showing P(O)
   and then showing [P(n) -> P(S n)]. *)
Lemma plus_zero : forall n:nat, 
  plus n zero = n.
Proof.
  intros n. induction n.      
    (* First subgoal: *)
    simpl. reflexivity.
    (* Second subgoal: *)
    simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma times_zero : forall n:nat, times n zero = zero.
Proof.
  intro n. induction n.
  reflexivity. simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_one : forall n:nat, 
  plus n one = S n.
Proof.
  intros n. induction n. 
    simpl. reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma times_one : forall n:nat, 
  times n one = n.
Proof.
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn. rewrite -> plus_one. reflexivity.
Qed.

(* The precise way we state definitions can often have a large
   influence on proofs.  For example, suppose that we had defined the
   [times] function in a slightly different way (reversing the order
   of arguments to [plus] on the last line): *)
Fixpoint times' (m n : nat) {struct m} : nat :=
  match m with
    | O => O
    | S m' => plus n (times' m' n)
  end.

(* Now we cannot use straightforward simplification to prove the
   [one_times] lemma (try it yourself and see what goes wrong!);
   instead, we must use induction. *)
Lemma one_times' : forall n:nat, 
  times' one n = n.
Proof.
(* Works, too: *)
(*   intros n. destruct n. reflexivity. *)
(*   simpl. rewrite -> plus_zero. reflexivity. *)
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> plus_zero. reflexivity.
Qed.
(* Note, too, that we applied a rewrite here justified by a previously
   proved lemma ([plus_zero]) rather than an assumption in the
   immediate context. *)
(* FIX: maybe comment not needed? *)

Lemma plus_assoc : forall m n p : nat, 
  plus m (plus n p) = plus (plus m n) p.   
Proof.
  intros m n p. induction m.
    simpl. reflexivity.
    simpl. rewrite -> IHm. reflexivity.
Qed.

(* An exercise to be worked together: *)
Lemma minus_n_n_zero : forall n,
  minus n n = zero.
Proof.
  intro n. induction n.
  reflexivity. 
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma dist_succ_plus : forall m n : nat, 
  plus m (S n) = S (plus m n).
Proof. 
  intros m n. induction m.
  simpl. reflexivity.
  simpl. rewrite IHm. trivial.
Qed.

Lemma plus_commut : forall m n : nat, 
  plus m n = plus n m.
Proof.
  intros m n.
  induction m. simpl. rewrite plus_zero. trivial.
  simpl. rewrite dist_succ_plus. rewrite IHm. trivial.
Qed.

(* EXERCISE: Which of the following lemmas require induction in their
   proofs?  (See if you can predict in advance, before trying with
   Coq.) *)
Lemma S_neq_zero : forall n:nat,
  eqnat (S n) zero = no.
Proof.
  intro n. simpl. trivial.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Induction on lists *)

(* We can do induction not just on numbers, but on any inductively
   defined type: Coq generates an appropriate induction principle when
   it processes the [Inductive] declaration.

   Here is the induction principle for (polymorphic) lists:

     If X is a type and [P l] is some proposition involving a list l
     of type [list X], and we want to show that P holds for all l, we
     can reason like this:

        - show that P (nil X) holds
        - show that, for any element x:X and any list l : list X, if
          [P l] holds, then so does [P (x::l)]
        - conclude that [P l] holds for all lists l.
*)
Lemma append_assoc : forall X:Set, forall l1 l2 l3 : list X, 
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.   
Proof.
  intros X l1 l2 l3. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma append_nil : forall X:Set, forall l : list X, 
  l ++ (nil _) = l.   
Proof.
  intros X l. induction l.
  simpl. trivial.
  simpl. rewrite IHl. trivial.
Qed.

(* An exercise to be worked together: *)
Lemma length_append : forall X : Set,
                      forall l1 l2 : list X,
  length _ (l1 ++ l2) = plus (length _ l1) (length _ l2).,
Proof.
  intros X l1 l2.
  induction l1. simpl. trivial.
  simpl. rewrite IHl1. reflexivity.
Qed.

(* Now let's try something a little more intricate: proving that
   reversing a list does not change its length.  Our first attempt at
   this proof gets stuck in the successor case... *)
Lemma length_reverse_firsttry : 
  forall X : Set, forall l : list X,
  length _ l = length _ (reverse _ l).
Proof.
  intros X l. induction l.
    simpl. reflexivity.
    simpl. (* Here we get stuck: the goal is an equality
           involving [snoc], but we don't have any equations
           in either the immediate context or the global
           environment that have anything to do with
           [snoc]! *)
Admitted.

(* So let's take the equation about snoc that would have enabled us to
   make progress and prove it as a separate lemma. *)
Lemma length_snoc : forall X : Set,
                    forall v : X,
                    forall l : list X,
  length _ (snoc _ l v) = S (length _ l).
Proof.
  intros X v l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl. reflexivity.
Qed. 

(* Now we can complete the original proof. *)
Lemma length_reverse : forall X : Set,
                       forall l : list X,
  length _ l = length _ (reverse _ l).
Proof.
  intros X l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> length_snoc. rewrite -> IHl.  reflexivity.
Qed. 

(* An exercise to work together: Show that [map] and [reverse]
   "commute" in a similar way. *)
Lemma map_snoc : forall X Y : Set, 
                 forall f : X->Y, 
                 forall l : list X,
                 forall v : X,
  map X Y f (snoc X l v) = snoc Y (map X Y f l) (f v).
Proof.
  intros X Y f l v. induction l.
    simpl. trivial.
    simpl. rewrite IHl. trivial.
Qed.

Lemma map_reverse : forall X Y : Set, 
                    forall f : X->Y,
                    forall s : list X,
  map X Y f (reverse X s) = reverse Y (map X Y f s).
Proof. 
  intros B Y f s.  induction s.
    simpl. trivial.
    simpl. rewrite map_snoc. rewrite IHs. trivial.
Qed.
    

(* Exercises... *)

Lemma reverse_snoc : 
  forall X : Set, forall l : list X, forall v : X,
    reverse _ (snoc _ l v) = v :: reverse _ l.
Proof.
  intros X l v.  induction l. simpl. trivial.
  simpl. rewrite IHl. simpl. trivial.
Qed.

Lemma reverse_reverse : forall X : Set, 
                        forall s : list X,
  reverse X (reverse X s) = s.
Proof.
  intros X s.  induction s.
    trivial.
    simpl. rewrite reverse_snoc. rewrite IHs. trivial.
Qed.

Lemma append_snoc : 
  forall X : Set, forall l1 l2 : list X, forall v : X,
    snoc _ (l1 ++ l2) v = l1 ++ snoc _ l2 v.
Proof.
  intros X l1 l2 v.  induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. trivial.
Qed.

Lemma reverse_append : forall X : Set, 
                       forall l1 l2 : list X,
  reverse _ (l1 ++ l2) = (reverse _ l2) ++ (reverse _ l1).
Proof.
  intros X l1 l2. induction l1.
    simpl. rewrite append_nil. trivial.
    simpl. rewrite IHl1. rewrite append_snoc. trivial.
Qed.

(* EXERCISE: 
     - Find a non-trivial equation involving cons (::), snoc, and
       append (++).
     - Prove it.
FILL IN HERE
*)


(* There is a short solution to the next exercise.  If you find
   yourself getting tangled up, step back and try to look for a
   simpler way... *)
Lemma append_assoc4 : forall X : Set,
                      forall l1 l2 l3 l4 : list X,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros X l1 l2 l3 l4.
  rewrite append_assoc. rewrite append_assoc. reflexivity.
Qed.


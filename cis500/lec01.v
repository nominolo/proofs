(** * Software Foundations, Formally   
      Benjamin C. Pierce
      Version of 9/4/2007

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
       - A set of tools for stating LOGICAL ASSERTIONS and
         constructing (and verifying) evidence of their
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
   way to construct FULLY VERIFIED programs in mainstream
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
(* [Check] just instructs Coq to print the type of an
   expression. *)

(* The type of [both_yes], written [yesno->yesno->yesno],
   can be thought of like this: "Given two inputs, both of
   type [yesno], this function produces an output of type
   [yesno]." *)
Check (both_yes).

(* EXERCISE: Uncomment and then complete the definitions of
   the following functions, making sure that the assertions
   below each can be verified by Coq. *)

Definition one_yes (b1:yesno) (b2:yesno) : yesno :=
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

Definition all3_yes (b1:yesno) (b2:yesno) (b3:yesno) : yesno :=
  both_yes b1 (both_yes b2 b3).

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

(* The types we defined above are often called "enumerated
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
     - [S] is a function that takes a natural number and
       gives us another one -- that is, if [n] is a natural
       number, then [S n] is too.
*)

(* We can write simple functions that pattern match on
   natural numbers just as we did above: *)
Definition pred (m : nat) : nat :=
  match m with
    | O => O
    | S m' => m'
  end.

Definition minustwo (m : nat) : nat :=
  match m with
    | O => O
    | S O => O
    | S (S m') => m'
  end.

Eval simpl in (minustwo (S (S (S (S O))))).

(* But for other kinds of function definitions, just pattern
   matching is not enough: we need something new.  For
   example, to check that a number [n] is even, we may need
   to "recursively" check whether [n-2] is even.  To write
   such functions, we use the keyword [Fixpoint].
*)
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

(* A notational convenience: If two or more arguments have
   the same type, they can be written together.  Here,
   writing [(m n : nat)] is just the same as if we had
   written [(m : nat) (n : nat)]. *)
Fixpoint times (m n : nat) {struct m} : nat :=
  match m with
    | O => O
    | S m' => plus n (times m' n)
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
   Translate this into Coq's notation.*)

Fixpoint factorial (n:nat) {struct n} : nat :=
  match n with
  | O    => S O
  | S n' => times n (factorial n')
  end. 

Lemma check_factorial1: 
  (factorial three) = six.
Proof. simpl. reflexivity. Qed.
Lemma check_factorial2: 
  (factorial five) = (times ten twelve).
Proof. compute. reflexivity. Qed.


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
  match m with
  | O => yes
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
  both_yes (lenat m n) (swap_yesno (eqnat m n)).  

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

(* The [right associativity] part of the first declaration
   tells Coq how to parenthesize sequences of uses of [::].
   The next three declarations mean exactly the same
   thing. *)
Definition l123'   := one :: (two :: (three :: nil)).
Definition l123''  := one :: two :: three :: nil.
Definition l123''' := [one,two,three].

(* Some useful functions for constructing, querying, and
   manipulating lists... *)

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
  length (oddmembers l).

Lemma check_countoddmembers1: 
  countoddmembers [one,zero,three,one,four,five] = four.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers2: 
  countoddmembers [zero,two,four] = zero.
Proof. simpl. reflexivity. Qed.
Lemma check_countoddmembers3: 
  countoddmembers nil = zero.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) {struct l1} : natlist :=
  match l1 with
  | nil => l2
  | h :: t => 
      match l2 with
      | nil => h :: t
      | h' :: t' => h :: h' :: alternate t t'
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

Fixpoint reverse (l:natlist) {struct l} : natlist := 
  match l with
  | nil => nil
  | h :: t => append (reverse t) [h]
  end.

Lemma check_reverse1: 
  reverse [one,two,three] = [three,two,one].
Proof. simpl. reflexivity. Qed.
Lemma check_reverse2: 
  reverse nil = nil.
Proof. simpl. reflexivity. Qed.

(* -------------------------------------------------------------- *)
(** * EXERCISE: bags via lists *)

(* EXERCISE: A BAG (often called a MULTISET) is a set where
   each element can appear any finite number of times.  One
   reasonable implementation of bags is to represent a bag
   of numbers as a LIST of numbers.

   Uncomment and complete the definitions. *)

Definition bag := natlist.  

Fixpoint count (v:nat) (s:bag) {struct s} : nat := 
  match s with
  | nil => O
  | h :: t => 
    match eqnat h v with
    | yes => S (count v t)
    | no => count v t
    end
  end.

Lemma check_count1: 
  count one [one,two,three,one,four,one] = three.
Proof. simpl. reflexivity. Qed.
Lemma check_count2: 
  count six [one,two,three,one,four,one] = zero.
Proof. simpl. reflexivity. Qed.

Definition union := 
  append.

Lemma check_union1: 
  count one (union [one,two,three] [one,four,one]) = three.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := 
  v :: s.

Lemma check_add1: 
  count one (add one [one,four,one]) = three.
Proof. simpl. reflexivity. Qed.
Lemma check_add2: 
  count five (add one [one,four,one]) = zero.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : yesno := 
  ltnat zero (count v s).

Lemma check_member1: 
  member one [one,four,one] = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_member2: 
  member two [one,four,one] = no.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) {struct s} : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match eqnat h v with
    | yes => t
    | no => h :: remove_one v t
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
  match s with
  | nil => nil
  | h :: t =>
    match eqnat h v with
    | yes => remove_all v t
    | no => h :: remove_all v t
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
  match s1 with
  | nil => yes
  | h :: t =>
    match member h s2 with
    | no => no
    | yes => subset t (remove_one h s2)
    end
  end.

Lemma check_subset1: 
  subset [one,two] [two,one,four,one] = yes.
Proof. simpl. reflexivity. Qed.
Lemma check_subset2: 
  subset [one,two,two] [two,one,four,one] = no.
Proof. simpl. reflexivity. Qed.


(* -------------------------------------------------------------- *)
(** * Options *)
Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(* Now we have a better way to define hd: *)
Definition better_hd (l:natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

End NatList.


(** * Software Foundations, Formally   
      Benjamin C. Pierce
      Version of 9/21/2007

   Before handing in this file with your homework solutions, please
   fill in the names of all members of your group:

     FILL IN HERE

   Also, please tell us roughly how many person-hours you spent on
   this assignment (i.e., if you worked in a group, give us the SUM of
   the number of hours spent by each person individually).

     FILL IN HERE

*)

(* ====================================================================== *)
(** * LECTURE 1 *)

(** This file develops basic concepts of functional programming,
    logic, operational semantics, lambda-calculus, and static type
    systems, using the Coq proof assistant.  It is intended to be
    "read" in an interactive session with Coq under a development
    environment -- either CoqIDE or Proof General.
*)

(** Coq can be seen as a combination of two things:
       - A simple but very expressive PROGRAMMING LANGUAGE
       - A set of tools for stating LOGICAL ASSERTIONS (including
         assertions about the behavior of programs) and for assembling
         evidence of their truth.

    We will spend a few lectures with the programming language and
    then begin looking seriously at the logical aspects of the system.

    In Coq's programming language, almost nothing is built in -- not
    even numbers!  Instead, it provides powerful tools for defining
    new types of data and functions that process and transform them.
*)

(* -------------------------------------------------------------- *)
(** * Days of the week *)

(** Let's start with a very simple example.  The following definition
    tells Coq that we are defining a new set of data values.  The set
    is called [day] and its members are [monday], [tuesday], etc.  The
    lines of the definition can be read "[monday] is a [day],
    [tuesday] is a [day], etc." *)
Inductive day : Set :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** Having defined this set, we can write functions that operate on
    its members. *)
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

(** There are three ways of "executing" programs written in Coq's
    programming language... *)

(* First, we can run them interactively: *)
Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday (next_weekday saturday))).

(* Second, we can make an assertion about their results: *)
Lemma check_next_weekday1: 
  (next_weekday (next_weekday (next_weekday saturday)))
  = wednesday.
Proof. simpl. reflexivity. Qed.
(* For now, let's not worry about the details of what's going on here.
   Roughly, though, we are...
      - making an assertion (that the third weekday after saturday is
        wednesday),
      - giving it a name (check_next_weekday1) in case we want to
        refer to it later, and
      - telling Coq that it can be verified by "simplification".
*)

(* Third, we can ask Coq to "extract", from a Definition, a program in
   some other, more mainstream, programming language (OCaml or
   Haskell).

   This facility is very interesting, since it gives us a way to
   construct FULLY CERTIFIED programs in mainstream languages.  This
   is actually one of the main purposes for which Coq has been
   developed.  However, exploring it would take us too far from the
   main topics of this course, so we will say no more about it here.
*)

(* -------------------------------------------------------------- *)
(** * Yes/no answers *)

(** Here is an even simpler type declaration, corresponding to the
    built-in type of booleans in most programming languages.  We will
    use it heavily in what follows. *)
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

(* Note that functions like [swap_yesno] are also a data values, just
   like [yes] and [no].  Their types are called "function types."

   The type of [swap_yesno], written [yesno->yesno], is pronounced
   "[yesno] arrow [yesno]."  It can be thought of like this: "Given an
   input of type [yesno], this function produces an output of type
   [yesno]." 
*)
Check (swap_yesno).
(* The [Check] command just instructs Coq to print the type of an
   expression. *)

(* The type of [both_yes], written [yesno->yesno->yesno], can be
   thought of like this: "Given two inputs, both of type [yesno], this
   function produces an output of type [yesno]." *)
Check (both_yes).

(* Exercise: Uncomment and then complete the definitions of the
   following functions, making sure that the assertions below each can
   be verified by Coq. *)

(* This function should return [yes] if either or both of its inputs
   are [yes]. *)
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

(* The types we defined above are octen called "enumerated types"
   because their definitions explicitly enumerate a finite collection
   of elements.

   A more interesting way of defining a type is to give a collection
   of INDUCTIVE RULES describing its elements.  For example, we can
   define the natural numbers as follows:
*)
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

(* This definition can be read: 
     - [O] is a natural number (note that this is the letter "O", not
       the numeral "0")
     - [S] is a CONSTRUCTOR that takes a natural number and yields
       another one -- that is, if [n] is a natural number, then [S n]
       is too.

   The names [nat], [O], and [S] introduced by the definition are
   completely up to us -- there is nothing special or built in about
   these three. *)

(* We can write simple functions that pattern match on natural numbers
   just as we did above: *)
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

(* Note that the constructor [S] has the same type as functions like
   [pred] and [minustwo]... *)
Check pred.
Check minustwo.
Check S.
(* ...because they can all be applied to a number to yield a number.
   However, there is a fundamental difference: [pred] and [minustwo]
   come with COMPUTATION RULES -- e.g., the definition of [pred] says
   that [pred n] can be replaced with [match n with | O => O | S m' =>
   m' end] -- while [S] has no such behavior attached.  Although it is
   a function in the sense that it can be applied to an argument, it
   does not "do" anything at all!

   What's going on here is that every inductively defined set (like
   [nat], [yesno], and all the others we'll see below) is actually a
   set of EXPRESSIONS.  The definition of [nat] says how expressions
   in the set [nat] can be constructed:
      - the expression [O] belongs to the set [nat];
      - if [n] is an expression belonging to the set [nat], then [S n]
        is also an expression belonging to the set [nat]; and
      - expressions formed in these two ways are the only ones
        belonging to the set [nat].
   These three conditions are the precise force of the [Inductive]
   declaration.  They imply that
      - [O]
      - [S O]
      - [S (S O)]
      - [S (S (S O))]
      - etc.
   belong to the set [nat], while other expressions like [yes] and
   [S (S no)] do not. *)
 
(** ** Fixpoint definitions *)

(* For most function definitions over numbers, pure pattern matching
   is not enough: we need recursion.  For example, to check that a
   number [n] is even, we may need to "recursively" check whether
   [n-2] is even.  To write such functions, we use the keyword
   [Fixpoint]. *)
Fixpoint even (n:nat) {struct n} : yesno := 
  match n with
  | O        => yes
  | S O      => no
  | S (S n') => even n'
  end.
(* One important thing to note about this definition is the
   declaration [{struct n}] on the first line.  This tells Coq to
   check that we are performing a "structural recursion" over the
   argument [n] -- i.e., that we make recursive calls only on strictly
   smaller values of [n].  This allows Coq to check that all calls to
   [even] will eventually terminate. *)

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

(* A notational convenience: If two or more arguments have the same
   type, they can be written together.  Here, writing [(m n : nat)] is
   just the same as if we had written [(m : nat) (n : nat)]. *)
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

(* Such examples are getting a little hard to read!  We could help
   matters by adding some [Definition]s -- e.g., like this:

      Definition zero  := O.
      Definition one   := (S O).
      Definition two   := (S (S O)).
      Definition three := (S (S (S O))).
      Definition four  := (S (S (S (S O)))).
      Definition five  := (S (S (S (S (S O))))).
      Definition six   := (S (S (S (S (S (S O)))))).

  This would make it easier to ENTER expressions involving numbers.
  For example, we could now write

      Lemma check_times1': 
          (times three two) 
        = six.

  However, we'd like a little more -- we'd also like for Coq to PRINT
  expressions involving numbers using our short names, whenever
  possible.  We can instruct it to do so by using the keyword
  [Notation] instead of [Definition].
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

(* These notations make it much less painful to see what is going on
   in larger examples: *)
Eval simpl in (exp two three).

(* Exercise: Recall that the factorial function is defined like this
   in mathematical notation:
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

(* When we say that Coq comes with nothing built-in, we really mean
   it!  Even equality testing has to be defined. *)
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

(* Exercise: Complete the definitions of the following comparison
   functions. *)
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

(* Coq provides a sophisticated module system, to aid in organizing
   large and complex developments.  In this course, we won't need most
   of its features, but one is useful: if we enclose a collection of
   declarations between [Module X] and [End X] markers, then, in the
   remainder of the file after the [End], all these definitions will
   be referred to by names like [X.foo] instead of just [foo].  This
   means we are free to define the unqualified name [foo] later, which
   would otherwise be an error (a name can only be defined once in a
   given scope).

   Here, we wrap the definitions for pairs and lists of numbers in a
   module so that, later, we can use the same names for generic
   versions of the same operations. *)
Module NatList.

(* Each constructor of an inductive type can take any number of
   parameters -- none (as with [yes] and [O]), one (as with [S]), or
   more than one: *)
Inductive prodnat : Set :=
  pair : nat -> nat -> prodnat.

(* This declaration can be read: "There is just one way to construct a
   pair of numbers: by applying the constructor [pair] to two
   arguments of type [nat]." *)

(* Some simple function definitions illustrating pattern matching on
   two-argument constructors *)
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

(* It would be nice to be able to use the more standard mathematical
   notation [(x,y)] instead of [pair x y].  We can tell Coq we intend
   to do this with a [Notation] declaration. *)
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

(* Generalizing the definition of pairs a little, we can describe the
   type of lists of numbers like this: "A list can be either the empty
   list or else a pair of a number and another list." *)
Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* A three-element list: *)
Definition l123 := cons one (cons two (cons three nil)).

(* As with pairs, it is more convenient to write lists in familiar
   mathematical notation.  These two declarations allow us to use ::
   as an infix-cons operator and square brackets as an "outfix"
   notation for constructing lists. *)
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* It is not necessary to deeply understand the [at level 60, right
   associativity] part of the first declaration, but in case you are
   interested, here is roughly what's going on.  The [right
   associativity] part tells Coq how to parenthesize sequences of uses
   of [::].  The next three declarations mean exactly the same
   thing. *)
Definition l123'   := one :: (two :: (three :: nil)).
Definition l123''  := one :: two :: three :: nil.
Definition l123''' := [one,two,three].
(* The [at level 60] part tells Coq how to parenthesize expressions
   that involve both :: and some other infix operator.  For example,
   we'll define ++ below as infix notation for the [append] function,
   at level 59.  This means that [one :: [two] ++ [three]] will be
   parsed as [one :: ([two] ++ [three])] rather than [(one :: [two])
   ++ [three]]. *)

(* Here are several useful functions for constructing, querying, and
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

(* Exercise: Complete the following definitions. *)
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

(* The following exercise illustrates the fact that it sometimes
   requires a little extra thought to satisfy Coq's requirement that
   all Fixpoint definitions be "obviously terminating."  There is an
   easy way to write the [alternate] function using just a single
   [match...end], but Coq will not accept it as obviously terminating.
   Look for a slightly more verbose solution with two nested
   [match...end] constructs.  (Note that each [match] must be
   terminated by an [end].) *)
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
(** * Exercise: Bags via lists *)

(* Exercise: A BAG (often called a MULTISET) is a set where each
   element can appear any finite number of times.  One reasonable
   implementation of bags is to represent a bag of numbers as a LIST
   of numbers.

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

(* ====================================================================== *)
(** * LECTURE 2 *)

(* Administrivia:

     - Please send email to cis500@seas, not to me or Leonid
       individually; it is easier for us to respond that way.

     - Is everyone here receiving messages on CIS500-002-07C?  If not,
       please send mail to cis500@seas and we will add you.

     - Change of BCP office hours:
          -- This week: tomorrow from 11:30 to 1
          -- Future weeks: TBA
*)

(* Any comments or questions about the material so far? *)

(* -------------------------------------------------------------- *)
(** * Options *)

(* Here is another type definition that is quite useful in day-to-day
   functional programming: *)
Inductive natoption : Set :=
  | Some : nat -> natoption
  | None : natoption.  

(* We can use [natoption] as a way of returning "error codes" from
   functions.  For example, suppose we want to write a function that
   returns the nth element of some list.  If we give it type
   [nat->natlist->nat], then we'll have to return some number when the
   list is too short! *)
Fixpoint nth_lessgood (n : nat) (l : natlist) {struct l} : nat :=
  match l with
  | nil => twelve  (* arbitrary! *)
  | a :: l' => if eqnat n O then a else nth_lessgood (pred n) l'
  end.

(* If we give it type [nat->natlist->natoption], then we can return
   [None] when the list is too short and [Some m] when the list has
   enough members and [m] is the one at position [n]. *)
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

(* A HIGHER-ORDER function is one that returns a function as its
   result or takes a function as a parameters -- i.e., it treats
   functions as data. *)

(* In fact, the multiple-argument functions we have already seen are
   simple examples of higher-order functions.  For instance, the type
   of [plus] is [nat->nat->nat]. *)
Check plus.
(* Since [->] associates to the right, this type can also be written
   [nat -> (nat->nat)] -- i.e., the type can be read as saying that
   "[plus] is a one-argument function that takes a [nat] and returns a
   one-argument function that takes another [nat] and returns a
   [nat]."  In the examples above, we have always applied [plus] to
   both of its arguments at once, but if we like we can supply just
   the first.  This is called "partial application." *)
Definition plus3 : nat->nat := plus three.

Lemma check_plus3 :
  plus3 four = seven.
Proof. simpl. reflexivity. Qed.

(* More novel are functions that take other functions as parameters.
   Here is a simple one. *)
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

(* This gives us, for example, a more concise way to define the
   [countoddmembers] function we saw before. *)
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

(* Exercise: Complete the following definition. *)
Definition countzeros (l:natlist) : nat := 
  (* SOLUTION *)
  length (filter (eqnat zero) l).

Lemma check_countzeros1: 
  countzeros [one,zero,three,zero,four,five] = two.
Proof. simpl. reflexivity. Qed.

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

(* Functions in Coq are ordinary data values.  In fact, it is possible
   to construct a function "on the fly" without declaring it at the
   top level and giving it a name; this is analogous to the notation
   we've been using for writing down constant lists, etc. *)
Eval simpl in (map (fun n => times n n) [two,zero,three,one]).
(* The expression [fun n => times n n] here can be read "The function
   that, given a number [n], returns [times n n]." *)

Lemma check_doitthreetimes4: 
  doitthreetimes (fun n => minus (times n two) one) two = nine.
Proof. simpl. reflexivity. Qed.

(* ** A different implementation of bags *)

(* Higher-order functions can be used to give an alternate
   implementation of bags.  In this version, a bag is a function from
   numbers to numbers: *)
Definition bagf := nat -> nat.  

(* When applied to an argument n, this function tells you how many
   times n occurs in the bag. *)
Definition countf (v:nat) (s:bagf) : nat := 
  s v.

(* The empty bagf returns zero when queried for the count of any
   element. *)
Definition emptybagf : bagf := (fun n => zero).

Lemma check_emptybagf1: 
  countf three emptybagf = zero.
Proof. simpl. reflexivity. Qed.  

(* As another example, let us construct, by hand, a bagf containing
   the numbers five (once) and six (twice): *)
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

(* To add an element to a bagf [b], we build a function that, when
   queried for the count for some element [n], first asks [b] for its
   count and then either adds one or not, as appropriate. *)
Definition addf (m:nat) (b:bagf) := 
  fun (n:nat) => 
    match eqnat m n with 
    | no => b n
    | yes => S (b n)
    end.

Lemma check_addf1: 
  countf three (addf three emptybagf) = one.
Proof. simpl. reflexivity. Qed.  

(* Here is a function that converts from the old representation of
   bags to the new one. *)
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

(* Exercise: Complete the following definitions for this new
   implementation of bags. *)

Definition unionf (b1 b2 : bagf) := 
  (* SOLUTION *)
  fun n => plus (countf n b1) (countf n b2).

Lemma check_unionf1: 
  countf one (unionf (bag2bagf [one,two,three]) (bag2bagf [one,four,one])) 
  = three.
Proof. simpl. reflexivity. Qed.

Definition remove_onef (v:nat) (s:bagf) : bagf :=
  (* SOLUTION *)
  fun n => 
    match eqnat n v with
    | no => s n
    | yes => pred (s n)
    end.

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

(* THOUGHT PROBLEM (not to be handed in): Can you write a [subset]
   function for this variant of bags? *)

(* SOLUTION: No -- this would require asking one of the bags for its
   counts for EVERY number, which cannot be done in finite time. *)

End NatList.

(* ---------------------------------------------------------------------- *)
(** ** Polymorphism *)

(* It happens very common that we need different variants of a given
   function with different type annotations.  As a trivial example, we
   might want a doitthreetimes function that works with yesno values
   instead of numbers. *)
Definition doitthreetimes_yn (f:yesno->yesno) (n:yesno) : yesno := 
  f (f (f n)).

(* Defining all these different variants explicitly is annoying and
   error-prone.  Many programming languages -- including Coq -- allow
   us to give a single POLYMORPHIC (or GENERIC) definition: *)
Definition doitthreetimes (X:Set) (f:X->X) (n:X) : X := 
  f (f (f n)).

(* This definition adds an extra parameter to the function, telling it
   what SET to expect its third argument to come from (and its second
   argument [f] to accept and return).  To use [doitthreetimes], we
   must now apply it an appropriate set in addition to its other
   arguments. *)

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
(* The prefix [forall X : Set] corresponds to the first parameter [X].
   The whole type

      [forall X : Set, (X -> X) -> X -> X]

   can be thought of as a more refined version of the type

      [Set -> (X -> X) -> X -> X]
      
   (that is, it tells us that [doitthreetimes] takes three arguments,
   the first of which is a Set, the second a function, etc.); the
   difference is that the [forall X] prefix BINDS the variable [X] in
   the rest of the type, telling us that the second parameter must be
   a function from the set given as the the first parameter to itself,
   etc.  Following this intuition, we might be tempted to write it
   like this

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

(* Exercise: Fill in the implicit arguments in the next line (i.e.,
   replace all occurrences of _ by explicit types): *)
Definition l000l000 := cons _ l000 (cons _ l000 (nil _)).

Notation "[ x , .. , y ]" := (cons _ x .. (cons _ y (nil _)) ..).
Eval simpl in [one,two,three].

(* Side remark: While we're talking about writing less type
   information, we should also mention that Coq can usually infer the
   result types of [Definition]s and [Fixpoint]s -- just leave off the
   result type and the colon.  In what follows, we'll generally
   continue to show result types explicitly, for the sake of
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

(* Exercise: Complete the following function definitions.  Make sure
   you understand what is going on in all the test cases! *)
Fixpoint filter (X:Set) (test: X->yesno) (l:list X) {struct l} : (list X) :=
  (* SOLUTION *)
  match l with
  | nil => nil X
  | h :: t =>
      match (test h) with
      | no => filter X test t
      | yes => h :: (filter X test t)
      end
  end.

Lemma check_filter1: 
  filter nat even [one,two,three,four] = [two,four].
Proof. simpl. reflexivity. Qed.
Lemma check_filter2: 
  filter (list nat) (fun l => eqnat (length nat l) one) 
         [ [one, two], [three], [four], [five,six,seven], (nil _), [eight] ]
  = [ [three], [four], [eight] ].
Proof. simpl. reflexivity. Qed.
  
Fixpoint repeat (X : Set) (n : X) (count : nat) {struct count} : list X := 
  (* SOLUTION *)
  match count with
  | O => nil _
  | S count' => n :: (repeat _ n count')
  end.

Lemma check_repeat1: 
  repeat yesno yes five = [yes,yes,yes,yes,yes].
Proof. simpl. reflexivity. Qed.
Lemma check_repeat2: 
  map nat (list yesno) (fun n => repeat yesno no n) [two,one,three] 
  = [ [no,no], [no], [no,no,no] ].
Proof. simpl. reflexivity. Qed.


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

Inductive option (X:Set) : Set :=
  | Some : X -> option X
  | None : option X.

Fixpoint nth (X : Set) (n : nat)
             (l : list X) {struct l} : option X :=
  match l with
  | nil => None _
  | a :: l' => if eqnat n O then Some _ a else nth _ (pred n) l'
  end.

(* Side note: Coq comes with a large "standard library" of useful
   types (and functions over them), including booleans, natural
   numbers, (polymorphic) pairs, lists, sets, options, etc.  We're
   building everything ourselves here, for the sake of seeing exactly
   how it is done, but of course expert Coq programmers don't need to
   start from scratch like this every time! *)

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
     - the termination parameter is the auxiliary 'c' argument ('c'
       for counter)
     - the annotation for the result type is needed because of the way
       that all_interleavings_aux is called in the body -- it's a
       little too complicated for Coq to work out what the result type
       must be
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

Definition all_interleavings (X:Set) (l1 : list X) (l2 : list X) 
                             : (list (list X)) :=
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


(* ====================================================================== *)
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
  (* SOLUTION *)
  simpl. reflexivity.
Qed.

Lemma const_append : forall l:list nat, 
  append nat [three,four] l = three :: four :: l.
Proof.
  (* SOLUTION *)
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
   rewrite -> eq. (* Rewrite the goal according to the hypothesis *)
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
  (* SOLUTION *)
  intros m n o.  
   intros eqmn. 
   intros eqno. 
   rewrite -> eqmn. 
   rewrite -> eqno. 
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
  (* SOLUTION *)
  intros b. destruct b.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma all3_spec : forall b c : yesno,
    one_yes 
      (both_yes b c) 
      (one_yes (swap_yesno b)
               (swap_yesno c))
  = yes.
Proof.
  (* SOLUTION *)
  intros b c. destruct b.
    destruct c.
      simpl. reflexivity.
      simpl. reflexivity.
    destruct c.
      simpl. reflexivity.
      simpl. reflexivity.
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
  (* SOLUTION *)
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn. simpl. reflexivity.
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
(* Note that we applied a rewrite here justified by a previously
   proved lemma ([plus_one]) rather than an assumption in the
   immediate context. *)

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
  (* SOLUTION *)  
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Qed.

Lemma dist_succ_plus : forall m n : nat, 
  plus m (S n) = S (plus m n).
Proof. 
  (* SOLUTION *)
  intros m n. induction m.
    simpl. reflexivity.
    simpl. rewrite -> IHm. reflexivity.
Qed. 

Lemma plus_commut : forall m n : nat, 
  plus m n = plus n m.
Proof.
  (* SOLUTION *)
  intros m n. induction n. 
    simpl. rewrite -> plus_zero. reflexivity.
    simpl. rewrite <- IHn. rewrite -> dist_succ_plus. reflexivity.
Qed.

(* Exercise: Which of the following lemmas require induction in their
   proofs?  (See if you can predict in advance, before trying with
   Coq.) *)
Lemma S_neq_zero : forall n:nat,
  eqnat (S n) zero = no.
Proof.
  (* SOLUTION *)
  simpl. reflexivity.
Qed.
Lemma zero_neq_S : forall n:nat,
  eqnat zero (S n) = no.
Proof.
  (* SOLUTION *)
  simpl. reflexivity.
Qed.
Lemma n_neq_Sn : forall n : nat,
  eqnat n (S n) = no.
Proof.
  (* SOLUTION *)
  intros n. induction n.
    simpl. reflexivity.
    simpl. rewrite -> IHn. reflexivity.
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
  (* SOLUTION *)
  intros X l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> IHl. reflexivity.
Qed.

(* An exercise to be worked together: *)
Lemma length_append : forall X : Set,
                      forall l1 l2 : list X,
  length _ (l1 ++ l2) = plus (length _ l1) (length _ l2).
Proof.
  (* SOLUTION *)
  intros X l1 l2. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
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

(* Similarly, the fact that [map] and [snoc] "commute" (in the sense
   that it doesn't matter which we do first)... *)
Lemma map_snoc : forall X Y : Set, 
                 forall f : X->Y,
                 forall v : X,
                 forall s : list X,
  map X Y f (snoc X s v) = snoc Y (map X Y f s) (f v).
Proof.
  intros X Y f v s. induction s.
    simpl. reflexivity.
    simpl. rewrite -> IHs. reflexivity.
Qed.

(* An exercise to work together: Show that [map] and [reverse]
   "commute" in a similar way. *)
Lemma map_reverse : forall X Y : Set, 
                    forall f : X->Y,
                    forall s : list X,
  map X Y f (reverse X s) = reverse Y (map X Y f s).
Proof.
  (* SOLUTION *)
  intros X Y f s. induction s. 
    simpl. reflexivity.
    simpl. rewrite -> map_snoc. rewrite -> IHs. reflexivity.
Qed.

(* Exercises... *)

Lemma reverse_snoc : forall X : Set, 
                     forall v : X,
                     forall s : list X,
  reverse X (snoc X s v) = v :: (reverse _ s).
Proof.
  intros X v s. induction s.
    simpl. reflexivity.
    simpl. rewrite -> IHs. simpl. reflexivity.
Qed.

Lemma reverse_reverse : forall X : Set, 
                        forall s : list X,
  reverse X (reverse X s) = s.
Proof.
  (* SOLUTION *)
  intros X s. induction s.
    simpl. reflexivity.
    simpl. rewrite -> reverse_snoc. rewrite -> IHs. reflexivity.
Qed.

Lemma snoc_append : forall X : Set, 
                    forall l1 l2 : list X,
                    forall v : X,
  snoc _ (l1 ++ l2) v = l1 ++ (snoc _ l2 v).
Proof.
  intros X l1 l2 v. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma reverse_append : forall X : Set, 
                       forall l1 l2 : list X,
  reverse _ (l1 ++ l2) = (reverse _ l2) ++ (reverse _ l1).
Proof.
  (* SOLUTION *)
  intros X l1 l2. induction l1.
    simpl. rewrite -> append_nil. reflexivity.
    simpl. rewrite -> IHl1. rewrite -> snoc_append. reflexivity.
Qed.

(* EXERCISE: 
     - Find a non-trivial equation involving cons (::), snoc, and
       append (++).
     - Prove it.
FILL IN HERE
*)
(* HIDE WHEN EXERCISE *)
Lemma append_snoc : forall X : Set, 
                    forall l1 l2 : list X,
                    forall v : X,
  ((snoc _ l1 v) ++ l2) = l1 ++ (v :: l2).
Proof.
  intros X l1 l2 v. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

(* There is a short solution to the next exercise.  If you find
   yourself getting tangled up, step back and try to look for a
   simpler way... *)
Lemma append_assoc4 : forall X : Set,
                      forall l1 l2 l3 l4 : list X,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* SOLUTION *)
  intros X l1 l2 l3 l4. 
   rewrite -> append_assoc. rewrite -> append_assoc.
   reflexivity.
Qed.


(* ====================================================================== *)
(** * LECTURE 4 *)

(* The small set of tactics we have seen so far can already be used to
   prove some fairly interesting properties of inductively defined
   functions.  In this lecture we extend our range by introducing
   several other fundamental tactics and exploring how they can be
   used for more sophisticated reasoning involving equalities and
   induction. *)

(* Note: As we get into Coq more seriously, using a richer set of
   tactics and attacking harder problems, you will probably find
   yourself getting stuck more often.  This is when your study partner
   or group will start being extremly useful: two or three people tend
   to get unstuck exponentially faster than one person working alone.

   If you are not in a study group and want to be, please let us know
   and we will facilitate.

   If you are happy working solo, that's OK.  But make sure that you
   at least have some phone numbers of people you can call when you
   are feeling frustrated.

   In either case, you should at least attempt all the homework
   problems before Friday's recitions, if at all possible, so that you
   can ask questions there. *)

(* ---------------------------------------------------------------------- *)
(** * The [Case] annotation *)

(* One of the less nice things about Coq's mechanisms for interactive
   proof is the way subgoals seem to come and go almost at random,
   with no explicit indication of where we are -- which case of an
   induction or case analysis we are in -- at any given moment.  In
   very short proofs, this is not a big deal.  But in more complex
   proofs it can become quite difficult to stay oriented.

   Here is a simple hack that I find helps things quite a bit.  It
   uses some facilities of Coq that we have not discussed -- the
   string library (just for the concrete syntax of quoted strings) and
   the [Ltac] command, which allows us to declare custom tactics.  We
   will come back to [Ltac] in more detail later.  For now, don't
   worry about the details of this declaration. *)
Require String. Open Scope string_scope.
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.
Ltac Case s := let c := fresh "case" in set (c := s); move_to_top c.

(* Having defined the [Case] tactic, let's see how it is used.  Step
   through the following proof and observe how the context changes. *)
Lemma length_reverse' : forall X : Set,
                        forall l : list X,
  length _ l = length _ (reverse _ l).
Proof.
  intros X l. induction l.
    Case "nil". 
      simpl. reflexivity.
    Case "cons". 
      simpl. rewrite -> length_snoc. rewrite -> IHl.  reflexivity.
Qed. 

(* The [Case] tactic does something very trivial: It simply adds a
   string that we choose (tagged with the identifier "case") to the
   context for the current goal.  When subgoals are generated, this
   string is carried over into their contexts.  When the last of these
   subgoals is finally proved and the next top-level goal (a sibling
   of the current one) becomes active, this string will no longer
   appear in the context and we will be able to see that the case
   where we introduced it is complete. *)


(* ---------------------------------------------------------------------- *)
(** * The [unfold] tactic *)

(* Sometimes the [simpl] tactic doesn't make things quite as simple as
   we need.  The [unfold] tactic can be used to explicitly replace a
   defined name by the right-hand side of its definition. *)

Definition plus3 (n:nat) := plus n three.

Lemma plus3_example : forall n,
  plus3 n = plus three n.
Proof.
  simpl.
  (* Note that the [simpl] rewrites the right-hand side of the
     equation, but not the left.  Now we are stuck unless we know
     something about the way plus3 is defined. *)
  unfold plus3. intros n. rewrite -> plus_commut. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(** * The [apply] tactic *)

(* We often encounter situations where the goal to be proved is
   exactly the same as some hypothesis in the context or some
   previously proved lemma. *)
Lemma silly1 : forall (m n o p : nat),
     m = n 
  -> [m,o] = [m,p]
  -> [m,o] = [n,p].
Proof.
  intros m n o p eq1 eq2.
  rewrite <- eq1.
(* At this point, we could finish with [rewrite -> eq2. reflexivity.]
   as we have done several times above.  But we can achieve the same
   effect in a single step by using the [apply] tactic instead: *)
  apply eq2.
Qed.

(* The [apply] tactic also works with CONDITIONAL hypotheses and
   lemmas: if the statement being applied is an implication, then the
   premises of this implication will be added to the list of subgoals
   needing to be proved. *)
Lemma silly2 : forall (m n o p : nat),
     m = n 
  -> (forall (q r : nat), q = r -> [q,o] = [r,p])
  -> [m,o] = [n,p].
Proof.
  intros m n o p eq1 eq2.
  apply eq2. apply eq1.
Qed.
(* You may find it instructive to experiment with this proof and see
   if there is a way to complete it using just [rewrite] instead of
   [apply]. *)

(* Typically, when we use [apply H], the statement [H] will begin with
   a [forall] binding some "universal variables."  When Coq matches
   the current goal against the conclusion of [H], it will try to find
   appropriate values for these variables.  For example, when we do
   [apply eq2] in in the following proof, the universal variable [q]
   in [eq2] gets instantiated with [(m,m)] and [r] gets instantiated
   with [(n,n)].  (What does [X] get instantiated with?) *)
Lemma silly2a : forall (m n : nat),
     (m,m) = (n,n) 
  -> (forall (X : Set) (q r : X), q = r -> [q] = [r])
  -> [(m,m)] = [(n,n)].
Proof.
  intros m n eq1 eq2.
  apply eq2. apply eq1.
Qed.

(* Exercise: Complete the following proof without using [simpl]. *)
Lemma silly_ex : 
     (forall n, even n = yes -> odd (S n) = yes)
  -> even three = yes
  -> odd four = yes.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* To use the [apply] tactic, the (conclusion of the) fact being
   applied must match the goal EXACTLY -- for example, [apply] will
   not work if the left and right sides of the equality are
   swapped. *)
Lemma silly3_firsttry : forall (m : nat),
  (eqnat m five = yes -> eqnat (S (S m)) seven = yes)
  -> yes = eqnat m five 
  -> yes = eqnat (S (S m)) seven.
Proof.
  intros m eq H.
  (* here we are stuck *)
Admitted.

(* When you find yourself in such a situation, one thing to do is to
   go back and try changing reorganizing the statement of whatever you
   are trying to prove so that things appear the right way around when
   they are needed.  But if this is not possible or convenient, then
   the following lemma can be used to swap the sides of an equality
   statement in the goal so that some other lemma can be applied. *)
Lemma eq_symm : forall (X:Set) (m n : X),
  m = n -> n = m.
Proof.
  intros X m n eq. rewrite -> eq. reflexivity.
Qed.

Lemma silly3 : forall (m : nat),
  (eqnat m five = yes -> eqnat (S (S m)) seven = yes)
  -> yes = eqnat m five 
  -> yes = eqnat (S (S m)) seven.
Proof.
  intros m eq H.
  apply eq_symm. apply eq. apply eq_symm. apply H.
Qed.

Lemma reverse_exercise1 : forall (X : Set) (l l' : list X),
     l = reverse X l'
  -> l' = reverse X l.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.


(* ---------------------------------------------------------------------- *)
(** * Using tactics on hypotheses *)

(* By default, most tactics perform some operation on the goal formula
   and leave the context unchanged.  But tactics often come with
   variants that can be used to perform similar operations on a
   statement in the context. *)

(* For example, the tactic [simpl in H] performs simplification in the
   hypothesis named [H] in the context. *)
Lemma S_inj' : forall (m n : nat) (b : yesno),
     eqnat (S m) (S n) = b 
  -> eqnat m n = b. 
Proof.
  intros m n b H. simpl in H. apply H. 
Qed.

(* Similarly, the tactic [apply L in H] matches some conditional
   statement [L] (of the form [L1->L2], say) against a hypothesis H in
   the context.  However, unlike ordinary [apply] (which rewrites a
   goal matching [L2] into a subgoal [L1]), [apply L in H] matches [H]
   against [L1] and, if successful, replaces it with [L2].  

   In other words, [apply L in H] gives us a form of FORWARD
   REASONING -- from [L1->L2] and a hypothesis matching [L1], it gives
   us a hypothesis matching [L2].

   By contrast, [apply L] is BACKWARD REASONING -- it says that if we
   know [L1->L2] and we are trying to prove [L2], it suffices to prove
   [L1]. *)

(* Here is a variant of a proof from above, using forward reasoning
   throughout intead of backward reasoning. *)
Lemma silly3' : forall (m : nat),
  (eqnat m five = yes -> eqnat (S (S m)) seven = yes)
  -> yes = eqnat m five 
  -> yes = eqnat (S (S m)) seven.
Proof.
  intros m eq H.
  apply eq_symm in H. apply eq in H. apply eq_symm in H. apply H.
Qed.


(* ---------------------------------------------------------------------- *)
(** * The [assert] tactic *)

(* Coq's default style of reasoning is backward.  However, it can
   sometimes be convenient to switch to a "forward mode" for part of a
   proof.  Here is one more tactic that does this in a very powerful
   way... *)

(* It is common to reach a point in a proof where we would like to
   apply some fact [L] that we have not proven yet.  One way to deal
   with this is to abort the current proof, state [L] as a separate
   lemma, prove it, and then go back to where we were.  But this
   strategy may sometimes not be attractive: it may be that [L]
   depends on many local assumptions, so that stating it as a separate
   lemma would require adding many awkward hypotheses; or it may be
   that the proof of [L] is short or uninteresting.  The [assert]
   tactic helps in such cases.

   If the current goal statement is [G], then doing [assert L as H] leaves
   us with two subgoals:
     - proving [L]
     - proving [G] again, but now with [L] as a hypothesis (named [H])
       in the context.

   For example, here is an alternative proof of the [reverse_reverse]
   lemma, with the proof of the auxiliary [reverse_snoc] lemma
   in-lined using [assert]. *)

Lemma reverse_reverse' : forall X : Set, 
                         forall s : list X,
  reverse X (reverse X s) = s.
Proof.
  intros X s. induction s.
    Case "nil".
      simpl. reflexivity.
    Case "cons". 
      simpl. 
      assert (forall Y : Set, 
              forall v : Y,
              forall l : list Y,
              reverse Y (snoc Y l v) = v :: (reverse _ l))
          as reverse_snoc.
        Case "Proof of reverse_snoc".
          intros Y v l. induction l.
            Case "nil". reflexivity.
            Case "cons". simpl. rewrite -> IHl. reflexivity.
      rewrite -> reverse_snoc. rewrite -> IHs. reflexivity.
Qed.  

(* In the previous proof, [reverse_snoc] was inlined "verbatim" from
   above, for simplicity.  But this example is also an illustration of
   how asserting needed facts in-line can be simpler than breaking
   them out as separate lemmas: we can simplify the statement of
   [reverse_snoc] by omitting the quantification over [Y] --
   essentially, proving just the version of [reverse_snoc] that we
   need right here (where the elements of the list have type [X])
   rather than a more general one. *)
Lemma reverse_reverse'' : forall X : Set, 
                          forall s : list X,
  reverse X (reverse X s) = s.
Proof.
  intros X s. induction s.
    Case "nil".
      simpl. reflexivity.
    Case "cons". 
      simpl. 
      assert (forall v : X,
              forall l : list X,
              reverse X (snoc X l v) = v :: (reverse _ l))
          as reverse_snoc.
        Case "Proof of reverse_snoc".
          intros v l. induction l.
            Case "nil". reflexivity.
            Case "cons". simpl. rewrite -> IHl. reflexivity.
      rewrite -> reverse_snoc. rewrite -> IHs. reflexivity.
Qed.


(* ---------------------------------------------------------------------- *)
(** * The [inversion] tactic *)

(* A fundamental property of inductive definitions is that their
   constructors are INJECTIVE.  For example, the only way we can have
   [S n = S m] is if [m = n].

   The [inversion] tactic uses this injectivity principle to
   'destruct' an equality hypothesis. *)
Lemma S_inj : forall (m o : nat),
     S m = S o
  -> m = o.
Proof.
  intros m o eq. inversion eq. reflexivity.
Qed.

(* The same principle applies to other inductively defined sets, such
   as lists. *)
Lemma silly4 : forall (m o : nat),
     [m] = [o]
  -> m = o.
Proof.
  intros m o eq. inversion eq. reflexivity.
Qed.

(* The [inversion] tactic will destruct equalities between complex
   values, binding multiple variables as it goes. *)
Lemma silly5 : forall (m n o : nat),
     [m,n] = [o,o]
  -> [m] = [n].
Proof.
  intros m n o eq. inversion eq. reflexivity.
Qed.

Lemma sillyex1 : forall (X : Set) (x y z : X) (l j : list X),
     x :: y :: l = z :: j
  -> y :: l = x :: j
  -> x = y.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Another critical property of inductive definitions is that distinct
   constructors are never equal, no matter what they are applied to.
   For example, [S n] can never be equal to [O], no matter what [n]
   is.  This means that anytime we can see a HYPOTHESIS of the form [S
   n = O], we know that we must have made contradictory assumptions at
   some point.  The [inversion] tactic can be used to cut off the
   proof at this point. *)
Lemma silly6 : forall (n : nat),
     S n = O
  -> plus two two = five.
Proof.
  intros n contra. inversion contra. 
Qed.

(* Similarly, under the assumption that [no = yes], anything at all
   becomes provable. *)
Lemma silly7 : forall (m n : nat),
     no = yes
  -> [m] = [n].
Proof.
  intros m n contra. inversion contra. 
Qed.

Lemma sillyex2 : forall (X : Set) (x y z : X) (l j : list X),
     x :: y :: l = nil _
  -> y :: l = z :: j
  -> x = z.
Proof.
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* Here is a more realistic use of inversion to prove a property that
   we will find useful at many points later on... *)
Lemma eqnat_yes : forall m n,
  eqnat m n = yes -> m = n.
Proof.
  intros m. induction m. 
    Case "O". 
      intros n. destruct n.  
      Case "O". simpl. reflexivity.  
      Case "S". simpl. intros contra. inversion contra. 
    Case "S". 
      intros n. destruct n.
      Case "O". intros contra. inversion contra.
      Case "S". intros H. simpl in H.
        apply IHm in H. rewrite -> H. reflexivity.
Qed.
(* Note how nested uses of our [Case] tactic behave: when there is
   already a "case" tag in the context, it adds a new tag called
   "case0" (then "case1", etc.).  In this way we can keep track of
   nested cases to any depth we like. *)

(* Exercise: The above lemma can also be proved by induction on
   [m] (though we have to be a little careful about which order we
   introduce the variables, so that we get a general enough induction
   hypothesis; this is done for you below).  Finish the following
   proof.  To get maximum benefit from the exercise, try first to do
   it without looking back at the one above. *)
Lemma eqnat_yes' : forall n m,
  eqnat m n = yes -> m = n.
Proof.
  intros n. induction n. 
  (* FILL IN HERE (and delete "Admitted") *) Admitted.

(* ====================================================================== *)
(** * LECTURE 5 *)

(* Mini-sermon: Mindless proof-hacking is a terrible temptation in
   Coq... Please resist it! *)
     
(* ---------------------------------------------------------------------- *)
(* The [apply...with...] tactic *)

(* The following (silly) example uses two rewrites in a row to get from 
   [ [m,n] ] to [ [r,s] ]. *)
Lemma eq_trans_example : forall (a b c d e f : nat),
     [a,b] = [c,d]
  -> [c,d] = [e,f]
  -> [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(* Since this is a common pattern, we might abstract it out as a lemma
   recording once and for all the fact that equality is transitive. *)
Lemma eq_trans : forall (X:Set) (m n o : X),
  m = n -> n = o -> m = o.
Proof.
  intros X m n o eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

(* Now, we should be able to use [eq_trans] to prove the above
   example.  However, to do this we need a slight refinement of the
   [apply] tactic... *)
Lemma eq_trans_example' : forall (a b c d e f : nat),
     [a,b] = [c,d]
  -> [c,d] = [e,f]
  -> [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply eq_trans] at this point, it can
     tell (by matching the goal against the conclusion of the lemma)
     that it should instantiate [X] with [nat], [m] with [[a,b]], and
     [o] with [[e,f]].  However, the matching process doesn't
     determine an instantiation for [n]: we have to supply one
     explicitly by adding [with (n:=[c,d])] to the invocation of
     [apply]. *) 
  apply eq_trans with (n:=[c,d]). apply eq1. apply eq2. 
Qed.

Lemma eq_trans_exercise : forall (m n o p : nat),
     (plus m p) = n
  -> n = (minustwo o)
  -> (plus m p) = (minustwo o). 
Proof.
  intros m n o p.
  apply eq_trans.
Qed.

(* ---------------------------------------------------------------------- *)
(* Practice session *)

(* Some nontrivial but not-too-complicated proofs to work together in
   class, and some for you to work as exercises... *)

(* This is a slightly roundabout way of stating a fact that we have
   already proved above.  The extra equalities force us to do a little
   more equational reasoning and exercise some of the tactics we've
   seen recently. *)
Lemma length_snoc' : forall (X : Set) (v : X)  (l : list X) (n : nat),
     length _ l = n
  -> length _ (snoc _ l v) = S n. 
Proof.
  intros X v l. induction l.
    Case "nil". intros n eq. rewrite <- eq. reflexivity.
    Case "cons". intros n eq. simpl. destruct n.
      Case "O". inversion eq.
      Case "S". 
        assert (length X (snoc X l v) = S n).
          Case "Proof of assertion". apply IHl with (n:=n). simpl in eq. 
          inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

(* A slightly different way of making the same assertion. *)
Lemma length_snoc'' : forall (X : Set) (v : X)  (l : list X) (n : nat),
     S (length _ l) = n
  -> length _ (snoc _ l v) = n.
Proof.
  intros X v l. induction l.
    Case "nil".  intros n eq. rewrite <- eq. simpl. trivial.
    Case "cons". intros n eq. rewrite <- eq. simpl. 
      assert (forall m n, m = n -> S m = S n).
        intros. rewrite H. trivial.
      apply H. rewrite <- IHl. trivial. trivial.
Qed.
      

Fixpoint double (n:nat) {struct n} :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma eq_S : forall m n, m = n -> S m = S n.
Proof.
  intros m n eq. rewrite eq. trivial.
Qed.

Lemma double_injective : forall m n,
     double m = double n
  -> m = n.
Proof.
  intros m. induction m.
    intros n eq. destruct n. trivial. simpl in eq. inversion eq. 
    intros n eq. destruct n. simpl in eq. inversion eq.
      apply eq_S. apply IHm. simpl in eq. inversion eq. trivial.
Qed.

Lemma plus_m_m_injective : forall m n,
     plus m m = plus n n
  -> m = n.
Proof.
  intros m. induction m.
    intros n eq. destruct n. trivial. simpl in eq. inversion eq.
    intros n eq. destruct n. simpl in eq. inversion eq. 
      apply eq_S. apply IHm. simpl in eq. inversion eq.
        rewrite plus_commut in H0.  apply eq_symm in H0. rewrite plus_commut in H0.
          simpl in H0. inversion H0. trivial.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Case analysis of compound expressions *)

(* We have seen many examples where the [destruct] tactic is used to
   perform case analysis of the value of some variable.  But sometimes
   we need to reason by cases on the result of some *expression*.  We
   can also do this with [destruct]. *)

Definition sillyfun (n : nat) : yesno :=
  if eqnat n three then no
  else if eqnat n five then no
  else no.

Lemma sillyfun_no : forall (n : nat),
  sillyfun n = no.
Proof.
  intros n. unfold sillyfun. 
  destruct (eqnat n three).
    Case "yes". reflexivity.
    Case "no". destruct (eqnat n five).
      Case "yes". reflexivity.
      Case "no". reflexivity.
Qed.

Lemma sillyfun_odd : forall (n : nat),
     sillyfun n = yes
  -> odd n = yes.
Proof.
  (* intros n eq. rewrite sillyfun_no in eq. inversion eq. *)
  intro n.  unfold sillyfun. destruct (eqnat n three).
    intro H; inversion H.
    destruct (eqnat n five); intro H; inversion H.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Case study: Interpreters *)

(* Now it's time to start playing with programming languages.  Let's
   begin with an incredibly simple one: a language of expressions
   involving just numeric constants and a single binary operator,
   addition.  You may want to refer to Chapter 3 of TAPL as background
   for this lecture. *)

(* Let's enclose the next bit in a module so that we can re-use the
   names it declares later on in the course without conflicting with
   the ones defined here (as we did above with lists of numbers and
   polymorphic lists) *)
Module SimpleArith.  

(* An ABSTRACT SYNTAX of terms.  (See the discussion in TAPL of
   abstract syntax vs. concrete syntax.) *)
Inductive tm : Set :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm. 

(* An INTERPRETER that maps each term to a number. *)
Fixpoint interp (t:tm) {struct t} : nat :=
  match t with
  | tm_const n => n
  | tm_plus t1 t2 => plus (interp t1) (interp t2)
  end.

Lemma check_interp1: 
    interp (tm_const three) 
  = three.
Proof. reflexivity. Qed.
Lemma check_interp2: 
    interp (tm_plus 
              (tm_plus (tm_const one) (tm_const two))
              (tm_plus (tm_const three) (tm_const four)))
  = ten.
Proof. reflexivity. Qed.

(* We can write a variety of programs that operate on terms -- often
   called METAPROGRAMS because they are programs that manipulate other
   programs.  For example, here is a simple metaprogram that reverses
   a term by swapping the arguments to each tm_plus node. *)
Fixpoint tmreverse (t:tm) {struct t} : tm :=
  match t with
  | tm_const n => tm_const n
  | tm_plus t1 t2 => tm_plus (tmreverse t2) (tmreverse t1)
  end.

Lemma check_tmreverse: 
    tmreverse (tm_plus 
                (tm_plus (tm_const one) (tm_const two))
                (tm_plus (tm_const three) (tm_const four)))
  =           (tm_plus 
                (tm_plus (tm_const four) (tm_const three))
                (tm_plus (tm_const two) (tm_const one))).
Proof. reflexivity. Qed.

(* As a sanity check for such a program transformation, we should
   check that it preserves the program's meaning, as defined by
   [interp]. *)
Lemma tmreverse_interp : forall t : tm, 
  interp (tmreverse t) = interp t.
Proof.
  intros t.
  induction t.
    Case "tm_const". simpl. reflexivity.
    Case "tm_plus". simpl. rewrite -> IHt1. rewrite -> IHt2.
      rewrite -> plus_commut. reflexivity.
Qed.

(* Here is a more practical (though still extremely simple) program
   transformation -- an optimization that replaces every subterm of
   the form [tm_plus (tm_const zero) t] by just [t]. *)
Fixpoint simplify_0plus (t:tm) {struct t} : tm :=
  match t with
  | tm_const n => tm_const n
  | tm_plus (tm_const zero) t2 => simplify_0plus t2
  | tm_plus t1 t2 => tm_plus (simplify_0plus t1) (simplify_0plus t2)
  end.

Lemma check_simplify_0plus: 
    simplify_0plus
      (tm_plus 
        (tm_plus (tm_const zero) (tm_const two))
        (tm_plus (tm_const three) (tm_const zero)))
  =   
      (tm_plus 
        (tm_const two)
        (tm_plus (tm_const three) (tm_const zero))).
Proof. reflexivity. Qed.
Lemma check_simplify_0plus': 
    simplify_0plus
      (tm_plus 
        (tm_const zero)
        (tm_plus (tm_const zero) (tm_const three)))
  =   
        (tm_const three).
Proof. reflexivity. Qed.
Lemma check_simplify_0plus'': 
    simplify_0plus
      (tm_plus 
        (tm_const zero)
        (tm_plus 
          (tm_const two) 
          (tm_plus (tm_const zero) (tm_const three))))
  =   
        (tm_plus 
          (tm_const two) 
          (tm_const three)).
Proof. reflexivity. Qed.

(* And here is the proof that [simplify_0plus] preserves meaning. *)
Lemma simplify_0plus_interp : forall (t:tm),
  interp (simplify_0plus t) = interp t.
Proof.
  induction t.
    Case "tm_const". simpl. reflexivity.
    Case "tm_plus". destruct t1. 
      Case "tm_const". destruct n.  
        Case "O". simpl. rewrite -> IHt2. reflexivity.
        Case "S". simpl. rewrite -> IHt2. reflexivity.
      Case "tm_plus". simpl. simpl in IHt1. simpl in IHt2. 
          rewrite -> IHt1. rewrite -> IHt2. reflexivity.
Qed.

(* Now let's look at a more interesting operation on terms: ONE-STEP
   SIMPLIFICATION.  This function identifies the leftmost subterm that
   is "ready to be simplified" -- i.e., it has the form
   [tm_plus (tm_const m) (tm_const n)] -- and replaces it with
   [tm_const (plus m n)], leaving everything else the same.  If there
   is no such subterm (i.e., if the whole term is just a constant),
   then the simplification function "fails" by returning [None]. *)
Fixpoint simplify_step (t:tm) {struct t} : option tm :=
  match t with
  | tm_const n => None _
  | tm_plus t1 t2 => 
      match (t1,t2) with
      | (tm_const n1, tm_const n2) => Some _ (tm_const (plus n1 n2))
      | (tm_const n1, _) => 
          match simplify_step t2 with
          | Some t2' => Some _ (tm_plus t1 t2')
          | None => None _   
          end
      | (_, _) => 
          match simplify_step t1 with
          | Some t1' => Some _ (tm_plus t1' t2)
          | None => None _   
          end
      end
  end.

(* A constant is done being simplified -- it cannot take a step: *)
Lemma check_simplify_step_1: 
    simplify_step
      (tm_const five)
  =   
      None _.
Proof. reflexivity. Qed.
(* If [t1] can take a step to [t1'], then [tm_plus t1 t2] steps to 
   [plus t1' t2]: *)
Lemma check_simplify_step_2: 
    simplify_step
      (tm_plus 
        (tm_plus (tm_const zero) (tm_const three))
        (tm_plus (tm_const two) (tm_const four)))
  =   
     Some _ 
       (tm_plus 
         (tm_const three)
         (tm_plus (tm_const two) (tm_const four))).
Proof. reflexivity. Qed.
(* Right-hand sides of sums can take a step only when the left-hand
   side is finished: if [t2] can take a step to [t2'], then
   [tm_plus (tm_const n) t2] steps to [tm_plus (tm_const n) t2']: *)
Lemma check_simplify_step_3: 
    simplify_step
      (tm_plus 
        (tm_const zero)
        (tm_plus 
          (tm_const two) 
          (tm_plus (tm_const zero) (tm_const three))))
  =   
     Some _ (tm_plus 
              (tm_const zero)
              (tm_plus 
                (tm_const two) 
                (tm_const three))).
Proof. reflexivity. Qed.

Lemma simplify_step_interp : forall t t',
     simplify_step t = Some _ t'
  -> interp t = interp t'.
Proof.
  intros t. induction t.
    Case "tm_const". intros t'. simpl. intros eq. inversion eq. 
    Case "tm_plus". intros t' eq. simpl. simpl in eq. destruct t1.
      Case "tm_const". destruct t2.
        Case "tm_const". simpl. inversion eq. reflexivity. 
        Case "tm_plus". 
          destruct (simplify_step (tm_plus t2_1 t2_2)). 
            Case "Some".   
              inversion eq.
              assert (interp (tm_plus t2_1 t2_2) = interp t) as H.
                Case "Proof of assertion". 
                  apply IHt2. reflexivity.
              rewrite -> H. reflexivity.
            Case "None". inversion eq.
      Case "tm_plus". 
        destruct (simplify_step (tm_plus t1_1 t1_2)). 
          Case "Some".   
            inversion eq. 
            assert (interp (tm_plus t1_1 t1_2) = interp t) as H.  
              Case "Proof of assertion". apply IHt1. reflexivity.
            rewrite -> H. reflexivity.
          Case "None". inversion eq.
Qed.      

End SimpleArith.

(* ---------------------------------------------------------------------- *)

Module SimpleArithExercise.

(* Exercise: The [SimpleArith] module developed a small collection of
   program transformations for a very simple programming language with
   just constants and addition.  Your task is to extend this
   development to a very slightly less trivial language with
   constants, addition, and subtraction.  The definition of the
   language and its meaning (the [interp] function) are given to you,
   as well as some new test cases for the definitions (to make sure
   subtraction works correctly) and some parts of the proofs, to get
   you started. *)

   (* Remove this open-comment and the close-comment at the very end of
     the module before starting. *)

Inductive tm : Set :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_minus : tm -> tm -> tm. 

Fixpoint interp (t:tm) {struct t} : nat :=
  match t with
  | tm_const n => n
  | tm_plus t1 t2 => plus (interp t1) (interp t2)
  | tm_minus t1 t2 => minus (interp t1) (interp t2)
  end.

Lemma check_interp1: 
    interp (tm_const three) 
  = three.
Proof. reflexivity. Qed.
Lemma check_interp2: 
    interp (tm_plus 
              (tm_plus (tm_const one) (tm_const two))
              (tm_plus (tm_const three) (tm_const four)))
  = ten.
Proof. reflexivity. Qed.

(* Subtraction is not a commutative operation, so [tmreverse] should
   swap the subterms just of [tm_plus] nodes, not [tm_minus] nodes. *)
Fixpoint tmreverse (t:tm) {struct t} : tm :=
  match t with
  | tm_const n => tm_const n
  | tm_plus t1 t2 => tm_plus (tmreverse t2) (tmreverse t1)
  | tm_minus t1 t2 => tm_minus (tmreverse t1) (tmreverse t2)
  end.

Lemma check_tmreverse1: 
    tmreverse (tm_plus 
                (tm_plus (tm_const one) (tm_const two))
                (tm_plus (tm_const three) (tm_const four)))
  =           (tm_plus 
                (tm_plus (tm_const four) (tm_const three))
                (tm_plus (tm_const two) (tm_const one))).
Proof. reflexivity. Qed.
Lemma check_tmreverse2: 
    tmreverse (tm_plus
                (tm_minus (tm_const one) (tm_const two))
                (tm_plus (tm_const three) (tm_const four)))
  =           (tm_plus
                (tm_plus (tm_const four) (tm_const three))
                (tm_minus (tm_const one) (tm_const two))).
Proof. reflexivity. Qed.
Lemma check_tmreverse3: 
    tmreverse (tm_minus
                (tm_minus (tm_const one) (tm_const two))
                (tm_plus (tm_const three) (tm_const four)))
  =           (tm_minus
                (tm_minus (tm_const one) (tm_const two))
                (tm_plus (tm_const four) (tm_const three))).
Proof. reflexivity. Qed.

Lemma tmreverse_interp : forall t : tm, 
  interp (tmreverse t) = interp t.
Proof.
  intro t. induction t.
    Case "tm_const".
      simpl. reflexivity.
    Case "tm_plus".
      simpl.  rewrite IHt1. rewrite IHt2. rewrite plus_commut. reflexivity.
    Case "tm_minus".
      simpl.  rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

Fixpoint simplify_0plus (t:tm) {struct t} : tm :=
  match t with
  | tm_const n => tm_const n
  | tm_plus (tm_const zero) t2 => simplify_0plus t2
  | tm_plus t1 t2 => tm_plus (simplify_0plus t1) (simplify_0plus t2)
  | tm_minus t1 t2 => tm_minus (simplify_0plus t1) (simplify_0plus t2)
  end.

Lemma simplify_0plus_interp : forall (t:tm),
  interp (simplify_0plus t) = interp t.
Proof.
  intro t. induction t.
  Case "tm_const".  trivial.
  Case "tm_plus".  destruct t1.
    destruct n.
      simpl.  rewrite IHt2. trivial.
      simpl.  rewrite IHt2. trivial.
    simpl. simpl in IHt1.  rewrite IHt1. rewrite IHt2. trivial.
  Case "tm_minus".
    simpl.  inversion IHt2. inversion IHt1. rewrite H1. trivial.
    simpl. rewrite IHt1. rewrite IHt2. trivial.
Qed.


Fixpoint simplify_step (t:tm) {struct t} : option tm :=
  match t with
  | tm_const n => None _
  | tm_plus t1 t2 => 
      match (t1,t2) with
      | (tm_const n1, tm_const n2) => Some _ (tm_const (plus n1 n2))
      | (tm_const n1, _) => 
          match simplify_step t2 with
          | Some t2' => Some _ (tm_plus t1 t2')
          | None => None _   
          end
      | (_, _) => 
          match simplify_step t1 with
          | Some t1' => Some _ (tm_plus t1' t2)
          | None => None _   
          end
      end
  | tm_minus t1 t2 =>
      match (t1,t2) with
      | (tm_const n1, tm_const n2) => Some _ (tm_const (minus n1 n2))
      | (tm_const n1, _) =>
          match simplify_step t2 with
          | Some t2' => Some _ (tm_minus t1 t2')
          | None => None _
          end
      | (_,_) =>
          match simplify_step t1 with
          | None => None _
          | Some t1' => Some _ (tm_minus t1' t2)
          end 
      end
  end.

Lemma check_simplify_step_1: 
    simplify_step
      (tm_const five)
  =   
      None _.
Proof. reflexivity. Qed.
Lemma check_simplify_step_2: 
    simplify_step
      (tm_plus 
        (tm_plus (tm_const zero) (tm_const three))
        (tm_plus (tm_const two) (tm_const four)))
  =   
     Some _ 
       (tm_plus 
         (tm_const three)
         (tm_plus (tm_const two) (tm_const four))).
Proof. reflexivity. Qed.
Lemma check_simplify_step_3: 
    simplify_step
      (tm_plus 
        (tm_const zero)
        (tm_plus 
          (tm_const two) 
          (tm_plus (tm_const zero) (tm_const three))))
  =   
     Some _ (tm_plus 
              (tm_const zero)
              (tm_plus 
                (tm_const two) 
                (tm_const three))).
Proof. reflexivity. Qed.

(* [tm_minus] behaves like [tm_plus]: *)
Lemma check_simplify_step_4: 
    simplify_step
      (tm_minus
        (tm_minus (tm_const three) (tm_const one))
        (tm_plus (tm_const two) (tm_const four)))
  =   
     Some _ 
       (tm_minus
         (tm_const two)
         (tm_plus (tm_const two) (tm_const four))).
Proof. reflexivity. Qed.
Lemma check_simplify_step_5: 
    simplify_step
      (tm_minus
        (tm_const zero)
        (tm_minus
          (tm_const two) 
          (tm_plus (tm_const zero) (tm_const three))))
  =   
     Some _ (tm_minus
              (tm_const zero)
              (tm_minus
                (tm_const two) 
                (tm_const three))).
Proof. reflexivity. Qed.

Lemma simplify_step_interp : forall t t',
     simplify_step t = Some _ t'
  -> interp t = interp t'.
Proof.
  (* Hint: The proof of this property is pretty long, but its
     structure very closely follows the proof of the same property in
     the [SimpleArith] module -- no new ideas are needed. *)
  intro t.  induction t.
  Case "tm_const". intros t'.  simpl.  intro eq. inversion eq.
  Case "tm_plus".  intros s eq. simpl. simpl in eq. destruct t1. 
    Case "tm_const".  destruct t2.
      Case "tm_const". inversion eq. simpl. trivial.
      Case "tm_plus".
        destruct (simplify_step (tm_plus t2_1 t2_2)).
        Case "Some".
          inversion eq.
          assert (interp (tm_plus t2_1 t2_2) = interp t).
            apply IHt2. trivial.
          rewrite H.simpl. trivial.
        Case "None".
          inversion eq.
      Case "tm_minus".
        destruct (simplify_step (tm_minus t2_1 t2_2)).
        Case "Some".
          inversion eq.
          assert (interp (tm_minus t2_1 t2_2) = interp t).
            apply IHt2. trivial.
          rewrite H. simpl. trivial.
        Case "None". inversion eq. 
    Case "tm_plus".
      destruct (simplify_step (tm_plus t1_1 t1_2)).
      Case "Some".
        inversion eq.
        assert (interp (tm_plus t1_1 t1_2) = interp t).
          apply IHt1. trivial.
        rewrite H. simpl. trivial.
      Case "None".
        inversion eq.
    Case "tm_minus".
      destruct (simplify_step (tm_minus t1_1 t1_2)).
      Case "Some".
        inversion eq.
        assert (interp (tm_minus t1_1 t1_2) = interp t).
          apply IHt1. trivial.
        rewrite H. simpl. trivial.
      Case "None". inversion eq.
  Case "tm_minus". intros s eq. simpl in eq. destruct t1.
    Case "tm_const". destruct t2.
      Case "tm_const". inversion eq. simpl. trivial.
      Case "tm_plus".
        destruct (simplify_step (tm_plus t2_1 t2_2)).
          inversion eq.
          assert (interp (tm_plus t2_1 t2_2) = interp t). apply IHt2. trivial.
          simpl. rewrite <- H. simpl. trivial.
         inversion eq.
      Case "tm_minus".
        destruct (simplify_step (tm_minus t2_1 t2_2)).
          inversion eq.
            assert (interp (tm_minus t2_1 t2_2) = interp t). apply IHt2. trivial.
            simpl. rewrite <- H. simpl. trivial.
          inversion eq.
    Case "tm_plus".
      destruct (simplify_step (tm_plus t1_1 t1_2)).
        inversion eq.
          assert (interp (tm_plus t1_1 t1_2) = interp t). apply IHt1. trivial.
          simpl. rewrite <- H. simpl. trivial.
        inversion eq.
    Case "tm_minus".
      destruct (simplify_step (tm_minus t1_1 t1_2)).
        inversion eq.
          assert (interp (tm_minus t1_1 t1_2) = interp t). apply IHt1. trivial.
          simpl. rewrite <- H. simpl. trivial.
        inversion eq.
Qed.

End SimpleArithExercise.


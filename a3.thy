theory a3
imports "AutoCorres"
begin

(*******************************************************************************)

section {* Regular Expressions (21 marks)*}

(* Definitions of regular expressions from week06B's demo. *)

datatype regexp =
  Atom char ("<_>")
 |Alt regexp regexp (infixl "\<bar>" 50)
 |Conc regexp regexp (infixl "\<cdot>"  60)
 |Star regexp ("_ \<star>" [79] 80)
 |Neg regexp ("!_" [70] 70)

inductive_set star for L
where 
  star_empty[simp,intro!]: "[] \<in> star L"
 |star_app: "\<lbrakk>u\<in>L; v\<in>star L\<rbrakk> \<Longrightarrow> u@v \<in> star L"
 
 
definition conc :: "string set \<Rightarrow> string set \<Rightarrow> string set"
  where
  "conc  l1 l2 \<equiv>{ w1@w2  |w1 w2. w1 \<in>  l1 \<and> w2 \<in>  l2}"
  
primrec 
  lang :: "regexp \<Rightarrow> string set"
where
  "lang (Atom c) = {[c]}"
 |"lang (Alt e1 e2) = lang e1 \<union> lang e2"
 |"lang (Conc e1 e2) = conc (lang e1) (lang e2)"
 |"lang (Star e) = star (lang e)"
 |"lang (Neg e) = - (lang e)"
 
 
(* Let U be the regular expression defining the
   universal language, i.e. the language of all words. 
   Let N be the regular expression defining the
   empty language, i.e. the language containing no words.
   Let E be the regular expression defining the
   language containing only the empty word. *)
   
definition
  U :: regexp
where
  "U \<equiv> Alt (Atom CHR ''x'')  (Neg (Atom CHR ''x''))"

definition
  N :: regexp
where
  "N \<equiv> Neg U"
  
definition
  E :: regexp
where
  "E \<equiv> Star N"
  
  
(* (a) Prove that the language recognised by U is indeed
        the universal set UNIV, that the language recognised
        by N is indeed the empty set, and that the language 
        recognised by E is indeed the set containing 
        only the empty word. *)
        
lemma lang_U [simp]:
  "lang U = UNIV"
  (*TODO*)
  sorry
  
lemma lang_N [simp]:
  "lang N = {}"
  (* TODO *)
  sorry   
 
lemma lang_E [simp]:
  "lang E = {[]}"
  (*TODO*)
  sorry
  
  
  
(* (b) Define a function  String (using primrec), 
      taking a list of characters in parameters, and producing 
      the regular expression recognising that string. 
      If the list is empty, the regular expression should 
      the regular expression recognising only the empty word. 
      Check (prove) the lang_String lemma. *)


primrec 
  String :: "char list \<Rightarrow> regexp"
  where 
  (*TODO*)

lemma lang_String: "lang (String xs) = {xs}"
  (*TODO*)
  
  
  
(* (c) Define a function Maybe, taking a regular 
       expression e, and producing the regular 
       expression (noted "e?") recognising 
       either e or empty word.
       Check (prove) the lang_Maybe lemma. 
       (1 mark) *)
       
  
definition 
  Maybe :: "regexp \<Rightarrow> regexp" ("_?" [79] 80)
where
  (* TODO *)
  
lemma lang_Maybe [simp]:
  "lang (e?) = {[]} \<union> lang e"
  (* TODO *)
  
  
(* (d) Define a function Plus, taking a regular 
       expression e, and producing the regular 
       expression (noted "e+") recognising 
       one or more concatenations of e.
       Check (prove) the lang_Plus lemma. *)
  
definition 
  Plus :: "regexp \<Rightarrow> regexp" ("_+" [79] 80)
where
  (*TODO*)
    
lemma lang_Plus [simp]:
  "[] \<notin> lang e \<Longrightarrow> lang (Plus e) = lang (Star e) - {[]}"
  (*TODO*)
  
  
(* (e) Define a function CClass, taking a list of characters,
       and producing the regular expression recognising 
       the words made of any of these single characters, i.e.
       "CClass [c1, c2]" recognises the two words "[c1]"
       and "[c2]".
       Check (prove) the lang_CClass lemma. *)
       
primrec 
  CClass :: "char list \<Rightarrow> regexp"
where
  (*TODO *)
  
  
lemma lang_CClass: "lang (CClass xs) = set (map (\<lambda>c. [c]) xs)"
  (* TODO *)
  
(* (f) Consider the function  Tilde below, taking a regular
       expression e,
       and producing the regular expression recognising 
       words made of any string not containing e
       followed by one e. This function is useful to
       define comments. Note that  enum enumerates all the elements
       of a finite type.      
       Check the lang_Tilde lemma. *)
       
definition 
  AnyChar :: regexp
where
  "AnyChar \<equiv> CClass Enum.enum"
  
definition 
  Tilde :: "regexp \<Rightarrow> regexp" 
where
  "Tilde e \<equiv> ! ( AnyChar \<star> \<cdot> e \<cdot> AnyChar \<star>) \<cdot> e"

lemma lang_Tilde: "{w@[c] | w. c\<notin> set w} \<subseteq> lang (Tilde <c>)"
  (*TODO*)


(*(g) Define a function  maybeempty (using primrec)
      taking a regular expression  e of type regexp
      (i.e. one of the five type of regular expressions of week06B)
      and returning True if this  e may contain 
      the empty word, False otherwise.
      Check (proof) the maybeempty_correct lemma. 
      Hint: you may look at how JFlex defines this function. *)

primrec maybeempty :: "regexp \<Rightarrow> bool"
where 
  (*TODO*)

lemma maybeempty_correct: "maybeempty e = ([] \<in> lang e) "
  (*TODO*)
      
(*(h) Prove that maybeempty of the five new types of regular expressions
      defined above (Maybe, Plus, CClass and Tilde) is equal 
      to what JFlex defines, i.e. prove maybeempty_Maybe,
      maybeempty_Plus, maybeempty_CCLass, maybeempty_String and
      maybeempty_Tilde.
      (2 points) *)

lemma maybeempty_Maybe: "maybeempty (Maybe e)= True"
  (*TODO*)
  
lemma maybeempty_Plus: "maybeempty (Plus e)= maybeempty e"
  (*TODO*)
  
lemma maybeempty_CCLass: "maybeempty (CClass xs) = False"
  (*TODO*)
  
lemma maybeempty_String: "maybeempty (String xs) = (length xs = 0)"
  (*TODO*)
  
lemma maybeempty_Tilde: "maybeempty (Tilde c) = False"
  (*TODO*)


(*******************************************************************************)

section {* Termination (15 marks)*}

(* see a3.pdf *)



(*******************************************************************************)

section "C Verification: Binary Search (64 marks)"

install_C_file "binsearch.c"

autocorres [unsigned_word_abs=binary_search] "binsearch.c"


context binsearch
begin

(* The monadic definition that autocorres produces for the C code: *)
thm binary_search'_def

(* Abbreviation for signed machine integers *)
type_synonym s_int = "32 signed word"

(* The heap only stores unsigned machine integers;
   they have the same representation as signed ones and can be converted to each other *)
type_synonym u_int = "32 word"

(* A few lemmas to help improve automation: *)

(* Pointer arithmetic on pointers to signed and unsigned words is the same *)
lemma ptr_coerce_add_signed_unsigned [simp]:
  "(ptr_coerce ((a :: s_int ptr) +\<^sub>p x) :: u_int ptr) = ptr_coerce a +\<^sub>p x"
  by (cases a) (simp add: ptr_add_def)

(* Pointer arithmetic distributivity law *)
lemma ptr_add_add [simp]:
  "p +\<^sub>p (x + y) = p +\<^sub>p x +\<^sub>p y"
  by (simp add: ptr_add_def distrib_left mult.commute)

(* C division is the same as Isabelle division for non-negative numbers: *)
lemma sdiv [simp]:
  "0 \<le> a \<Longrightarrow> a sdiv 2 = a div (2::int)"
  by (auto simp: sdiv_int_def sgn_if)

(* Some useful facts about INT_MIN and INT_MAX to improve automation: *)
lemma INT_MIN_neg [simp]:
  "INT_MIN < 0"
  by (simp add: INT_MIN_def)
lemma INT_MAX_gr [simp]: 
  "- 1 < INT_MAX" "-1 \<le> INT_MAX" "1 \<le> INT_MAX"
  by (auto simp add: INT_MAX_def)


(* This function enumerates the addresses of the entries of an signed int array: *)
fun array_addrs :: "s_int ptr \<Rightarrow> nat \<Rightarrow> s_int ptr list" where
  "array_addrs p 0 = []" |
  "array_addrs p (Suc len) = p # array_addrs (p +\<^sub>p 1) len"


(*******************************************************************************)
(* a) fill in the array_list definition *)
definition array_list :: "(u_int ptr \<Rightarrow> u_int) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> int list" where
  "array_list h p len = TODO"


(* b) fill in the valid_array definition. It might make sense to do this in two parts and look
   at the invariant and proof obligations first. *)
definition valid_array :: "(u_int ptr \<Rightarrow> bool) \<Rightarrow> (u_int ptr \<Rightarrow> u_int) \<Rightarrow> s_int ptr \<Rightarrow> int \<Rightarrow> bool" where
  "valid_array vld h p len = TODO"


(* Hints: 
    - remember to try the @{text arith} proof method for arithmetic goals on
      integers or natural numbers. 
    - use find_theorems to find Isabelle library theorems about existing concepts.
    - the lemma @{thm sorted_equals_nth_mono} might be useful
    - you are allowed to use sledgehammer and other automation
    - if you can't prove one of the lemmas below, you can still assume it in the rest of the proof
    - the function @{const int} converts an Isabelle nat to an int
    - the function @{const nat} converts an Isabelle int to a nat
*)

thm sorted_equals_nth_mono
term int
term nat

text {* Prove the following lemma: *}
lemma length_array_addrs [simp]:
  "length (array_addrs a len) = len"
  sorry

text {* Prove the following lemma: *}
lemma array_addrs_nth [simp]:
  "\<lbrakk> 0 \<le> x; nat x < len \<rbrakk> \<Longrightarrow> array_addrs a len ! nat x = a +\<^sub>p x"
  sorry

text {* Prove the following lemma: *}
lemma ptr_array:
  "\<lbrakk> 0 \<le> x; x < len \<rbrakk> \<Longrightarrow>
   uint (heap_w32 s (ptr_coerce (a :: s_int ptr) +\<^sub>p x)) = array_list (heap_w32 s) a len ! nat x"
   sorry

text {* Prove the following lemma: *}
lemma key_lt:
  "\<lbrakk> key < xs ! nat mid;  mid - 1 < x; sorted xs; 0 \<le> mid; x < int (length xs) \<rbrakk> 
  \<Longrightarrow> key < xs ! nat x"
  sorry

text {* Prove the following lemma: *}
lemma key_gt:
  "\<lbrakk> xs ! nat mid < key; 0 \<le> x; x \<le> mid; sorted xs; mid < int (length xs) \<rbrakk>
  \<Longrightarrow> xs ! nat x < key"
  sorry



lemma binary_search_correct:
  notes ptr_array [where len=len, simp]
  shows
  "\<lbrace>\<lambda>s. sorted (array_list (heap_w32 s) a len) \<and>
        valid_array (is_valid_w32 s) (heap_w32 s) a len \<and> 
        TODO \<rbrace>
   binary_search' a len key
   \<lbrace> \<lambda>r s. (r < 0 \<longrightarrow> key \<notin> set (array_list (heap_w32 s) a len)) \<and>
           (0 \<le> r \<longrightarrow> r < len \<and> (array_list (heap_w32 s) a len ! nat r) = key)\<rbrace>!"
  unfolding binary_search'_def
  apply(subst whileLoopE_add_inv[where 
               I="\<lambda>(high,low) s. valid_array (is_valid_w32 s) (heap_w32 s) a len \<and>
                                 sorted (array_list (heap_w32 s) a len) \<and>
                                 TODO1" and 
               M="\<lambda>((high,low),_). TODO2"])
  apply wp
  oops

end

end
(*>*)

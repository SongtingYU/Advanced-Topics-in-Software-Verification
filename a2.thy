theory a2
imports Main
begin


(**********************************************)
(* PART 1: "Compiling Arithmetic Expressions" *)
(**********************************************)


(* Syntax of the language *)
datatype expr = BinOp "(nat \<Rightarrow> nat \<Rightarrow> nat)" expr expr |
                UnOp "(nat \<Rightarrow> nat)" expr |
                Const nat

definition
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "plus \<equiv> (\<lambda>a b. a + b)"
  
lemma "plus = (op +)"
  by(simp add: plus_def)

(* Evaluation function *)
primrec
  eval :: "expr \<Rightarrow> nat"
where
  "eval (Const n) = n" |
  "eval (BinOp f a b) = f (eval a) (eval b)" |
  "eval (UnOp f a) = f (eval a)"

lemma "eval (BinOp (op +) (Const 2) (Const 3)) = 5"
  by simp
  
(* Programs for the stack machine *)
datatype stackp = Push nat |
                  DoUnOp "nat \<Rightarrow> nat" |
                  DoBinOp "nat \<Rightarrow> nat \<Rightarrow> nat" |
                  Seq stackp stackp ("_ ;; _")  |
                  Skip
print_theorems
type_synonym stack = "nat list"

(* Big step operational semantics to programs for the stack machine *)
inductive
  sem :: "stack \<Rightarrow> stackp \<Rightarrow> stack \<Rightarrow> bool" ("\<langle>_, _\<rangle> \<Down> _")
where
  sem_Push: "sem s (Push n) (n#s)" |
  sem_DoBinOp: "sem (a#b#s) (DoBinOp f) ((f a b)#s)" |
  sem_DoUnOp: "sem (a#s) (DoUnOp f) ((f a)#s)" |
  sem_Seq: "\<lbrakk>sem s a t; sem t b u\<rbrakk> \<Longrightarrow> sem s (Seq a b) u"

print_theorems

inductive_cases sem_PushE[elim!]: "\<langle>s, Push n\<rangle> \<Down> u"
inductive_cases sem_DoBinOpE[elim!]: "\<langle>s, DoBinOp f\<rangle> \<Down> u"
inductive_cases sem_DoUnOpE[elim!]: "\<langle>s, DoUnOp f\<rangle> \<Down> u"
inductive_cases sem_Seq[elim!]: "\<langle>s, Seq a b\<rangle> \<Down> u"
inductive_cases sem_SkipE[elim!]: "\<langle>s, Skip\<rangle> \<Down> u" 

declare sem.intros[simp, intro]

(* Simple compiler from expression to stack programs *)
primrec
  compile  :: "expr \<Rightarrow> stackp" 
where
  "compile (Const n) = Push n" |
  "compile (BinOp f a b) = Seq (compile b) (Seq (compile a) (DoBinOp f))" |
  "compile (UnOp f a) = Seq (compile a) (DoUnOp f)"

(* ---------- *)
(* Question 1 *)
(* ---------- *)

(* (a) Prove that the stack machine semantics is deterministic *)
lemma sem_det:
  "sem s e t \<Longrightarrow> sem s e u \<Longrightarrow> u = t"
  (***TODO***)
  apply (induct arbitrary:u rule: sem.induct)
   apply (erule sem.cases)
      apply simp+
    apply (erule sem.cases)
      apply simp+
    apply (erule sem.cases)
      apply blast+
    done

(* (b) Prove that the compiler is correct *)
lemma compile_correct:
  "sem s (compile e) ((eval e)#s)"
  (***TODO***)
  apply (induct e arbitrary: s)
    apply simp_all
      apply blast+
  done
  
(* (c) Prove that whether an expression can evaluate 
       depends only on the size of the initial stack *)
lemma sem_stack_content_agnostic_a:
  "sem s p t \<Longrightarrow> \<forall>s'. length s' = length s \<longrightarrow> (\<exists>t'. sem s' p t' \<and> length t = length t')"
    apply (induct rule: sem.induct)
    apply auto[1]
      apply clarsimp
      apply (case_tac s')
        apply simp
      apply (case_tac list)
        apply simp
        apply (rule_tac x="f a aa# lista" in exI)
        apply simp
        apply clarsimp
       apply (case_tac s')
        apply simp 
        apply (rule_tac x="f a # list" in exI)
        apply simp
       apply clarsimp
        apply (case_tac s')
          apply auto[1]
        apply (erule_tac x="s'" in allE)
          apply clarsimp
        apply (erule_tac x="t'" in allE)
          apply clarsimp
          apply auto
   done

lemma sem_stack_content_agnostic:
   "sem s p t \<Longrightarrow> \<forall>s'. length s' = length s \<longrightarrow> (\<exists>t'. sem s' p t')"
  (***TODO***)
    apply(drule sem_stack_content_agnostic_a)
      apply blast
    done
  
  
(* ---------- *)
(* Question 2 *)
(* ---------- *)

(* Sufficient initial stack size *)
definition
  reqd_init_stack :: "stackp \<Rightarrow> nat \<Rightarrow> bool"
where
  "reqd_init_stack p h \<equiv> (\<exists>s t. \<langle>s,p\<rangle> \<Down> t) \<longrightarrow> (\<forall>s. length s \<ge> h \<longrightarrow> (\<exists>t. \<langle>s,p\<rangle> \<Down> t))"

(* (a) Prove that compiled expressions require no initial stack *)
lemma compile_reqd_init_stack:
  "reqd_init_stack (compile e) 0"
  (***TODO***)
  apply (simp add: reqd_init_stack_def)
   apply (rule impI)
     apply (rule allI)
   apply (rule_tac x="eval e#s" in exI)
    apply (simp add: compile_correct)
  done

(* (b) Minimal initial stack length for atomic programs *)
lemma reqd_init_stack_Push:
  "reqd_init_stack (Push n) 0"
  (***TODO***)
  apply (simp add: reqd_init_stack_def)
  apply (rule impI)
    apply (erule exE)+
    apply (rule allI)
    apply blast
  done

lemma reqd_init_stack_DoUnOp:
  "reqd_init_stack (DoUnOp f) (Suc 0)"
  (***TODO***)
  apply (simp add: reqd_init_stack_def)
    apply (rule impI)
    apply (rule allI)
   apply (erule exE)
   apply (erule exE)
    apply (rule impI)
   apply (case_tac s)
     apply simp+
    apply (rule_tac x="f a#list" in exI)
     apply simp
  done

lemma reqd_init_stack_DoBinOp:
  "reqd_init_stack (DoBinOp f) (Suc (Suc 0))"
  (***TODO***)
  apply (simp add: reqd_init_stack_def)
    apply (rule impI)
      apply (rule allI)
        apply (erule exE)+
        apply (rule impI)
    apply (case_tac s)
      apply simp
     apply (case_tac list)
      apply simp+
        apply blast
  done
  
lemma reqd_init_stack_Skip:
  "reqd_init_stack Skip 0"
  (***TODO***)
  apply (simp add: reqd_init_stack_def)
    apply (rule impI)
  apply (rule allI)
  apply (erule exE)+
    apply blast
  done
  
(* (c) Minimal initial stack length for Seq *)
lemma reqd_init_stack_Seq:
  "\<lbrakk>(reqd_init_stack p1) n; (reqd_init_stack p2 m)\<rbrakk>
       \<Longrightarrow> (reqd_init_stack (Seq p1 p2) (m + n))"
  (****TODO***)
   apply (induct p1)
    apply auto
   apply (clarsimp simp: reqd_init_stack_def)
    apply auto
   apply (induct p2)
    apply auto
   apply blast+
    apply (case_tac sa)
     apply (clarsimp simp: reqd_init_stack_Push)
      apply blast
  prefer 5
   apply (clarsimp simp: reqd_init_stack_def)
  prefer 2
   apply (clarsimp simp: reqd_init_stack_def)
    apply auto
    apply (case_tac sb)
    apply blast+
 
  sorry

(* (d) Define a function that given a program p 
       calculates an appropriate stack length h
       such that reqd_init_stack p h holds *)
    
primrec
  sufficient_init_stack :: "stackp \<Rightarrow> nat"
where
  (***TODO***)
  "sufficient_init_stack (Push n) = 0"|
  "sufficient_init_stack (DoBinOp f) = (Suc 0)"|
  "sufficient_init_stack (DoUnOp f) = (Suc (Suc 0))"|
  "sufficient_init_stack (Seq p1 p2) = sufficient_init_stack p1 + sufficient_init_stack p2"|
  "sufficient_init_stack Skip = 0"
  

(* (e) Prove your function from (d) correct *)
lemma sufficient_init_stack_is_reqd_init_stack:
  "reqd_init_stack p (sufficient_init_stack p)"
  (***TODO***)
  apply (induct p)
    apply auto[1]
  prefer 5
    apply (clarsimp simp: reqd_init_stack_Skip)
      apply (clarsimp simp: reqd_init_stack_Push)
      apply (clarsimp simp: reqd_init_stack_def)
        apply (case_tac sb)
          apply auto[1]
        apply (clarsimp simp: reqd_init_stack_DoUnOp)
          apply auto
         apply (clarsimp simp: reqd_init_stack_def)
          apply (case_tac sb)
          apply auto[1]
         apply (clarsimp simp: reqd_init_stack_def)
   prefer 2
      apply (clarsimp simp: reqd_init_stack_def)
        apply auto[1]
        apply (case_tac sa)
   
  sorry
  
(* ---------- *)
(* Question 3 *)
(* ---------- *)

(*  Small-step semantics *)
inductive
  sems :: "stack \<Rightarrow> stackp \<Rightarrow> stack \<Rightarrow> stackp \<Rightarrow> bool"
where
  "sems s (Push n) (n#s) Skip" |
  "sems (a#b#s) (DoBinOp f) ((f a b)#s) Skip" |
  "sems (a#s) (DoUnOp f) ((f a)#s) Skip" |
  "sems s a s' a' \<Longrightarrow> sems s (Seq a b) s' (Seq a' b)" |
  "sems s (Seq Skip b) s b"


  
(* (a) Define a function semsn:: nat \<Rightarrow> stack \<Rightarrow> stackp \<Rightarrow> stack \<Rightarrow> stackp \<Rightarrow> bool
       that executes n steps of the small-step semantics *)

   
primrec
  semsn :: "nat \<Rightarrow> stack \<Rightarrow> stackp \<Rightarrow> stack \<Rightarrow> stackp \<Rightarrow> bool"
where
  "semsn 0 s a s' a' = sems s (Seq Skip a) s a" |
  "semsn (Suc n) s a s' a' = (\<exists>s1 a1. sems s a s1 a1 \<and> semsn n s1 a1 s' a')"

(* (b) Prove that if a program a executes in the big-step semantics to a 
       resulting stack t from an initial stack s, then it executes in the
       small-step semantics to the same resulting stack and the resulting
       program Skip. *)  
lemma semsn_correct:
  "sem s a t \<Longrightarrow> \<exists>n. semsn n s a t Skip"
  (***TODO***) 
  apply (induct)
    using sems.intros(5) semsn.simps(1) 
      apply blast
    using sems.intros(5) semsn.simps(1) 
      apply blast
    using sems.intros(5) semsn.simps(1) 
      apply blast
    using sems.intros(5) semsn.simps(1) 
      apply blast
    using sems.intros(5) semsn.simps(1) 
      apply blast
  done

(* (c) Prove that there is no universal stack bound for any compiled program *)
(* Predicate stating that stack size h is a stack bound for program p *)

definition
  stack_bound :: "stackp \<Rightarrow> nat \<Rightarrow> bool"
where
  "stack_bound p h \<equiv> \<forall>s n s' p'. semsn n s p s' p' \<longrightarrow>  length s' - length s \<le> h"

primrec
  prog_using_Suc :: "nat \<Rightarrow> expr"
where
  "prog_using_Suc 0 = Const 0" |
  "prog_using_Suc (Suc n) = (BinOp (op +) (prog_using_Suc n) (Const 0))"
  
lemma compile_has_no_universal_stack_bound:
  "\<not> (\<exists>h. (\<forall>p. stack_bound (compile p) h))"
  apply (induct) 
    apply (metis Suc_n_not_le_n diff_zero length_replicate sems.intros(5) semsn.simps(1) stack_bound_def)
    apply (metis Suc_n_not_le_n diff_zero length_replicate sems.intros(5) semsn.simps(1) stack_bound_def)
    apply (metis Suc_n_not_le_n diff_zero length_replicate sems.intros(5) semsn.simps(1) stack_bound_def)
    apply auto
    apply (metis Suc_n_not_le_n diff_zero length_replicate sems.intros(5) semsn.simps(1) stack_bound_def)
  done
 

(****************************************)
(* PART 2: "Rewriting rules for groups" *)
(****************************************)
  

(* Replace A-H below by equation stating that e is left- and right-neutral,
   and that i is left- and right-inverse, for the \<star> operator.
  
   Justify why your set of rules is confluent and terminating.
   (why it is safe to add them to the simp set)
*)

axiomatization
  e:: 'a and
  op:: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<star>" 70)  and
  i:: "'a \<Rightarrow> 'a" 
where
  neutral_left[simp]: "\<forall>a::'a. e \<star> a = a" and
  neutral_right[simp]: "\<forall>a::'a. a \<star> e = a" and
  inverse_left[simp]: "\<forall>u v::'a. (u \<star> v = e) \<and> (i v = u)" and
  inverse_right[simp]: "\<forall>u v::'a. u \<star> i u = e"
  

  lemma case_1:
   "10 \<star> a = e"
    apply auto
    done

  lemma case_2:
   "(i a)  \<star> a = e"
    apply auto
    done

   lemma case_3:
   "a \<star> (i a) = e"
    apply auto
    done

(*  
  As the lemma case 1 2 3 can be auto proof correct
  the answer could right
  neutral_left:
    all a in a' and use e \<star> a therefore is neutral a
  neutral_right:
    same with neutral_left when a \<star> e neutral_right e
  inverse_left:
    assume u v in a' u \<star> v = e and i v = u thus inverse_left v
  inverse_right:
    same with inverse_left use simp form inverse_right u
*)


end
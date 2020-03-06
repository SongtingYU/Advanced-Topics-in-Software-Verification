theory a1
imports Main
begin

section "Question 1: Lambda-Calculus"

text {* submit as part of a .txt or .pdf file *}

section "Question 2: Higher Order Unification"

text {* submit as part of a .txt or .pdf file *}

section "Question 3: Propositional Logic"

lemma prop_a:
  "B \<longrightarrow> (B \<or> A)"
  apply (rule impI)
  apply (rule disjI1)
  apply assumption
  done

lemma prop_b:
  "(A = True) = A"
  apply (rule iffI)
  apply (erule iffE)
  apply (erule impE)
  apply (erule impE)
  apply (rule TrueI)
  apply assumption
  apply (erule impE)
  apply assumption+
  apply (rule iffI)
  apply (rule TrueI)
  apply assumption
  done

lemma prop_c:
  "(A = False) = (\<not> A)"
  apply (rule iffI)
  apply (erule iffE)
  apply (rule notI)
  apply (erule impE)
  apply assumption+
  apply (rule iffI)
  apply (erule notE)
  apply assumption+
  apply (rule ccontr)
  apply assumption
  done

lemma prop_d: "P \<longrightarrow> \<not>\<not>P"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma prop_e: "\<not>\<not>P \<longrightarrow> P"
  apply (rule impI)
  apply (case_tac P)
  apply assumption
  apply (erule notE)
  apply assumption
  done

text {* 
Which of the above statements are provable only in a classical logic? 
e
*}

section "Question 4: Higher Order Logic"

lemma hol_a:
  "(\<forall>x. P x) \<or> (\<forall>x. Q x) \<longrightarrow> (\<forall>x. P x \<or> Q x)"
  apply (rule impI)
  apply (rule allI)
  apply (erule disjE)
  apply (rule disjI1)
  apply (erule spec)
  apply (rule disjI2)
  apply (erule spec)
  done

lemma hol_b:
  "(\<forall>P. P) = False"
  apply (rule iffI)
  apply (erule_tac x=False in allE)
  apply assumption
  apply (erule FalseE)
  done

lemma hol_c:
  "(\<forall>x. Q x = P x) \<and> ((\<exists>x. P x) \<longrightarrow> C) \<and> (\<exists>x. Q x) \<longrightarrow> C"
  apply (rule impI) 
  apply (erule conjE)+
  apply (erule impE)
  apply (erule exE)
  apply (erule_tac x=x in allE)
  apply (rule_tac x=x in exI)
  apply (erule iffE)
  apply (erule impE)
  apply assumption+
  done

lemma hol_d:
  "(\<forall>x. \<not> (R x) \<longrightarrow> R (M x)) \<Longrightarrow> (\<forall>x. \<not> R (M x) \<longrightarrow> R x)"
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x=x in allE)
  apply (rule classical)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

lemma hol_e:
  "\<lbrakk>(\<forall>x. \<not> (R x) \<longrightarrow> R (M x)); (\<exists>x. R x)\<rbrakk> \<Longrightarrow> (\<exists>x. R x \<and> R (M (M x)))"
  apply (erule exE)
  apply (rule classical)
  apply (rule_tac x=x in exI)
  apply (rule conjI)
  apply (erule_tac x=x in allE)
  apply assumption
  apply (erule notE)
  apply (rule classical)
  apply (erule notE)
  apply (rule classical)
  apply (rule exI)
  apply (rule conjI)
  apply  assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule_tac x="M x" in exI)
  apply (rule conjI)
  apply (erule_tac x="M x" in allE)
  apply (rule classical)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  apply (erule allE)
  apply (erule impE)
  apply assumption+
  done

text {* 
Formalise and prove the following statement using only the proof methods and rules as earlier in this question.

If every poor person has a rich mother, then there is a rich person
with a rich grandmother.
*}

lemma "\<forall>x. \<not> rich x \<longrightarrow> rich (M x) \<Longrightarrow> \<exists>x. rich x \<longrightarrow> rich (M (M x))"
  apply (erule allE)
  apply (rule classical)
  apply (erule impE)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply assumption
  apply (rule exI)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply assumption
  done

end

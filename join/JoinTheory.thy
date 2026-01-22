theory JoinTheory
  imports JoinAlg
begin

section \<open> Join Algebras \<close>

text \<open>
  See Brotherstone & Villard. "Parametric Completeness for Separation Theories".
\<close>

\<comment> \<open> no unital conditions \<close>
definition
  \<open>bounded_morphism (f :: 'a::join_alg \<Rightarrow> 'b::join_alg) \<equiv>
    (\<forall>au. is_join_unit au \<longrightarrow> is_join_unit (f au)) \<and>
    (\<forall>a b c. \<^bold>J a b c \<longrightarrow> \<^bold>J (f a) (f b) (f c)) \<and>
    (\<forall>fa fb c. \<^bold>J fa fb (f c) \<longrightarrow> (\<exists>a b. \<^bold>J a b c \<and> fa = f a \<and> fb = f b)) \<and>
    (\<forall>fa b fc. \<^bold>J fa (f b) fc \<longrightarrow> (\<exists>a c. \<^bold>J a b c \<and> fa = f a \<and> fc = f c))\<close>

definition
  \<open>bounded_morphic_image (f :: 'a::join_alg \<Rightarrow> 'b::join_alg) \<equiv>
    bounded_morphism f \<and> surj f\<close>

definition
  \<open>join_positive p \<equiv> \<lambda>a b. \<forall>x y. p x \<longrightarrow> p y \<longrightarrow> \<^bold>J a x b \<longrightarrow> \<^bold>J b y a \<longrightarrow> a = b\<close>

definition
  \<open>join_nontrivial (A::'a::join_alg set) \<equiv> A = {x::'a. \<exists>a b. \<^bold>J x a b \<or> \<^bold>J a x b \<or> \<^bold>J a b x}\<close>


lemma
  fixes f :: \<open>'a::join_alg \<Rightarrow> 'b::join_alg\<close>
  shows
  \<open>\<not> \<top> \<le> join_positive (\<top>::'a \<Rightarrow> bool) \<Longrightarrow>
    \<top> \<le> join_positive (\<top>::'b \<Rightarrow> bool) \<Longrightarrow>
    \<top> \<le> join_functional (\<top>::'a \<Rightarrow> bool) \<Longrightarrow>
    \<top> \<le> join_functional (\<top>::'b \<Rightarrow> bool) \<Longrightarrow>
    join_nontrivial (UNIV::'a set) \<Longrightarrow>
    join_nontrivial (UNIV::'b set) \<Longrightarrow>
    Ja = {(a::'a,b,c). \<^bold>J a b c} \<Longrightarrow>
    Jb = {(a::'b,b,c). \<^bold>J a b c} \<Longrightarrow>
    bounded_morphic_image f \<Longrightarrow>
    False\<close>
  unfolding join_functional_def
  apply (clarsimp simp add: le_fun_def)
  nitpick[card 'a=2, card 'b=1]
  oops

lemma
  fixes f :: \<open>'a::join_alg \<Rightarrow> 'b::join_alg\<close>
  shows
  \<open>\<top> \<le> join_positive (\<top>::'a \<Rightarrow> bool) \<Longrightarrow>
   \<not> \<top> \<le> join_positive (\<top>::'b \<Rightarrow> bool) \<Longrightarrow>
    bounded_morphic_image f \<Longrightarrow>
    False\<close>
  apply (clarsimp simp add: le_fun_def join_positive_def bounded_morphic_image_def
      bounded_morphism_def)
  apply (rename_tac bx "by" bi bj)
  apply (case_tac \<open>\<exists>ax ay ai aj. f ax = bx\<close>)
   prefer 2
   apply (metis surjD)
  apply clarsimp
  apply (case_tac \<open>\<exists>ay1 ai. f ay1 = by \<and> f ai = bi \<and> \<^bold>J ax ai ay1\<close>)
   prefer 2
   apply (metis join_comm)
  apply (case_tac \<open>\<exists>ay2 aj. f ay2 = by \<and> f aj = bj \<and> \<^bold>J ay2 aj ax\<close>)
   prefer 2
   apply metis
  apply clarsimp
  apply (subgoal_tac \<open>ay1 \<noteq> ay2\<close>)
   prefer 2
   apply blast
    \<comment> \<open> model
          a1 \<midarrow>+1\<rightarrow> b1 \<midarrow>+1\<rightarrow> a2 \<midarrow>+1\<rightarrow> b2 \<midarrow>+1\<rightarrow> a3 \<midarrow>+1\<rightarrow> ...
        is not a join algebra.
       \<close>
  oops


instance positive_cxalg :: join_alg
  apply standard
   apply (transfer, clarsimp simp add: doubleton_eq_iff)
   apply (elim disjE conjE exE; (simp; fail)?)
  apply simp


lemma
  fixes f :: \<open>'a::join_alg \<Rightarrow> 'b::join_alg\<close>
  shows
  \<open>\<top> \<le> join_functional (\<top>::'a \<Rightarrow> bool) \<Longrightarrow>
    \<not> \<top> \<le> join_functional (\<top>::'b \<Rightarrow> bool) \<Longrightarrow>
    join_nontrivial (UNIV::'a set) \<Longrightarrow>
    join_nontrivial (UNIV::'b set) \<Longrightarrow>
    Ja = {(a::'a,b,c). \<^bold>J a b c} \<Longrightarrow>
    Jb = {(a::'b,b,c). \<^bold>J a b c} \<Longrightarrow>
    bounded_morphic_image f \<Longrightarrow>
    False\<close>
  unfolding join_functional_def
  apply (clarsimp simp add: le_fun_def)
    \<comment> \<open> there should be a counterexample at 'a=7, 'b=5, but nitpick can't find it... \<close>
  nitpick[card 'a=7, card 'b=5, timeout=60]
  oops



end
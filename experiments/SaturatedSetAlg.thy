theory SaturatedSetAlg
  imports "../RGLogic"
begin

definition
  \<open>saturated_set (A::('a::pre_perm_alg) set) \<equiv>
    (\<forall>b. (\<exists>a\<in>A. \<exists>c\<in>A. a \<preceq> b \<and> b \<preceq> c) \<longrightarrow> b \<in> A) \<and>
    ((\<exists>a. a\<in>A) \<longrightarrow>
      (\<exists>m\<in>A. (\<forall>a\<in>A. a \<preceq> m) \<and>
        (\<forall>a\<in>A. \<forall>b\<in>A. a ## b \<longrightarrow> a + b \<preceq> m)))\<close>

definition
  \<open>set_plus A \<equiv>
    ((`) (case_prod (+)) \<circ> Set.filter (case_prod (##)) \<circ> (\<times>) A)\<close>

lemma set_plus_eq:
  \<open>set_plus A B = {a + b |a b. a \<in> A \<and> b \<in> B \<and> a ## b}\<close>
  unfolding set_plus_def
  by (simp add: set_eq_iff image_def Set.filter_def, blast)

lemma
  fixes A B :: \<open>('a::perm_alg) set\<close>
  shows
  \<open>L = {(a::'a,b). a \<prec> b} \<Longrightarrow>
    R = {(a::'a, b, a+b)|a b. a ## b} \<Longrightarrow>
    saturated_set A \<Longrightarrow>
    saturated_set B \<Longrightarrow>
    AB = set_plus A B \<Longrightarrow>
    saturated_set AB\<close>
  nitpick[card 'a=3]
  oops


end
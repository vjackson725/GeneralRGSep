theory Experimental
  imports "../Util"
begin

lemma refinement_atomic_condition1:
  \<open>b' \<le> b \<Longrightarrow> sp b (wlp r P) s \<le> Q \<Longrightarrow> sp b' (wlp r P) s \<le> Q\<close>
  using sp_rel_mono
  by auto


section \<open> Appel et. al.'s permission algebra \<close>

class appel_perm_alg = ord +
  fixes J :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes join_eq: \<open>J a b z1 \<Longrightarrow> J a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_assoc: \<open>J a b d \<Longrightarrow> J d c e \<Longrightarrow> \<exists>f. J b c f \<and> J a f e\<close>
  assumes join_comm: \<open>J a b c \<Longrightarrow> J b a c\<close>
  assumes join_positivity: \<open>J a c1 b \<Longrightarrow> J b c2 a \<Longrightarrow> a = b\<close>
begin

lemma ex_pseudo_unit:
  \<open>\<forall>a. \<exists>u. J a u a\<close>
  nitpick
  oops

lemma related_pseudo_units_identical_failure:
  \<open>J u1 a a \<Longrightarrow> J u2 a a \<Longrightarrow> u1 = u2\<close>
  nitpick
  oops

lemma related_units_identical_failure:
  \<open>(\<forall>a z. J u1 a z \<longrightarrow> z = a) \<Longrightarrow> (\<forall>a z. J u2 a z \<longrightarrow> z = a) \<Longrightarrow>
    J u1 a a \<Longrightarrow> J u2 a a \<Longrightarrow> u1 = u2\<close>
  by (metis join_assoc join_comm)

lemma join_add_rightL: \<open>J b c bc \<Longrightarrow> J a bc abc \<Longrightarrow> \<exists>ab. J a b ab\<close>
  using join_assoc join_comm by blast


definition
  \<open>disjoint2 a b \<equiv> Ex (J a b)\<close>

definition
  \<open>plus2 a b \<equiv> (THE c. J a b c)\<close>

lemma plus2_eq[simp]:
  \<open>J a b x \<Longrightarrow> plus2 a b = x\<close>
  by (metis plus2_def the_equality join_eq)

lemma plus2_eq2[simp]:
  \<open>J b a x \<Longrightarrow> plus2 a b = x\<close>
  using join_comm plus2_eq by blast

lemma partial_add_commute:
  \<open>disjoint2 a b \<Longrightarrow> plus2 a b = plus2 b a\<close>
  by (clarsimp simp add: disjoint2_def)

lemma join_assoc2:
  \<open>J a b ab \<Longrightarrow> J b c bc \<Longrightarrow> J ab c abc \<Longrightarrow> J a bc abc\<close>
  using join_assoc join_eq by blast

lemma partial_add_assoc:
  \<open>disjoint2 a b \<Longrightarrow> disjoint2 b c \<Longrightarrow> disjoint2 a c \<Longrightarrow>
    plus2 (plus2 a b) c = plus2 a (plus2 b c)\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (simp add: plus2_def)
  apply (meson join_assoc2 join_comm)
  done

lemma disjoint_sym: \<open>disjoint2 a b \<Longrightarrow> disjoint2 b a\<close>
  using disjoint2_def join_comm by blast

lemma disjoint_add_rightL: \<open>disjoint2 b c \<Longrightarrow> disjoint2 a (plus2 b c) \<Longrightarrow> disjoint2 a b\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (metis join_assoc join_comm)
  done

lemma disjoint_add_right_commute:
  \<open>disjoint2 b c \<Longrightarrow> disjoint2 a (plus2 b c) \<Longrightarrow> disjoint2 b (plus2 a c)\<close>
  apply (clarsimp simp add: disjoint2_def)
  apply (frule join_assoc, rule join_comm, assumption)
  apply force
  done

end

section \<open> Dockins et. al.'s multiple unit sep-algebra \<close>

text \<open>
  We removed the dup-positivity law to show it's equivalent to positivity.
\<close>
class dockins_multi_sep_alg = ord +
  fixes J :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes join_eq: \<open>J a b z1 \<Longrightarrow> J a b z2 \<Longrightarrow> z1 = z2\<close>
  assumes join_cancel: \<open>J x1 y z \<Longrightarrow> J x2 y z \<Longrightarrow> x1 = x2\<close>
  assumes join_comm: \<open>J x y z \<Longrightarrow> J y x z\<close>
  assumes join_assoc: \<open>J x y xy \<Longrightarrow> J xy z xyz \<Longrightarrow> \<exists>yz. J y z yz \<and> J x yz xyz\<close>
  assumes join_multiunits: \<open>\<exists>u. J x u x\<close>
begin

definition
  \<open>join_dup_positivity (aty :: 'a itself) \<equiv>
    \<forall>a b c::'a. J a b c \<longrightarrow> J c c c \<longrightarrow> J a a a\<close>

lemma join_assoc2:
  \<open>J b c bc \<Longrightarrow> J a bc abc \<Longrightarrow> \<exists>ab. J a b ab \<and> J ab c abc\<close>
  by (meson join_assoc join_comm)

lemma dup_add_then_eq:
  \<open>J u u u \<Longrightarrow> J a u b \<Longrightarrow> b = a\<close>
  using join_assoc2 join_cancel join_eq by blast

lemma positivity:
  assumes
    \<open>join_dup_positivity TYPE('a)\<close>
    \<open>J a a' b\<close>
    \<open>J b b' a\<close>
  shows \<open>a = b\<close>
proof -
  obtain w where l1: \<open>J a' b' w\<close> \<open>J a w a\<close>
    using assms join_assoc by blast
  moreover have l3: \<open>J w w w \<close>
    using l1 join_assoc join_cancel join_comm by blast
  ultimately show ?thesis
    using assms dup_add_then_eq join_dup_positivity_def
    by blast
qed


lemma positivity_implies_join_dup_positivity:
  assumes \<open>\<And>a b a' b'. J a a' b \<Longrightarrow> J b b' a \<Longrightarrow> a = b\<close>
  shows \<open>join_dup_positivity TYPE('a)\<close>
  unfolding join_dup_positivity_def
proof clarify
  fix a b c
  assume assms2:
    \<open>J a b c\<close>
    \<open>J c c c\<close>
  then show \<open>J a a a\<close>
    using assms join_assoc2 join_cancel
    by blast
qed


lemma join_strong_dup_positivity:
  assumes
    \<open>join_dup_positivity TYPE('a)\<close>
    \<open>J a b c\<close>
    \<open>J c c c\<close>
  shows
    \<open>a = c\<close>
proof -
  obtain ac where l1: \<open>J a c ac\<close>
    using assms join_assoc2 join_comm by blast
  moreover obtain bc where l2: \<open>J b c bc\<close>
    using assms join_assoc2 join_comm by blast
  moreover have l3: \<open>ac = c\<close>
    using assms l1 dup_add_then_eq join_comm positivity
    by blast
  moreover have l4: \<open>bc = c\<close>
    using assms l1 l2 l3
    by (metis join_cancel join_comm join_eq)
  ultimately show \<open>a = c\<close>
    using assms join_cancel by blast
qed

end

end
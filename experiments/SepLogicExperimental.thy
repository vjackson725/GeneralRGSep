theory SepLogicExperimental
  imports "../SepLogic"
begin


context perm_alg
begin

subsection \<open> core \<close>

text \<open>
  Here we introduce the notion of a (duplicable) core, the greatest duplicable element
  below an element.

  The concept was originally introduced by Pottier (2012) (TODO: cite properly),
  and is used to great effect in Iris (TODO: cite properly).

  We do not have Pottier's second rule:
    \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow> core_rel c c' \<Longrightarrow> core_rel a a' \<Longrightarrow> c' = a'\<close>
  or his law
    \<open>a ## b \<Longrightarrow> a + b = c \<Longrightarrow>
      core_rel a a' \<Longrightarrow> core_rel b b' \<Longrightarrow> core_rel c c' \<Longrightarrow>
      a' + b' = c'\<close>
  both of which are much too strong, and prevent more than one duplicable element being below a
  resource. A quick argument to this effect: if \<open>a \<prec> c\<close> and both are duplicable, then \<open>a\<close>'s core
  should be \<open>a\<close>, and \<open>c\<close>'s core should be \<open>c\<close>, with this law, they are the same. This law is
  claimed by Pottier to be equivalent to the rule \<open>dup_sub_closure\<close>, but as we can see,
  it is in fact stronger.

  Neither do we have Iris' law that \<open>has_core\<close> is monotone. This is because there can be
  several non-comparible duplicable elements sitting below a or b. When all non-empty subsets
  of duplicable elements have a lub which is itself duplicable, \<open>has_core\<close> is monotone.
\<close>

definition \<open>core_rel a ca \<equiv>
  ca \<preceq> a \<and> sepadd_dup ca \<and> (\<forall>y. y \<preceq> a \<longrightarrow> sepadd_dup y \<longrightarrow> y \<preceq> ca)\<close>

abbreviation \<open>has_core a \<equiv> Ex (core_rel a)\<close>
abbreviation \<open>the_core a \<equiv> The (core_rel a)\<close>

(* simp doesn't like rewriting core_rel under an Ex in goal position. *)
lemma has_core_def:
  \<open>has_core a \<longleftrightarrow>
    (\<exists>ca. ca \<preceq> a \<and> sepadd_dup ca \<and> (\<forall>y. y \<preceq> a \<longrightarrow> sepadd_dup y \<longrightarrow> y \<preceq> ca))\<close>
  using core_rel_def by presburger

lemma the_core_core_rel_eq[simp]:
  \<open>core_rel a ca \<Longrightarrow> the_core a = ca\<close>
  using core_rel_def resource_ordering.antisym by auto

lemma has_core_the_core_eq:
  \<open>has_core a \<Longrightarrow> P (the_core a) \<longleftrightarrow> (\<forall>ca. core_rel a ca \<longrightarrow> P ca)\<close>
  using the_core_core_rel_eq by blast

lemma dup_has_core[dest]:
  \<open>sepadd_dup a \<Longrightarrow> has_core a\<close>
  using core_rel_def resource_ordering.refl by auto

lemma core_dup_is_self[simp]:
  \<open>sepadd_dup a \<Longrightarrow> the_core a = a\<close>
  by (simp add: core_rel_def resource_ordering.refl)

lemma core_is_dup:
  \<open>has_core a \<Longrightarrow> sepadd_dup (the_core a)\<close>
  using core_rel_def the_core_core_rel_eq by blast

lemma core_is_selfsep:
  \<open>has_core a \<Longrightarrow> the_core a ## the_core a\<close>
  using core_is_dup sepadd_dup_def
  by blast

lemma core_is_selfadd:
  \<open>has_core a \<Longrightarrow> the_core a + the_core a = the_core a\<close>
  using core_is_dup sepadd_dup_def
  by blast

lemma core_idem:
  \<open>has_core a \<Longrightarrow> the_core (the_core a) = the_core a\<close>
  by (clarsimp simp add: core_rel_def)

lemma core_disjoint:
  \<open>has_core a \<Longrightarrow> the_core a ## a\<close>
  by (metis core_rel_def less_eq_sepadd_def disjoint_add_left_commute2 disjoint_sym part_of_def
      sepadd_dup_def the_core_core_rel_eq)

lemma core_plus_same[simp]:
  \<open>has_core a \<Longrightarrow> the_core a + a = a\<close>
  by (metis core_rel_def less_eq_sepadd_def part_of_def partial_add_assoc sepadd_dup_def
      the_core_core_rel_eq)

lemma core_plus_sameR[simp]:
  \<open>has_core a \<Longrightarrow> a + the_core a = a\<close>
  using core_disjoint core_plus_same partial_add_commute
  by auto

lemma the_core_le_impl:
  \<open>has_core a \<Longrightarrow> has_core b \<Longrightarrow> a \<preceq> b \<Longrightarrow> the_core a \<preceq> the_core b\<close>
  by (metis core_rel_def resource_ordering.trans the_core_core_rel_eq)

  
text \<open>
  As every duplicable element is its own core, the monotonicity criterion is equivalent to
  the property that every element above a duplicable element (e.g. 0) has a unique greatest
  duplicable element below it.
\<close>
lemma has_core_mono_iff:
  \<open>(\<forall>a b. a \<preceq> b \<longrightarrow> has_core a \<longrightarrow> has_core b) \<longleftrightarrow>
    (\<forall>x. sepadd_dup x \<longrightarrow> (\<forall>a. x \<preceq> a \<longrightarrow> has_core a))\<close>
  unfolding sepadd_dup_def has_core_def
  apply (rule iffI)
   apply (blast intro: resource_ordering.refl)
  apply (blast intro: resource_ordering.trans)
  done

lemma core_rel_additive:
  \<open>x ## y \<Longrightarrow> core_rel x x \<Longrightarrow> core_rel y y \<Longrightarrow> core_rel (x + y) (x + y)\<close>
  unfolding core_rel_def
  by (metis disjoint_middle_swap2 disjoint_sym partial_add_commute partial_add_double_assoc
      sepadd_dup_def sepadd_left_mono)

lemma core_rel_additive:
  \<open>x ## y \<Longrightarrow> core_rel x cx \<Longrightarrow> core_rel y cy \<Longrightarrow> core_rel (x + y) cxy \<Longrightarrow> cx + cy \<le> cxy\<close>
  unfolding core_rel_def
  oops

end

context perm_alg
begin

definition \<open>grunit_rel a ua \<equiv>
  ua \<preceq> a \<and> sepadd_unit ua \<and> (\<forall>y. y \<preceq> a \<longrightarrow> sepadd_unit y \<longrightarrow> y \<preceq> ua)\<close>

abbreviation \<open>has_grunit a \<equiv> Ex (grunit_rel a)\<close>
abbreviation \<open>grunit a \<equiv> The (grunit_rel a)\<close>

(* simp doesn't like rewriting grunit_rel under an Ex in goal position. *)
lemma has_grunit_def:
  \<open>has_grunit a \<longleftrightarrow> (\<exists>ca.
    ca \<preceq> a \<and> sepadd_unit ca \<and> (\<forall>y. y \<preceq> a \<longrightarrow> sepadd_unit y \<longrightarrow> y \<preceq> ca))\<close>
  using grunit_rel_def
  by presburger

lemma has_unit_mono:
  \<open>a \<preceq> b \<Longrightarrow> has_grunit a \<Longrightarrow> has_grunit b\<close>
  by (clarsimp simp add: has_grunit_def)
    (metis resource_ordering.trans step_compatible_units_identical trans_ge_ge_is_compatible)

end

context dupcl_perm_alg
begin

lemma add_to_core_then_dup:
  \<open>a ## b \<Longrightarrow> core_rel c c' \<Longrightarrow> a + b = c' \<Longrightarrow> sepadd_dup a\<close>
  using core_rel_def the_core_core_rel_eq sepadd_dup_plus_dupL by blast

lemma add_to_core_then_dupR:
  \<open>a ## b \<Longrightarrow> core_rel c c' \<Longrightarrow> a + b = c' \<Longrightarrow> sepadd_dup b\<close>
  using core_rel_def sepadd_dup_plus_dupR by blast

text \<open>
  In the presence of dup_sub_closure,
  Pottier's second core condition collapses duplicable elements.
\<close>
lemma pottier2_collapse:
  \<open>(\<And>a b c c' a'.
    a ## b \<Longrightarrow> a + b = c \<Longrightarrow> core_rel c c' \<Longrightarrow> core_rel a a' \<Longrightarrow> c' = a') \<Longrightarrow>
    a \<preceq> b \<Longrightarrow> sepadd_dup b \<Longrightarrow> a = b\<close>
  by (metis core_dup_is_self dup_has_core less_eq_sepadd_def' sepadd_dup_antimono
      the_core_core_rel_eq)

end


section \<open> Algebras with greatest lower bound / least upper bound\<close>

subsection \<open> weak glb / lub \<close>

context perm_alg
begin

definition \<open>glb_rel a b ab \<equiv> ab \<preceq> a \<and> ab \<preceq> b \<and> (\<forall>ab'. ab' \<preceq> a \<longrightarrow> ab' \<preceq> b \<longrightarrow> ab' \<preceq> ab)\<close>

abbreviation \<open>glb_exists a b \<equiv> Ex (glb_rel a b)\<close>
abbreviation \<open>glb a b \<equiv> The (glb_rel a b)\<close>

definition \<open>lub_rel a b ab \<equiv> a \<preceq> ab \<and> b \<preceq> ab \<and> (\<forall>ab'. a \<preceq> ab' \<longrightarrow> b \<preceq> ab' \<longrightarrow> ab \<preceq> ab')\<close>

abbreviation \<open>lub_exists a b \<equiv> Ex (lub_rel a b)\<close>
abbreviation \<open>lub a b \<equiv> The (lub_rel a b)\<close>

lemma glb_glb_rel_eq[simp]:
  \<open>glb_rel a b ab \<Longrightarrow> glb a b = ab\<close>
  using glb_rel_def resource_ordering.antisym by auto

lemma lub_lub_rel_eq[simp]:
  \<open>lub_rel a b ab \<Longrightarrow> lub a b = ab\<close>
  using lub_rel_def resource_ordering.antisym by auto

lemma glb_exists_glb_eq:
  \<open>glb_exists a b \<Longrightarrow> P (glb a b) \<longleftrightarrow> (\<forall>ab. glb_rel a b ab \<longrightarrow> P ab)\<close>
  using glb_glb_rel_eq by blast

lemma lub_exists_lub_eq:
  \<open>lub_exists a b \<Longrightarrow> P (lub a b) \<longleftrightarrow> (\<forall>ab. lub_rel a b ab \<longrightarrow> P ab)\<close>
  using lub_lub_rel_eq by blast

subsection \<open> Complete Glb \<close>

definition \<open>Glb_rel A x \<equiv> (\<forall>a\<in>A. x \<preceq> a) \<and> (\<forall>x'. (\<forall>a\<in>A. x' \<preceq> a) \<longrightarrow> x' \<preceq> x)\<close>

abbreviation \<open>Glb_exists A \<equiv> Ex (Glb_rel A)\<close>
abbreviation \<open>Glb A \<equiv> The (Glb_rel A)\<close>

definition \<open>Lub_rel A x \<equiv> (\<forall>a\<in>A. a \<preceq> x) \<and> (\<forall>x'. (\<forall>a\<in>A. a \<preceq> x') \<longrightarrow> x \<preceq> x')\<close>

abbreviation \<open>Lub_exists A \<equiv> Ex (Lub_rel A)\<close>
abbreviation \<open>Lub A \<equiv> The (Lub_rel A)\<close>

lemma Glb_Glb_rel_eq[simp]:
  \<open>Glb_rel A x \<Longrightarrow> Glb A = x\<close>
  using Glb_rel_def resource_ordering.antisym by auto

lemma Lub_Lub_rel_eq[simp]:
  \<open>Lub_rel A x \<Longrightarrow> Lub A = x\<close>
  using Lub_rel_def resource_ordering.antisym by auto

lemma Glb_exists_Glb_eq:
  \<open>Glb_exists A \<Longrightarrow> P (Glb A) \<longleftrightarrow> (\<forall>x. Glb_rel A x \<longrightarrow> P x)\<close>
  using Glb_Glb_rel_eq by blast

lemma Lub_exists_Lub_eq:
  \<open>Lub_exists A \<Longrightarrow> P (Lub A) \<longleftrightarrow> (\<forall>x. Lub_rel A x \<longrightarrow> P x)\<close>
  using Lub_Lub_rel_eq by blast


lemma Glb_rel_in_Least_equality:
  \<open>Glb_rel (Collect P) x \<Longrightarrow> P x \<Longrightarrow> resource_order.Least P = x\<close>
  apply (clarsimp simp add: Glb_rel_def)
  apply (subst resource_order.Least_equality; force)
  done

lemma Lub_rel_in_Greatest_equality:
  \<open>Lub_rel (Collect P) x \<Longrightarrow> P x \<Longrightarrow> resource_order.Greatest P = x\<close>
  apply (clarsimp simp add: Lub_rel_def)
  apply (subst resource_order.Greatest_equality; force)
  done

subsection \<open> lub glb interchange properties \<close>

lemma lub_glb_distrib_weak:
  assumes
    \<open>glb_exists b c\<close>
    \<open>lub_exists a (glb b c)\<close>
    \<open>lub_exists a b\<close>
    \<open>lub_exists a c\<close>
    \<open>glb_exists (lub a b) (lub a c)\<close>
  shows
    \<open>lub a (glb b c) \<preceq> glb (lub a b) (lub a c)\<close>
  using assms
  by (clarsimp simp add: lub_rel_def glb_rel_def)

lemma lub_glb_distrib_strong:
  assumes
    \<open>glb_exists b c\<close>
    \<open>lub_exists a (glb b c)\<close>
    \<open>lub_exists a b\<close>
    \<open>lub_exists a c\<close>
    \<open>glb_exists (lub a b) (lub a c)\<close>
  shows
    \<open>glb (lub a b) (lub a c) \<preceq> lub a (glb b c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_lub_distrib_weak:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>lub_exists (glb a b) (glb a c)\<close>
    \<open>lub_exists b c\<close>
    \<open>glb_exists a (lub b c)\<close>
  shows
  \<open>lub (glb a b) (glb a c) \<preceq> glb a (lub b c)\<close>
  using assms
  by (clarsimp simp add: lub_rel_def glb_rel_def)

lemma glb_lub_distrib_strong:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>lub_exists (glb a b) (glb a c)\<close>
    \<open>lub_exists b c\<close>
    \<open>glb_exists a (lub b c)\<close>
  shows
  \<open>glb a (lub b c) \<preceq> lub (glb a b) (glb a c)\<close>
  text \<open> not true! \<close>
  oops

paragraph \<open> with addition \<close>

lemma \<open>a ## b \<Longrightarrow> lub_exists a b \<Longrightarrow> lub a b \<preceq> a + b\<close>
  by (clarsimp simp add: lub_rel_def partial_le_plus partial_le_plus2)

lemma \<open>a ## b \<Longrightarrow> lub_exists a b \<Longrightarrow> lub a b \<succeq> a + b\<close>
  text \<open> not true! \<close>
  oops


lemma add_glb_distrib_weak:
  assumes
    \<open>glb_exists b c\<close>
    \<open>a ## (glb b c)\<close>
    \<open>a ## b\<close>
    \<open>a ## c\<close>
    \<open>glb_exists (a + b) (a + c)\<close>
  shows
    \<open>a + (glb b c) \<preceq> glb (a + b) (a + c)\<close>
  using assms
  by (clarsimp simp add: glb_rel_def sepadd_left_mono)

lemma add_glb_distrib_strong:
  assumes
    \<open>glb_exists b c\<close>
    \<open>a ## (glb b c)\<close>
    \<open>a ## b\<close>
    \<open>a ## c\<close>
    \<open>glb_exists (a + b) (a + c)\<close>
  shows
    \<open>glb (a + b) (a + c) \<preceq> a + (glb b c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_add_distrib_weak:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>(glb a b) ## (glb a c)\<close>
    \<open>b ## c\<close>
    \<open>glb_exists a (b + c)\<close>
  shows
    \<open>(glb a b) + (glb a c) \<preceq> glb a (b + c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

lemma glb_add_distrib_strong:
  assumes
    \<open>glb_exists a b\<close>
    \<open>glb_exists a c\<close>
    \<open>(glb a b) ## (glb a c)\<close>
    \<open>b ## c\<close>
    \<open>glb_exists a (b + c)\<close>
  shows
  \<open>glb a (b + c) \<preceq> (glb a b) + (glb a c)\<close>
  text \<open> not true \<close>
  nitpick
  oops

subsection \<open> glb properties \<close>

lemma glb_leqL[intro]: \<open>glb_exists a b \<Longrightarrow> glb a b \<preceq> a\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_leqR[intro]: \<open>glb_exists a b \<Longrightarrow> glb a b \<preceq> b\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_least[intro]: \<open>glb_exists a b \<Longrightarrow> c \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> c \<preceq> glb a b\<close>
  by (clarsimp simp add: glb_rel_def)

lemma glb_disjointL: \<open>a ## b \<Longrightarrow> glb_exists a c \<Longrightarrow> glb a c ## b\<close>
  using disjoint_preservation by blast

lemma glb_disjointR: \<open>a ## b \<Longrightarrow> glb_exists b c \<Longrightarrow> a ## glb b c\<close>
  using disjoint_preservation2 by blast

lemma glb_idem[simp]: \<open>glb a a = a\<close>
  by (simp add: glb_rel_def)

lemma sepinf_assoc[simp]:
  \<open>glb_exists b c \<Longrightarrow>
    glb_exists a b \<Longrightarrow>
    glb_exists a (glb b c) \<Longrightarrow>
    glb_exists (glb a b) c \<Longrightarrow>
    glb a (glb b c) = glb (glb a b) c\<close>
  by (clarsimp, meson glb_rel_def resource_ordering.antisym resource_ordering.trans)

end

context dupcl_perm_alg
begin

subsection \<open> weak glb + core \<close>

lemma glb_dup[dest]:
  \<open>glb_exists a b \<Longrightarrow> sepadd_dup a \<Longrightarrow> sepadd_dup (glb a b)\<close>
  using sepadd_dup_antimono
  by blast

lemma glb_dup2[dest]:
  \<open>glb_exists a b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup (glb a b)\<close>
  using sepadd_dup_antimono
  by blast

lemma glb_has_core_antimono:
  \<open>\<forall>x. sepadd_dup x \<longrightarrow> glb_exists a x \<Longrightarrow>
    a \<preceq> b \<Longrightarrow>
    has_core b \<Longrightarrow>
    has_core a\<close>
  unfolding core_rel_def
  apply clarsimp
  apply (rename_tac cb)
  apply (rule_tac x=\<open>glb a cb\<close> in exI)
  apply (simp add: glb_exists_glb_eq glb_exists_glb_eq[of _ _ \<open>\<lambda>x. x \<preceq> _\<close>] glb_rel_def)
  apply (metis sepadd_dup_antimono)
  done

lemma has_core_iff_Lub:
  \<open>has_core a \<longleftrightarrow> (\<exists>x. Lub_rel {x. sepadd_dup x \<and> x \<preceq> a} x \<and> sepadd_dup x)\<close>
  apply (rule iffI)
   apply (clarsimp simp add: Lub_rel_def has_core_def, blast)
  apply (clarsimp simp add: Lub_rel_def has_core_def, blast)
  done

lemma Lub_has_core_mono:
  \<open>(\<And>A. A \<noteq> {} \<Longrightarrow> Ball A sepadd_dup \<Longrightarrow> (\<exists>x. Lub_rel A x \<and> sepadd_dup x)) \<Longrightarrow>
    a \<preceq> b \<Longrightarrow> has_core a \<Longrightarrow> has_core b\<close>
  apply (clarsimp simp add: has_core_iff_Lub)
  apply (drule meta_spec[of _ \<open>{x. sepadd_dup x \<and> x \<preceq> b}\<close>])
  apply (fastforce simp add: Lub_rel_def)
  done

lemma has_core_mono_iff_Lub:
  \<open>(\<forall>a b. a \<preceq> b \<longrightarrow> has_core a \<longrightarrow> has_core b) \<Longrightarrow>
    \<forall>A. A \<noteq> {} \<longrightarrow>
      Ball A sepadd_dup \<longrightarrow>
      (\<forall>x y. x \<preceq> y \<longrightarrow> y \<in> A \<longrightarrow> x \<in> A) \<longrightarrow>
      (\<exists>z. \<forall>x\<in>A. x \<preceq> z) \<longrightarrow>
      (\<exists>y. Lub_rel A y \<and> sepadd_dup y)\<close>
  apply -
  apply (subst (asm) has_core_mono_iff)
  apply (clarsimp simp add: Lub_rel_def)
  oops

end

subsection \<open> Separation Algebras with glb \<close>

class inf_perm_alg = perm_alg + inf +
  assumes sepinf_leqL[intro]: \<open>compatible a b \<Longrightarrow> a \<sqinter> b \<preceq> a\<close>
    and sepinf_leqR[intro]: \<open>compatible a b \<Longrightarrow> a \<sqinter> b \<preceq> b\<close>
    and sepinf_least[intro]: \<open>compatible a b \<Longrightarrow> c \<preceq> a \<Longrightarrow> c \<preceq> b \<Longrightarrow> c \<preceq> a \<sqinter> b\<close>
begin

lemma sepinf_disjointL: \<open>a ## b \<Longrightarrow> compatible a c \<Longrightarrow> a \<sqinter> c ## b\<close>
  using disjoint_preservation by blast

lemma sepinf_disjointR: \<open>a ## b \<Longrightarrow> compatible b c \<Longrightarrow> a ## b \<sqinter> c\<close>
  using disjoint_preservation2 by blast

lemma sepinf_preserves_compatibleL:
  \<open>compatible a b \<Longrightarrow> compatible a c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_trans le_is_compatible sepinf_leqL)

lemma sepinf_preserves_compatibleL2:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_trans sepinf_preserves_compatibleL)

lemma sepinf_preserves_compatibleL3:
  \<open>compatible a c \<Longrightarrow> compatible b c \<Longrightarrow> compatible (a \<sqinter> b) c\<close>
  by (meson compatible_sym compatible_trans sepinf_preserves_compatibleL)

lemma sepinf_preserves_compatibleR:
  \<open>compatible b c \<Longrightarrow> compatible a b \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_trans ge_is_compatible sepinf_leqL)

lemma sepinf_preserves_compatibleR2:
  \<open>compatible b c \<Longrightarrow> compatible a c \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_sym sepinf_preserves_compatibleL2)

lemma sepinf_preserves_compatibleR3:
  \<open>compatible a b \<Longrightarrow> compatible a c \<Longrightarrow> compatible a (b \<sqinter> c)\<close>
  by (meson compatible_sym sepinf_preserves_compatibleL3)


lemma sepinf_idem[simp]: \<open>a \<sqinter> a = a\<close>
  by (simp add: resource_ordering.eq_iff sepinf_least sepinf_leqL)

lemma sepinf_assoc[simp]:
  \<open>compatible a b \<Longrightarrow> compatible b c \<Longrightarrow> a \<sqinter> (b \<sqinter> c) = a \<sqinter> b \<sqinter> c\<close>
  apply (subgoal_tac \<open>compatible (a \<sqinter> b) c\<close>)
   prefer 2
   apply (metis sepinf_preserves_compatibleL2)
  apply (subgoal_tac \<open>compatible a (b \<sqinter> c)\<close>)
   prefer 2
   apply (metis sepinf_preserves_compatibleR)
  apply (meson resource_ordering.antisym resource_ordering.trans sepinf_least sepinf_leqL sepinf_leqR; fail)
  done

lemma disjoint_sepinf_of_add_impl_disjoint_sepinf_part:
  \<open>a ## b \<Longrightarrow>
    compatible a c \<Longrightarrow>
    compatible (a + b) c \<Longrightarrow>
    (a + b) \<sqinter> c ## y \<Longrightarrow>
    a \<sqinter> c ## y\<close>
  by (meson disjoint_preservation resource_ordering.trans partial_le_plus sepinf_least sepinf_leqL sepinf_leqR)

lemma sepinf_of_unit_is_unit:
  \<open>compatible a b \<Longrightarrow> sepadd_unit a \<Longrightarrow> sepadd_unit (a \<sqinter> b)\<close>
  using below_unit_impl_unit by blast

lemma sepinf_of_unit_eq_that_unit[simp]:
  \<open>compatible a b \<Longrightarrow> sepadd_unit a \<Longrightarrow> a \<sqinter> b = a\<close>
  by (metis le_unit_iff_eq sepinf_leqL)

lemma sepinf_of_unit_eq_that_unit2[simp]:
  \<open>compatible a b \<Longrightarrow> sepadd_unit b \<Longrightarrow> a \<sqinter> b = b\<close>
  by (metis le_unit_iff_eq sepinf_leqR)

end


class dupcl_inf_perm_alg = inf_perm_alg + dupcl_perm_alg
begin

subsection \<open> inf + core \<close>

lemma sepinf_dup[dest]:
  \<open>compatible a b \<Longrightarrow> sepadd_dup a \<Longrightarrow> sepadd_dup (a \<sqinter> b)\<close>
  using sepadd_dup_antimono
  by blast

lemma sepinf_dup2[dest]:
  \<open>compatible a b \<Longrightarrow> sepadd_dup b \<Longrightarrow> sepadd_dup (a \<sqinter> b)\<close>
  using sepadd_dup_antimono
  by blast

end


class allcompatible_inf_perm_alg = inf_perm_alg + allcompatible_perm_alg
begin

sublocale semilattice_inf \<open>(\<sqinter>)\<close> \<open>(\<preceq>)\<close> \<open>(\<prec>)\<close>
  by standard
    (simp add: all_compatible sepinf_leqL sepinf_leqR sepinf_least)+

end

class inf_multiunit_sep_alg = multiunit_sep_alg + inf_perm_alg

class inf_sep_alg = sep_alg + inf_multiunit_sep_alg
begin

subclass allcompatible_inf_perm_alg
  by standard

end

subsubsection \<open> distributive glb/add \<close>

(* TODO: generalise this to non-compatible algebras *)
class distrib_perm_alg = allcompatible_inf_perm_alg +
  assumes inf_add_distrib1:
    \<open>\<And>x a b. a ## b \<Longrightarrow> x \<sqinter> (a + b) = (x \<sqinter> a) + (x \<sqinter> b)\<close>
begin

lemma left_inf_preserves_disjoint:
  \<open>a ## b \<Longrightarrow> (x \<sqinter> a) ## (x \<sqinter> b)\<close>
  by (meson disjoint_preservation disjoint_sym inf.cobounded2)

lemma inf_add_distrib2:
    \<open>\<And>x a b. a ## b \<Longrightarrow> (a + b) \<sqinter> x = (a \<sqinter> x) + (b \<sqinter> x)\<close>
  by (simp add: inf_add_distrib1 inf_commute)

end

(* multiunit algebras collapse to a sep alg *)

class distrib_sep_alg = sep_alg + distrib_perm_alg


section \<open> Permission algebra without disjoint-associativity \<close>

text \<open>
  Trying to allow for a true error; doesn't work because it breaks assoc.
  See Callum's paper on why this is impossible.
\<close>

class weak_perm_alg = disjoint + plus +
  (* partial commutative monoid *)
  assumes partial_add_assoc: \<open>a ## b \<Longrightarrow> b ## c \<Longrightarrow> a ## c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_assoc2:
    \<open>a ## b \<Longrightarrow> a + b ## c \<Longrightarrow> b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> (a + b) + c = a + (b + c)\<close>
  assumes partial_add_commute: \<open>a ## b \<Longrightarrow> a + b = b + a\<close>
  assumes disjoint_sym: \<open>a ## b \<Longrightarrow> b ## a\<close>
  assumes disjoint_add_right_commute: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> b ## a + c\<close>
  (* separation laws *)
  assumes positivity:
    \<open>a ## c1 \<Longrightarrow> a + c1 = b \<Longrightarrow> b ## c2 \<Longrightarrow> b + c2 = a \<Longrightarrow> a = b\<close>
begin


lemma disjoint_add_rightL: \<open>b ## c \<Longrightarrow> a ## b + c \<Longrightarrow> a ## b\<close>
  nitpick
  oops

definition sepconj :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> (infixl \<open>\<^emph>\<^sub>2\<close> 88) where
  \<open>P \<^emph>\<^sub>2 Q \<equiv> \<lambda>h. \<exists>h1 h2. h1 ## h2 \<and> h = h1 + h2 \<and> P h1 \<and> Q h2\<close>

lemma \<open>p \<^emph>\<^sub>2 (q \<^emph>\<^sub>2 r) = (p \<^emph>\<^sub>2 q) \<^emph>\<^sub>2 r\<close>
  nitpick
  oops

end


section \<open> Heap-like algebra exploration \<close>

context order
begin

definition covered_by :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<prec>\<^sub>c\<close> 50) where
  \<open>x \<prec>\<^sub>c y \<equiv> x < y \<and> (\<forall>z. x \<le> z \<longrightarrow> z < y \<longrightarrow> z = x)\<close>

end

context perm_alg
begin

text \<open> addition irreducible; cf. join/meet irreducible \<close>
definition sepadd_irr :: \<open>'a \<Rightarrow> bool\<close> where
  \<open>sepadd_irr x \<equiv>
    (\<not> sepadd_unit x) \<and>
    (\<forall>a b. a \<prec> x \<longrightarrow> b \<prec> x \<longrightarrow> a ## b \<longrightarrow> a + b \<prec> x)\<close>

definition \<open>foundation a \<equiv> {j. j \<preceq> a \<and> sepadd_irr j}\<close>

end


subsection \<open> Labelled Permission algebra \<close>

text \<open>
  This subclass is supposed to be the algebraic version of a heap.
  It introduces an order which must be compatible with, but can be more coarse than,
  the subresource relation. The equivalence classes induced by this order represent
  resources with the same set of labels.

  We want labels to form a distributive lattice, to take advantage of
  Birkhoff's representation theorem.
  TODO,sorry: The law \<open>labels_strong_distrib_law\<close> probably does this, but I need to check.
\<close>

class labelled_perm_alg = perm_alg +
  fixes labels_leq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<le>\<^sub>l\<close> 50)
    and labels_less :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open><\<^sub>l\<close> 50)
  assumes labels_leq_less_preorder:
    \<open>preordering labels_leq labels_less\<close>
  assumes labels_less_embeds: \<open>\<And>a b. a \<prec> b \<Longrightarrow> a <\<^sub>l b\<close>
  assumes labels_leq_upper_bound:
    \<open>\<And>a b c. a ## b \<Longrightarrow> a \<le>\<^sub>l c \<Longrightarrow> b \<le>\<^sub>l c \<Longrightarrow> a + b \<le>\<^sub>l c\<close>
  assumes labels_strong_distrib_law:
    \<open>\<And>a b c.
      a ## b \<Longrightarrow> a ## c \<Longrightarrow> inf_exists b c \<Longrightarrow> inf_exists (a + b) (a + c) \<Longrightarrow>
        glb (a + b) (a + c) \<le>\<^sub>l a + glb b c\<close>
begin

lemma labels_leq_embeds:
  \<open>a \<preceq> b \<Longrightarrow> a \<le>\<^sub>l b\<close>
  using labels_leq_less_preorder labels_less_embeds
  by (metis resource_order.antisym_conv2 preordering.strict_iff_not preordering_refl)

lemma labels_leq_add:
  \<open>a ## b \<Longrightarrow> a \<le>\<^sub>l (a + b)\<close>
  by (simp add: labels_leq_embeds partial_le_plus)

definition labels_eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>=\<^sub>l\<close> 50) where
  \<open>labels_eq a b \<equiv> a \<le>\<^sub>l b \<and> b \<le>\<^sub>l a\<close>

lemma labels_eq_equivp: \<open>equivp (=\<^sub>l)\<close>
  unfolding labels_eq_def
  using labels_leq_less_preorder
  by (force intro: equivpI reflpI sympI transpI dest: preordering_refl preordering_trans)

lemma disjoint_units_have_same_labels:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>sepadd_unit b\<close>
  shows
    \<open>a =\<^sub>l b\<close>
  using assms
  by (metis labels_eq_def labels_leq_add disjoint_sym sepadd_unit_def)

lemma same_labels_as_unit_is_unit:
  assumes
    \<open>a ## b\<close>
    \<open>sepadd_unit a\<close>
    \<open>a =\<^sub>l b\<close>
  shows
    \<open>sepadd_unit b\<close>
  using assms
  by (metis labels_eq_def labels_leq_less_preorder labels_less_embeds less_sepadd_def part_of_def
      sepadd_unit_def preordering.strict_iff_not)


subsubsection  \<open> Label overlap \<close>

definition \<open>label_overlap a b \<equiv> \<exists>c. c \<le>\<^sub>l a \<and> c \<le>\<^sub>l b \<and> \<not> sepadd_unit c\<close>

lemma label_overlap_refl:
  \<open>\<not> sepadd_unit a \<Longrightarrow> label_overlap a a\<close>
  using label_overlap_def labels_leq_embeds by blast

lemma label_overlap_sym:
  \<open>label_overlap a b \<Longrightarrow> label_overlap b a\<close>
  using label_overlap_def by blast

lemma same_labels_implies_label_overlap:
  \<open>a =\<^sub>l b \<Longrightarrow> \<not> sepadd_unit a \<Longrightarrow> \<not> sepadd_unit b \<Longrightarrow> label_overlap a b\<close>
  using label_overlap_def labels_eq_def labels_leq_embeds by blast

end

class halving_labelled_perm_alg = halving_perm_alg + labelled_perm_alg
begin

lemma half_subseteq_labels: \<open>half a \<le>\<^sub>l a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_embeds partial_le_plus2)

lemma half_superseteq_labels: \<open>a \<le>\<^sub>l half a\<close>
  by (metis half_additive_split half_self_disjoint labels_leq_less_preorder labels_leq_upper_bound
      preordering_refl)

lemma half_has_same_labels: \<open>half a =\<^sub>l a\<close>
  by (simp add: half_subseteq_labels half_superseteq_labels labels_eq_def)

end

(* irreducibility should allow us to define some notion of 'atomic' resources. *)

context sep_alg
begin

lemma sepadd_irr_eq:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a \<prec> x \<longrightarrow> b \<prec> x \<longrightarrow> a ## b \<longrightarrow> a + b \<prec> x)\<close>
  unfolding sepadd_irr_def
  using zero_only_unit
  by presburger

lemma sepadd_irr_eq2:
  \<open>sepadd_irr x \<longleftrightarrow> x \<noteq> 0 \<and> (\<forall>a b. a ## b \<longrightarrow> x = a + b \<longrightarrow> x = a \<or> x = b)\<close>
  unfolding sepadd_irr_eq
  by (metis less_sepadd_def' partial_le_plus2 resource_order.nless_le sepadd_left_mono)

end


section \<open> Unit exploration \<close>

(* units *)

lemma (in perm_alg) (* pseudo-units are not antimonotone *)
  \<open>x \<preceq> y \<Longrightarrow> y ## u \<Longrightarrow> y + u = y \<Longrightarrow> x + u = x\<close>
  nitpick
  oops

(* quasi-units *)
definition (in perm_alg) \<open>sepadd_qunit u \<equiv> (\<exists>x. u ## x) \<and> (\<forall>a. a ## u \<longrightarrow> a + u = u \<or> a + u = a)\<close>

lemma (in cancel_perm_alg) cancel_punit_iff_unit:
  \<open>(\<exists>x. sepadd_punit_of u x) \<longleftrightarrow> sepadd_unit u\<close>
  using cancel_right_to_unit
  unfolding sepadd_unit_def sepadd_punit_of_def
  by blast

lemma (in sep_alg)
  \<open>(u ## u \<longrightarrow> u+u = u) \<Longrightarrow> sepadd_punit_of u x \<Longrightarrow> sepadd_qunit u\<close>
  nitpick
  oops

class unit_perm_alg = perm_alg +
  (* all pseudounits are units *)
  assumes punit_collapse: \<open>\<And>u x. u ## x \<Longrightarrow> u + x = x \<Longrightarrow> sepadd_unit u\<close>
begin

lemma punit_impl_wunit:
  \<open>sepadd_punit_of u x \<Longrightarrow> sepadd_unit u\<close>
  by (meson punit_collapse sepadd_punit_of_def sepadd_unit_def)

end

context strong_sep_perm_alg
begin

sublocale strong_sep_wunit: unit_perm_alg
  by standard (metis disjoint_add_rightL selfsep_iff)

end

context cancel_perm_alg
begin

sublocale cancel_wunit: unit_perm_alg
  by standard (blast dest: cancel_right_to_unit)

end

lemma
  \<open>(\<And>u::'a::sep_alg. \<exists>x. sepadd_punit_of u x \<Longrightarrow> sepadd_unit u) \<Longrightarrow>
    (\<And>a b c::'a. a ## c \<Longrightarrow> b ## c \<Longrightarrow> (a + c = b + c) = (a = b))\<close>
  apply (simp add: sepadd_punit_of_def sepadd_unit_def)
  nitpick
  oops


end